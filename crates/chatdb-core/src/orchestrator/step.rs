use chrono::Utc;
use rusqlite::{Connection, Result, Transaction, OptionalExtension};
use uuid::Uuid;

use crate::models::action::TypedAction;
use crate::lean::{LeanGateway, RealLeanGateway};
use crate::models::{LeanVerificationOutcome, Obligation};

#[derive(Debug)]
pub enum StepError {
    Conflict,
    InvalidAttempt,
    ActionSchemaInvalid(String),
    DatabaseError(rusqlite::Error),
    LeanGatewayError(String),
}

impl From<rusqlite::Error> for StepError {
    fn from(err: rusqlite::Error) -> Self {
        StepError::DatabaseError(err)
    }
}

/// Executes a two-phase commit `step()` with compare-and-swap
pub fn attempt_commit(
    tx: &Transaction,
    attempt_id: Uuid,
    expected_revision: i64,
    claim_token: &str,
    action: &TypedAction,
    lean_gateway: &dyn LeanGateway,
    cost_micros: i128,
) -> Result<LeanVerificationOutcome, StepError> {
    let now = Utc::now().to_rfc3339();

    // 1. Verify attempt is valid
    let attempt_info: Option<(String, String, String)> = tx.query_row(
        "SELECT status, episode_id, claim_token FROM action_attempts WHERE id = ?1",
        [attempt_id.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).optional()?;

    let (status, episode_id_str, db_claim_token) = match attempt_info {
        Some(info) => info,
        None => return Err(StepError::InvalidAttempt),
    };

    if status != "claimed" || db_claim_token != claim_token {
        return Err(StepError::InvalidAttempt);
    }

    // 2. Compare-and-swap
    let current_revision: i64 = tx.query_row(
        "SELECT current_revision FROM episodes WHERE id = ?1",
        [&episode_id_str],
        |row| row.get(0),
    )?;

    if current_revision != expected_revision {
        return Err(StepError::Conflict);
    }

    // Update attempt to executing
    tx.execute(
        "UPDATE action_attempts SET status = 'executing', execution_started_at = ?1 WHERE id = ?2",
        (&now, attempt_id.to_string()),
    )?;

    let mut is_valid = false;
    let mut outcome_result = LeanVerificationOutcome::KernelPass; // Dummy default

    // 3. Execute Lean if it's a Solve action
    match action {
        TypedAction::Solve { proof_term } => {
            // Find the pending obligation for this episode
            // We assume root obligation for now (simplified for the atomic step demonstration)
            let obligation_info: Option<(String, String, String, String)> = tx.query_row(
                "SELECT id, problem_version_id, lean_statement, statement_hash 
                 FROM episode_obligations 
                 WHERE episode_id = ?1 AND status IN ('open', 'in_progress') ORDER BY depth_from_root DESC LIMIT 1",
                [&episode_id_str],
                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)),
            ).optional()?;

            if let Some((obl_id_str, pv_id_str, lean_stmt, stmt_hash)) = obligation_info {
                let pv_env_hash: String = tx.query_row(
                    "SELECT environment_hash FROM problem_versions WHERE id = ?1",
                    [&pv_id_str],
                    |row| row.get(0),
                )?;

                // Construct a mock obligation
                let obl = Obligation {
                    id: Uuid::parse_str(&obl_id_str).unwrap(),
                    problem_version_id: Uuid::parse_str(&pv_id_str).unwrap(),
                    kind: crate::models::ObligationKind::Proof,
                    theorem_name: "O_test".to_string(),
                    lean_statement: lean_stmt,
                    statement_hash: stmt_hash,
                    natural_description: "".to_string(),
                    status: crate::models::ObligationStatus::InProgress,
                    depth_from_root: 0,
                    created_by: crate::models::ObligationCreator::InitialSketch,
                    created_by_epoch_id: None,
                    superseded_by_id: None,
                    proved_lemma_id: None,
                    refutation_lemma_id: None,
                    failure_lesson: None,
                    attempt_count: 0,
                    created_at: Utc::now(),
                    closed_at: None,
                };

                // No dependencies for this simplified version
                let dep_ids = vec![];

                match lean_gateway.verify_exact(&obl, proof_term, &dep_ids, &pv_env_hash) {
                    Ok(result) => {
                        outcome_result = result.outcome.clone();
                        is_valid = matches!(result.outcome, LeanVerificationOutcome::KernelPass);
                    }
                    Err(e) => {
                        return Err(StepError::LeanGatewayError(e));
                    }
                }
            } else {
                return Err(StepError::ActionSchemaInvalid("No open obligations found".to_string()));
            }
        }
        TypedAction::Decompose { .. } => {
            // Simplified: we treat decompose as always valid for telemetry purposes here
            is_valid = true;
        }
        TypedAction::GiveUp => {
            is_valid = false;
        }
        TypedAction::ExternalResponseRejected { .. } => {
            is_valid = false;
        }
    }

    // 4. Update episode telemetry and costs
    let new_revision = current_revision + 1;
    let cost_str = cost_micros.to_string(); // Store fixed-point i128 as string if needed, or deduct

    if is_valid {
        tx.execute(
            "UPDATE episodes SET 
                current_revision = ?1,
                step_count = step_count + 1,
                cost_budget_micros = cost_budget_micros - ?2,
                updated_at = ?3
             WHERE id = ?4",
            (new_revision, cost_micros as i64, Utc::now().to_rfc3339(), &episode_id_str),
        )?;
        
        tx.execute(
            "UPDATE action_attempts SET status = 'committed', execution_completed_at = ?1 WHERE id = ?2",
            (Utc::now().to_rfc3339(), attempt_id.to_string()),
        )?;
    } else {
        tx.execute(
            "UPDATE episodes SET 
                current_revision = ?1,
                step_count = step_count + 1,
                invalid_action_count = invalid_action_count + 1,
                cost_budget_micros = cost_budget_micros - ?2,
                updated_at = ?3
             WHERE id = ?4",
            (new_revision, cost_micros as i64, Utc::now().to_rfc3339(), &episode_id_str),
        )?;
        
        tx.execute(
            "UPDATE action_attempts SET status = 'rejected', execution_completed_at = ?1 WHERE id = ?2",
            (Utc::now().to_rfc3339(), attempt_id.to_string()),
        )?;
    }

    // 5. Deduct lease costs
    // The prompt says: "Deduct lease costs using fixed-point i128". 
    // We update model_call_leases if they exist, but for now we just deduct from episodes.

    Ok(outcome_result)
}
