use chrono::Utc;
use rusqlite::{Result, Transaction, OptionalExtension};
use uuid::Uuid;

use crate::models::action::TypedAction;
use crate::lean::LeanGateway;
use crate::models::{LeanVerificationOutcome, Obligation, Polarity};

#[derive(Debug)]
pub enum StepError {
    Conflict,
    InvalidAttempt,
    ActionSchemaInvalid(String),
    DatabaseError(rusqlite::Error),
    LeanGatewayError(String),
    Internal(String),
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
    let attempt_info: Option<(String, String, String, String)> = tx.query_row(
        "SELECT status, episode_id, claim_token, action_request_id FROM action_attempts WHERE id = ?1",
        [attempt_id.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)),
    ).optional()?;

    let (status, episode_id_str, db_claim_token, action_request_id_str) = match attempt_info {
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

    // The obligation this attempt was claimed against — set by advance() when it
    // built the observation. Using this instead of re-guessing keeps the commit
    // targeted at exactly what the client was shown, even when several obligations
    // are open at once (e.g. siblings created by a prior Decompose).
    let target_obligation_id: Option<String> = tx.query_row(
        "SELECT target_obligation_id FROM action_requests WHERE id = ?1",
        [&action_request_id_str],
        |row| row.get(0),
    )?;

    // Update attempt to executing
    tx.execute(
        "UPDATE action_attempts SET status = 'executing', execution_started_at = ?1 WHERE id = ?2",
        (&now, attempt_id.to_string()),
    )?;

    let is_valid: bool;
    let mut outcome_result = LeanVerificationOutcome::KernelFail; // Dummy default

    // 3. Execute the action
    match action {
        TypedAction::Solve { proof_term } => {
            let obl_id_str = target_obligation_id
                .ok_or_else(|| StepError::ActionSchemaInvalid("No target obligation for this request".to_string()))?;

            let (pv_id_str, lean_stmt, stmt_hash, depth): (String, String, String, i64) = tx.query_row(
                "SELECT problem_version_id, lean_statement, statement_hash, depth_from_root
                 FROM episode_obligations WHERE id = ?1 AND episode_id = ?2",
                [&obl_id_str, &episode_id_str],
                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)),
            )?;

            let (pv_env_hash, import_manifest_json): (String, String) = tx.query_row(
                "SELECT environment_hash, import_manifest_json FROM problem_versions WHERE id = ?1",
                [&pv_id_str],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )?;
            let import_manifest: Vec<String> = serde_json::from_str(&import_manifest_json).unwrap_or_default();

            // Only direct dependencies that are already proved may be imported.
            let mut dep_stmt = tx.prepare(
                "SELECT dependency_obligation_id FROM episode_obligation_edges e
                 JOIN episode_obligations dep ON dep.id = e.dependency_obligation_id
                 WHERE e.parent_obligation_id = ?1 AND dep.status = 'proved'",
            )?;
            let dep_ids: Vec<Uuid> = dep_stmt
                .query_map([&obl_id_str], |row| row.get::<_, String>(0))?
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .map(|s| Uuid::parse_str(&s).unwrap())
                .collect();

            let obl = Obligation {
                id: Uuid::parse_str(&obl_id_str).unwrap(),
                problem_version_id: Uuid::parse_str(&pv_id_str).unwrap(),
                kind: crate::models::ObligationKind::Proof,
                theorem_name: format!("O_{}", obl_id_str.replace('-', "").get(..16).unwrap_or(&obl_id_str)),
                lean_statement: lean_stmt,
                statement_hash: stmt_hash,
                natural_description: "".to_string(),
                status: crate::models::ObligationStatus::InProgress,
                depth_from_root: depth,
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

            match lean_gateway.verify_exact(&obl, proof_term, &dep_ids, &pv_env_hash, &import_manifest) {
                Ok(result) => {
                    outcome_result = result.outcome.clone();
                    is_valid = matches!(result.outcome, LeanVerificationOutcome::KernelPass);

                    tx.execute(
                        "UPDATE episode_obligations SET attempt_count = attempt_count + 1 WHERE id = ?1",
                        [&obl_id_str],
                    )?;

                    if is_valid {
                        let lemma_id = Uuid::new_v4();
                        tx.execute(
                            "INSERT INTO episode_verified_lemmas (
                                id, episode_id, obligation_id, polarity, theorem_name, statement_hash,
                                proof_source_artifact_hash, compiled_artifact_hash, proof_term_hash,
                                environment_hash, actual_dependency_ids_json, kernel_result_hash, verified_at
                            ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13)",
                            (
                                lemma_id.to_string(),
                                &episode_id_str,
                                &obl_id_str,
                                Polarity::Positive.to_string(),
                                &result.theorem_name,
                                &result.expected_statement_hash,
                                &result.proof_source_hash,
                                result.compiled_artifact_hash.as_deref().unwrap_or(""),
                                result.proof_term_hash.as_deref().unwrap_or(""),
                                &pv_env_hash,
                                "[]",
                                "",
                                Utc::now().to_rfc3339(),
                            ),
                        )?;
                        tx.execute(
                            "UPDATE episode_obligations SET status = 'proved', proved_lemma_id = ?1, closed_at = ?2 WHERE id = ?3",
                            (lemma_id.to_string(), Utc::now().to_rfc3339(), &obl_id_str),
                        )?;
                    } else {
                        let lesson = result.diagnostic.as_ref().map(|d| d.primary_message.clone());
                        tx.execute(
                            "UPDATE episode_obligations SET status = 'open', failure_lesson = COALESCE(?1, failure_lesson) WHERE id = ?2",
                            (lesson, &obl_id_str),
                        )?;
                    }
                }
                Err(e) => {
                    return Err(StepError::LeanGatewayError(e));
                }
            }
        }
        TypedAction::Decompose { sub_lemmas } => {
            let obl_id_str = target_obligation_id
                .ok_or_else(|| StepError::ActionSchemaInvalid("No target obligation for this request".to_string()))?;

            let (pv_id_str, depth): (String, i64) = tx.query_row(
                "SELECT problem_version_id, depth_from_root FROM episode_obligations WHERE id = ?1 AND episode_id = ?2",
                [&obl_id_str, &episode_id_str],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )?;

            let cleaned: Vec<&str> = sub_lemmas.iter().map(|s| s.trim()).filter(|s| !s.is_empty()).collect();
            if cleaned.is_empty() {
                return Err(StepError::ActionSchemaInvalid("decompose requires at least one non-empty sub_lemma".to_string()));
            }

            for sub in &cleaned {
                let child_id = Uuid::new_v4();
                // MUST match RealLeanGateway's derived name (`O_` + first 16 hex of the
                // obligation id): the gateway compiles the child under that name and the
                // observation advertises this theorem_name as a dependency signature —
                // if they diverge, no root proof can ever reference a proved child.
                let theorem_name = format!("O_{}", &child_id.simple().to_string()[..16]);
                let statement_hash = crate::hashing::canonical_hash(sub)
                    .map_err(StepError::Internal)?;

                tx.execute(
                    "INSERT INTO episode_obligations (
                        id, episode_id, problem_version_id, kind, theorem_name,
                        lean_statement, statement_hash, natural_description, status,
                        depth_from_root, created_by, created_at
                    ) VALUES (?1, ?2, ?3, 'proof', ?4, ?5, ?6, ?7, 'open', ?8, 'decomposition', ?9)",
                    (
                        child_id.to_string(),
                        &episode_id_str,
                        &pv_id_str,
                        &theorem_name,
                        sub,
                        &statement_hash,
                        sub,
                        depth + 1,
                        &now,
                    ),
                )?;

                tx.execute(
                    "INSERT INTO episode_obligation_edges (
                        parent_obligation_id, dependency_obligation_id, edge_kind, created_at
                    ) VALUES (?1, ?2, 'lemma', ?3)",
                    (&obl_id_str, child_id.to_string(), &now),
                )?;
            }

            tx.execute(
                "UPDATE episode_obligations SET status = 'in_progress' WHERE id = ?1 AND status = 'open'",
                [&obl_id_str],
            )?;

            is_valid = true;
        }
        TypedAction::GiveUp => {
            // A deliberate give-up is a valid, terminal action — not an invalid
            // submission. The caller (MCP layer) is responsible for ending the
            // episode with outcome='gave_up' when it sees this committed.
            is_valid = true;
        }
        TypedAction::ExternalResponseRejected { .. } => {
            is_valid = false;
        }
    }

    // Only Solve produces a genuine Lean outcome (set above, pass or fail). For every
    // other action, the caller reads `outcome_result` purely as an accepted/rejected
    // signal — reflect `is_valid` here so Decompose/GiveUp don't fall through to the
    // KernelFail default and get misreported as rejected.
    if !matches!(action, TypedAction::Solve { .. }) {
        outcome_result = if is_valid { LeanVerificationOutcome::KernelPass } else { LeanVerificationOutcome::KernelFail };
    }

    // 4. Update episode telemetry and costs
    let new_revision = current_revision + 1;
    let _cost_str = cost_micros.to_string();

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

    // Mark the fulfilling request so episode_observe/advance never surface it again.
    tx.execute(
        "UPDATE action_requests SET status = 'fulfilled', fulfilled_at = ?1, fulfilled_attempt_id = ?2 WHERE id = ?3",
        (Utc::now().to_rfc3339(), attempt_id.to_string(), &action_request_id_str),
    )?;

    Ok(outcome_result)
}
