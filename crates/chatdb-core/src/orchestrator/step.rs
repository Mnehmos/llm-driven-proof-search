use chrono::Utc;
use rusqlite::{Result, Transaction, OptionalExtension};
use uuid::Uuid;

use crate::models::action::TypedAction;
use crate::lean::LeanGateway;
use crate::lean::module::AssembledModule;
use crate::models::{LeanVerificationOutcome, LeanVerificationResult, LeanModuleVerificationResult, Obligation, Polarity};

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

/// Inputs for a Lean gateway call that must run OUTSIDE the DB lock (review
/// feedback on #16/#17: "do not hold the DB mutex while running Lean"). Built by
/// `attempt_prepare` from data read within its own short transaction; the caller
/// invokes the actual gateway method with the lock released, then passes the
/// response to `attempt_finalize`.
pub enum GatewayRequest {
    Solve {
        obl: Obligation,
        proof_term: String,
        dep_ids: Vec<Uuid>,
        env_hash: String,
        import_manifest: Vec<String>,
    },
    SubmitModule {
        assembled: AssembledModule,
        env_hash: String,
    },
}

/// The gateway's response to a [`GatewayRequest`], carried back into
/// `attempt_finalize`. `Err(String)` on either variant means the invocation
/// itself failed (spawn error, timeout) — an infrastructure failure, not a
/// normal kernel_fail outcome — exactly as `verify_exact`/`verify_module` define it.
pub enum GatewayResponse {
    Solve(std::result::Result<LeanVerificationResult, String>),
    SubmitModule(std::result::Result<LeanModuleVerificationResult, String>),
}

/// Data `attempt_finalize` needs to write results for the obligation this
/// attempt targeted, carried across the gap between `attempt_prepare` and
/// `attempt_finalize` (the gateway call happens in between, outside any tx).
pub enum FinalizeContext {
    Solve {
        obl_id_str: String,
        pv_env_hash: String,
    },
    SubmitModule {
        obl_id_str: String,
        stmt_hash: String,
        pv_env_hash: String,
        namespace: String,
        module_items_json: String,
        pv_id_str: String,
        pv_manifest_hash: String,
    },
}

/// What `attempt_prepare` learned about this attempt. `Done` means the action
/// needed no Lean invocation and every write (including the episode/attempt
/// bookkeeping tail) is already committed inside the same transaction the caller
/// passed in — nothing further to finalize. `NeedsGateway` means only
/// housekeeping (mark-executing, attempt_count) was written; the caller must
/// commit that transaction, run the gateway call WITHOUT holding the DB lock,
/// then call `attempt_finalize` in a fresh transaction with `request`'s result
/// and `ctx`.
pub enum PrepOutcome {
    Done { outcome: LeanVerificationOutcome, is_valid: bool },
    NeedsGateway { request: GatewayRequest, ctx: FinalizeContext },
}

/// Validates the attempt/claim/CAS, marks the attempt 'executing', and either:
/// - fully executes and commits a non-Lean action (Decompose / GiveUp /
///   ExternalResponseRejected) or a policy-rejected SubmitModule, returning
///   `Ok(PrepOutcome::Done { .. })` — the caller's transaction already has
///   everything (including the episode/attempt bookkeeping tail) and needs no
///   further step.rs call; or
/// - for Solve / a policy-passing SubmitModule, fetches everything needed to
///   call the Lean gateway and returns `Ok(PrepOutcome::NeedsGateway { .. })`
///   WITHOUT calling the gateway or writing the bookkeeping tail — the caller
///   must commit this transaction, run the gateway call with the DB lock
///   released, then call `attempt_finalize` in a new transaction.
///
/// Does not call the Lean gateway under any circumstances — that is the whole
/// point of the split.
pub fn attempt_prepare(
    tx: &Transaction,
    attempt_id: Uuid,
    expected_revision: i64,
    claim_token: &str,
    action: &TypedAction,
    cost_micros: i128,
) -> Result<PrepOutcome, StepError> {
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

            tx.execute(
                "UPDATE episode_obligations SET attempt_count = attempt_count + 1 WHERE id = ?1",
                [&obl_id_str],
            )?;

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

            Ok(PrepOutcome::NeedsGateway {
                request: GatewayRequest::Solve {
                    obl, proof_term: proof_term.clone(), dep_ids,
                    env_hash: pv_env_hash.clone(), import_manifest,
                },
                ctx: FinalizeContext::Solve { obl_id_str, pv_env_hash },
            })
        }
        TypedAction::SubmitModule { module_items, root_theorem } => {
            // A module proves its TARGET obligation as a whole. The root theorem's
            // statement must hash-match that obligation's statement (for the root
            // obligation, that is the problem's registered root formal statement).
            // Either the entire assembled module passes the kernel and the
            // obligation is closed, or nothing enters the trusted namespace.
            let obl_id_str = target_obligation_id
                .ok_or_else(|| StepError::ActionSchemaInvalid("No target obligation for this request".to_string()))?;

            let (pv_id_str, _lean_stmt, stmt_hash): (String, String, String) = tx.query_row(
                "SELECT problem_version_id, lean_statement, statement_hash
                 FROM episode_obligations WHERE id = ?1 AND episode_id = ?2",
                [&obl_id_str, &episode_id_str],
                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
            )?;

            let (pv_env_hash, import_manifest_json, pv_manifest_hash): (String, String, String) = tx.query_row(
                "SELECT environment_hash, import_manifest_json, import_manifest_hash FROM problem_versions WHERE id = ?1",
                [&pv_id_str],
                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
            )?;
            let import_manifest: Vec<String> = serde_json::from_str(&import_manifest_json).unwrap_or_default();

            // Same namespace derivation RealLeanGateway.verify_exact uses for the
            // single-theorem path, so both live under one problem namespace.
            let ns16 = pv_id_str.replace('-', "");
            let problem_namespace = format!("ChatDB.P_{}", &ns16[..16.min(ns16.len())]);

            tx.execute(
                "UPDATE episode_obligations SET attempt_count = attempt_count + 1 WHERE id = ?1",
                [&obl_id_str],
            )?;

            match crate::lean::module::assemble_module(&problem_namespace, &stmt_hash, module_items, root_theorem, &import_manifest) {
                Err(policy_err) => {
                    // Deterministic policy rejection (bad name, prohibited construct,
                    // root hash mismatch, ...). A normal rejected attempt — never a
                    // hard StepError, and no Lean invocation needed — so this is fully
                    // resolved right here, in this transaction.
                    let lesson = format!("module rejected by policy: {}", policy_err);
                    tx.execute(
                        "UPDATE episode_obligations SET status = 'open', failure_lesson = ?1 WHERE id = ?2",
                        (lesson, &obl_id_str),
                    )?;
                    finalize_bookkeeping(tx, attempt_id, &episode_id_str, &action_request_id_str, current_revision, cost_micros, false)?;
                    Ok(PrepOutcome::Done { outcome: LeanVerificationOutcome::KernelFail, is_valid: false })
                }
                Ok(assembled) => {
                    let module_items_json = serde_json::json!({
                        "module_items": module_items,
                        "root_theorem": root_theorem,
                    }).to_string();
                    let namespace = assembled.namespace.clone();
                    Ok(PrepOutcome::NeedsGateway {
                        request: GatewayRequest::SubmitModule { assembled, env_hash: pv_env_hash.clone() },
                        ctx: FinalizeContext::SubmitModule {
                            obl_id_str, stmt_hash, pv_env_hash, namespace,
                            module_items_json, pv_id_str, pv_manifest_hash,
                        },
                    })
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

            finalize_bookkeeping(tx, attempt_id, &episode_id_str, &action_request_id_str, current_revision, cost_micros, true)?;
            Ok(PrepOutcome::Done { outcome: LeanVerificationOutcome::KernelPass, is_valid: true })
        }
        TypedAction::GiveUp => {
            // A deliberate give-up is a valid, terminal action — not an invalid
            // submission. The caller (MCP layer) is responsible for ending the
            // episode with outcome='gave_up' when it sees this committed.
            finalize_bookkeeping(tx, attempt_id, &episode_id_str, &action_request_id_str, current_revision, cost_micros, true)?;
            Ok(PrepOutcome::Done { outcome: LeanVerificationOutcome::KernelPass, is_valid: true })
        }
        TypedAction::ExternalResponseRejected { .. } => {
            finalize_bookkeeping(tx, attempt_id, &episode_id_str, &action_request_id_str, current_revision, cost_micros, false)?;
            Ok(PrepOutcome::Done { outcome: LeanVerificationOutcome::KernelFail, is_valid: false })
        }
    }
}

/// Writes the Lean gateway's response for a deferred [`GatewayRequest`] (obtained
/// with the DB lock released) and completes the attempt: the verified
/// lemma/module row, the obligation status, and the episode/attempt/request
/// bookkeeping tail — mirroring exactly what `attempt_prepare`'s `Done` branches
/// write inline. Re-validates the attempt is still `executing` with the same
/// `claim_token` first: the gap between prepare and finalize is a real window
/// where a concurrent expiry sweep could have reclaimed a wedged attempt, and
/// writing results for an attempt that is no longer the live one would corrupt
/// state instead of just losing a report.
pub fn attempt_finalize(
    tx: &Transaction,
    attempt_id: Uuid,
    claim_token: &str,
    cost_micros: i128,
    ctx: FinalizeContext,
    response: GatewayResponse,
) -> Result<LeanVerificationOutcome, StepError> {
    let (status, episode_id_str, db_claim_token, action_request_id_str, current_revision): (String, String, String, String, i64) = {
        let (status, episode_id_str, db_claim_token, action_request_id_str): (String, String, String, String) = tx.query_row(
            "SELECT status, episode_id, claim_token, action_request_id FROM action_attempts WHERE id = ?1",
            [attempt_id.to_string()],
            |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)),
        ).optional()?.ok_or(StepError::InvalidAttempt)?;
        let current_revision: i64 = tx.query_row(
            "SELECT current_revision FROM episodes WHERE id = ?1",
            [&episode_id_str],
            |row| row.get(0),
        )?;
        (status, episode_id_str, db_claim_token, action_request_id_str, current_revision)
    };

    if status != "executing" || db_claim_token != claim_token {
        // The attempt was reclaimed (expiry sweep) or otherwise moved on while the
        // gateway call was in flight. Nothing safe to write — the caller surfaces
        // this exactly like any other InvalidAttempt (client re-claims and retries).
        return Err(StepError::InvalidAttempt);
    }

    let (outcome_result, is_valid) = match (ctx, response) {
        (FinalizeContext::Solve { obl_id_str, pv_env_hash }, GatewayResponse::Solve(gw_result)) => {
            match gw_result {
                Ok(result) => {
                    let is_valid = matches!(result.outcome, LeanVerificationOutcome::KernelPass);
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
                    (result.outcome, is_valid)
                }
                Err(e) => return Err(StepError::LeanGatewayError(e)),
            }
        }
        (FinalizeContext::SubmitModule { obl_id_str, stmt_hash, pv_env_hash, namespace, module_items_json, pv_id_str, pv_manifest_hash }, GatewayResponse::SubmitModule(gw_result)) => {
            match gw_result {
                Ok(result) => {
                    let is_valid = matches!(result.outcome, LeanVerificationOutcome::KernelPass);
                    if is_valid {
                        let lemma_id = Uuid::new_v4();
                        let root_theorem_name = format!("{}.{}", namespace, result.root_lean_name);
                        // Reuse episode_verified_lemmas to close the root obligation
                        // (so the existing kernel_verified/certified promotion fires).
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
                                &root_theorem_name,
                                &stmt_hash,
                                &result.module_source_hash,
                                &result.declaration_manifest_hash,
                                "",
                                &pv_env_hash,
                                "[]",
                                &result.kernel_result_hash,
                                Utc::now().to_rfc3339(),
                            ),
                        )?;
                        tx.execute(
                            "UPDATE episode_obligations SET status = 'proved', proved_lemma_id = ?1, closed_at = ?2 WHERE id = ?3",
                            (lemma_id.to_string(), Utc::now().to_rfc3339(), &obl_id_str),
                        )?;

                        // Persist the verified module as a structured, replayable
                        // artifact (issue #4). module_items_json holds the exact items
                        // + root theorem, so the precise Lean source re-assembles
                        // deterministically on export and replay. Shares this
                        // transaction, so it is atomic with closing the root obligation.
                        let module_row_id = Uuid::new_v4();
                        let now_ts = Utc::now().to_rfc3339();
                        tx.execute(
                            "INSERT INTO episode_verified_modules (
                                id, episode_id, problem_version_id, root_obligation_id,
                                root_statement_hash, import_manifest_hash, environment_hash,
                                module_source_hash, module_items_json, declaration_manifest_hash,
                                kernel_result_hash, verified_at
                            ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
                            (
                                module_row_id.to_string(),
                                &episode_id_str,
                                &pv_id_str,
                                &obl_id_str,
                                &stmt_hash,
                                &pv_manifest_hash,
                                &pv_env_hash,
                                &result.module_source_hash,
                                &module_items_json,
                                &result.declaration_manifest_hash,
                                &result.kernel_result_hash,
                                &now_ts,
                            ),
                        )?;
                        // Item manifest is re-derivable from module_items_json via
                        // assemble_module (import_manifest doesn't affect per-item
                        // hashes, only the rendered `source`, so an empty manifest here
                        // is sufficient and avoids another DB round trip).
                        if let Ok(stored) = serde_json::from_str::<serde_json::Value>(&module_items_json) {
                            let parsed_items = stored.get("module_items")
                                .and_then(|v| serde_json::from_value::<Vec<crate::models::action::LeanModuleItem>>(v.clone()).ok());
                            let parsed_root = stored.get("root_theorem")
                                .and_then(|v| serde_json::from_value::<crate::models::action::ModuleTheorem>(v.clone()).ok());
                            if let (Some(items), Some(root)) = (parsed_items, parsed_root) {
                                if let Ok(reassembled) = crate::lean::module::assemble_module(&namespace, &stmt_hash, &items, &root, &Vec::<String>::new()) {
                                    for item in &reassembled.item_manifest {
                                        let item_id = Uuid::new_v4();
                                        let depends_on_json = serde_json::to_string(&item.depends_on).unwrap_or_else(|_| "[]".to_string());
                                        tx.execute(
                                            "INSERT INTO episode_verified_module_items (
                                                id, module_id, item_order, item_kind, lean_name,
                                                statement_or_type_hash, body_hash, depends_on_json, policy_result_json
                                            ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)",
                                            (
                                                item_id.to_string(),
                                                module_row_id.to_string(),
                                                item.order as i64,
                                                &item.kind,
                                                &item.lean_name,
                                                &item.statement_or_type_hash,
                                                &item.body_hash,
                                                &depends_on_json,
                                                "{\"policy\":\"passed\"}",
                                            ),
                                        )?;
                                    }
                                }
                            }
                        }
                    } else {
                        let lesson = result.diagnostic.as_ref().map(|d| d.primary_message.clone());
                        tx.execute(
                            "UPDATE episode_obligations SET status = 'open', failure_lesson = COALESCE(?1, failure_lesson) WHERE id = ?2",
                            (lesson, &obl_id_str),
                        )?;
                    }
                    (result.outcome, is_valid)
                }
                Err(e) => return Err(StepError::LeanGatewayError(e)),
            }
        }
        _ => return Err(StepError::Internal("gateway response variant did not match the finalize context".to_string())),
    };

    finalize_bookkeeping(tx, attempt_id, &episode_id_str, &action_request_id_str, current_revision, cost_micros, is_valid)?;
    Ok(outcome_result)
}

/// Episode revision/step/budget bump, attempt status (committed/rejected), and
/// marking the fulfilling request — the shared tail every action variant writes
/// once its outcome (`is_valid`) is known, whether that happened immediately
/// (`attempt_prepare`'s Done branches) or after a deferred gateway call
/// (`attempt_finalize`).
fn finalize_bookkeeping(
    tx: &Transaction,
    attempt_id: Uuid,
    episode_id_str: &str,
    action_request_id_str: &str,
    current_revision: i64,
    cost_micros: i128,
    is_valid: bool,
) -> Result<(), StepError> {
    let new_revision = current_revision + 1;

    if is_valid {
        tx.execute(
            "UPDATE episodes SET
                current_revision = ?1,
                step_count = step_count + 1,
                cost_budget_micros = cost_budget_micros - ?2,
                updated_at = ?3
             WHERE id = ?4",
            (new_revision, cost_micros as i64, Utc::now().to_rfc3339(), episode_id_str),
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
            (new_revision, cost_micros as i64, Utc::now().to_rfc3339(), episode_id_str),
        )?;

        tx.execute(
            "UPDATE action_attempts SET status = 'rejected', execution_completed_at = ?1 WHERE id = ?2",
            (Utc::now().to_rfc3339(), attempt_id.to_string()),
        )?;
    }

    // Mark the fulfilling request so episode_observe/advance never surface it again.
    tx.execute(
        "UPDATE action_requests SET status = 'fulfilled', fulfilled_at = ?1, fulfilled_attempt_id = ?2 WHERE id = ?3",
        (Utc::now().to_rfc3339(), attempt_id.to_string(), action_request_id_str),
    )?;

    Ok(())
}

/// Convenience wrapper composing `attempt_prepare` + (a synchronous, in-transaction)
/// gateway call + `attempt_finalize` into the original single-call, single-transaction
/// contract. Review feedback on #16/#17 established that the MCP layer's `episode_step`
/// handler must NOT hold the DB mutex while Lean runs — `episode_step` calls
/// `attempt_prepare`/`attempt_finalize` directly, with the gateway invocation happening
/// in between while the lock is released (see `crates/chatdb-mcp/src/lib.rs`). This
/// wrapper exists for callers that run entirely synchronously, outside any async lock
/// (unit/integration tests driving a bare `rusqlite::Transaction` directly) — for those,
/// running the gateway call inside one transaction is simpler and there is no lock to
/// hold across it in the first place.
pub fn attempt_commit(
    tx: &Transaction,
    attempt_id: Uuid,
    expected_revision: i64,
    claim_token: &str,
    action: &TypedAction,
    lean_gateway: &dyn LeanGateway,
    cost_micros: i128,
) -> Result<LeanVerificationOutcome, StepError> {
    match attempt_prepare(tx, attempt_id, expected_revision, claim_token, action, cost_micros)? {
        PrepOutcome::Done { outcome, .. } => Ok(outcome),
        PrepOutcome::NeedsGateway { request, ctx } => {
            let response = match request {
                GatewayRequest::Solve { obl, proof_term, dep_ids, env_hash, import_manifest } => {
                    GatewayResponse::Solve(lean_gateway.verify_exact(&obl, &proof_term, &dep_ids, &env_hash, &import_manifest))
                }
                GatewayRequest::SubmitModule { assembled, env_hash } => {
                    GatewayResponse::SubmitModule(lean_gateway.verify_module(&assembled, &env_hash))
                }
            };
            attempt_finalize(tx, attempt_id, claim_token, cost_micros, ctx, response)
        }
    }
}
