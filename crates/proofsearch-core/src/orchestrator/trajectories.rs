use rusqlite::{Connection, Result, Transaction, OptionalExtension};
use uuid::Uuid;
use chrono::{DateTime, Utc};
use sha2::{Sha256, Digest};
use std::fmt::Write;

pub struct TrajectoryEvent {
    pub id: i64,
    pub episode_id: Uuid,
    pub event_sequence_number: i64,
    pub event_type: String,
    pub event_hash: String,
    pub previous_event_hash: String,
    pub state_hash_before: String,
    pub state_hash_after: String,
    pub lean_environment_hash: String,
    pub payload_json: String,
    pub payload_hash: String,
    pub created_at: DateTime<Utc>,
}

fn hex_encode(data: &[u8]) -> String {
    let mut s = String::with_capacity(data.len() * 2);
    for byte in data {
        write!(&mut s, "{:02x}", byte).unwrap();
    }
    s
}

pub fn record_event(
    tx: &Transaction,
    episode_id: Uuid,
    event_type: &str,
    state_hash_before: &str,
    state_hash_after: &str,
    lean_environment_hash: &str,
    payload_json: &str,
) -> Result<String, String> {
    let now = Utc::now().to_rfc3339();
    let episode_id_str = episode_id.to_string();

    let last_event: Option<(i64, String)> = tx.query_row(
        "SELECT event_sequence_number, event_hash FROM trajectory_events 
         WHERE episode_id = ?1 ORDER BY event_sequence_number DESC LIMIT 1",
        [&episode_id_str],
        |row| Ok((row.get(0)?, row.get(1)?)),
    ).optional().map_err(|e| e.to_string())?;

    let (seq_num, prev_hash) = match last_event {
        Some((s, h)) => (s + 1, h),
        None => (1, "GENESIS".to_string()),
    };

    let mut payload_hasher = Sha256::new();
    payload_hasher.update(payload_json.as_bytes());
    let payload_hash = hex_encode(&payload_hasher.finalize());

    let mut event_hasher = Sha256::new();
    event_hasher.update(episode_id_str.as_bytes());
    event_hasher.update(&seq_num.to_be_bytes());
    event_hasher.update(event_type.as_bytes());
    event_hasher.update(prev_hash.as_bytes());
    event_hasher.update(state_hash_before.as_bytes());
    event_hasher.update(state_hash_after.as_bytes());
    event_hasher.update(lean_environment_hash.as_bytes());
    event_hasher.update(payload_hash.as_bytes());
    
    let event_hash = hex_encode(&event_hasher.finalize());

    tx.execute(
        "INSERT INTO trajectory_events (
            episode_id, event_sequence_number, event_type, event_hash,
            previous_event_hash, state_hash_before, state_hash_after,
            lean_environment_hash, payload_json, payload_hash, created_at
        ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11)",
        (
            &episode_id_str,
            seq_num,
            event_type,
            &event_hash,
            &prev_hash,
            state_hash_before,
            state_hash_after,
            lean_environment_hash,
            payload_json,
            &payload_hash,
            &now,
        ),
    ).map_err(|e| e.to_string())?;

    Ok(event_hash)
}

pub fn audit_trajectory(conn: &Connection, episode_id: Uuid) -> Result<bool, String> {
    let mut stmt = conn.prepare(
        "SELECT event_sequence_number, event_type, event_hash, previous_event_hash, 
                state_hash_before, state_hash_after, lean_environment_hash, payload_json, payload_hash 
         FROM trajectory_events WHERE episode_id = ?1 ORDER BY event_sequence_number ASC"
    ).map_err(|e| e.to_string())?;

    let mut rows = stmt.query([episode_id.to_string()]).map_err(|e| e.to_string())?;
    
    let mut expected_prev_hash = "GENESIS".to_string();
    let mut expected_seq_num = 1;

    while let Some(row) = rows.next().map_err(|e| e.to_string())? {
        let seq_num: i64 = row.get(0).map_err(|e| e.to_string())?;
        let event_type: String = row.get(1).map_err(|e| e.to_string())?;
        let event_hash: String = row.get(2).map_err(|e| e.to_string())?;
        let prev_hash: String = row.get(3).map_err(|e| e.to_string())?;
        let state_hash_before: String = row.get(4).map_err(|e| e.to_string())?;
        let state_hash_after: String = row.get(5).map_err(|e| e.to_string())?;
        let lean_env_hash: String = row.get(6).map_err(|e| e.to_string())?;
        let payload_json: String = row.get(7).map_err(|e| e.to_string())?;
        let payload_hash: String = row.get(8).map_err(|e| e.to_string())?;

        if seq_num != expected_seq_num {
            return Ok(false);
        }

        if prev_hash != expected_prev_hash {
            return Ok(false);
        }

        let mut p_hasher = Sha256::new();
        p_hasher.update(payload_json.as_bytes());
        let computed_payload_hash = hex_encode(&p_hasher.finalize());
        if computed_payload_hash != payload_hash {
            return Ok(false);
        }

        let mut event_hasher = Sha256::new();
        event_hasher.update(episode_id.to_string().as_bytes());
        event_hasher.update(&seq_num.to_be_bytes());
        event_hasher.update(event_type.as_bytes());
        event_hasher.update(prev_hash.as_bytes());
        event_hasher.update(state_hash_before.as_bytes());
        event_hasher.update(state_hash_after.as_bytes());
        event_hasher.update(lean_env_hash.as_bytes());
        event_hasher.update(payload_hash.as_bytes());
        
        let computed_hash = hex_encode(&event_hasher.finalize());
        if computed_hash != event_hash {
            return Ok(false);
        }

        expected_prev_hash = event_hash;
        expected_seq_num += 1;
    }

    Ok(true)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReplayStatus {
    /// No trajectory events exist for this episode — nothing was replayed.
    Empty,
    /// Every `action_committed` Solve event re-verified to the same Lean outcome
    /// that was originally recorded. Carries the count of solve events checked.
    Matched(usize),
}

impl std::fmt::Display for ReplayStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplayStatus::Empty => write!(f, "empty"),
            ReplayStatus::Matched(n) => write!(f, "matched({n})"),
        }
    }
}

/// Re-executes every recorded `solve` action through the Lean gateway and checks the
/// outcome matches what was committed at the time. Non-solve events (decompose,
/// give_up, episode lifecycle markers) are structural only and are not re-verified.
pub fn replay_trajectory(
    conn: &Connection,
    episode_id: Uuid,
    lean_gateway: &dyn crate::lean::LeanGateway,
) -> Result<ReplayStatus, String> {
    let mut stmt = conn.prepare(
        "SELECT event_type, payload_json, lean_environment_hash FROM trajectory_events
         WHERE episode_id = ?1 ORDER BY event_sequence_number ASC",
    ).map_err(|e| e.to_string())?;

    let rows: Vec<(String, String, String)> = stmt
        .query_map([episode_id.to_string()], |row| {
            Ok((row.get(0)?, row.get(1)?, row.get(2)?))
        }).map_err(|e| e.to_string())?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| e.to_string())?;

    if rows.is_empty() {
        return Ok(ReplayStatus::Empty);
    }

    let mut solve_events_checked = 0usize;

    for (event_type, payload_json, lean_environment_hash) in rows {
        if event_type != "action_committed" {
            continue;
        }
        let payload: serde_json::Value = serde_json::from_str(&payload_json)
            .map_err(|e| format!("corrupt trajectory payload: {}", e))?;

        let Some(action_type) = payload.get("action").and_then(|a| a.get("type")).and_then(|t| t.as_str()) else {
            continue;
        };
        if action_type != "solve" && action_type != "submit_module" {
            continue;
        }

        // The trajectory is append-only truth: it also records attempts that never
        // reached the Lean gateway (stale revision, forged claim, gateway/infra
        // error). Those carry no Lean outcome (`outcome: null` / disposition !=
        // "accepted") — there is nothing deterministic to re-verify, so skip them.
        let disposition = payload.get("disposition").and_then(|s| s.as_str()).unwrap_or("");
        let Some(recorded_outcome) = payload.get("outcome").and_then(|s| s.as_str()) else {
            continue;
        };
        if disposition != "accepted" {
            continue;
        }

        // A verified module replays by re-assembling from its structured JSON
        // (never an opaque saved file), re-hashing, and re-verifying — and it must
        // FAIL if the current output differs from the recorded artifact.
        if action_type == "submit_module" {
            // Only successful modules carry a persisted artifact to round-trip.
            let accepted = payload.get("accepted").and_then(|v| v.as_bool()).unwrap_or(false);
            if !accepted {
                continue;
            }
            let problem_version_id_str = payload.get("problem_version_id").and_then(|s| s.as_str())
                .ok_or_else(|| "module trajectory event missing problem_version_id".to_string())?;
            let recorded_statement_hash = payload.get("statement_hash").and_then(|s| s.as_str())
                .ok_or_else(|| "module trajectory event missing statement_hash".to_string())?;
            let recorded_source_hash = payload.get("module_source_hash").and_then(|s| s.as_str())
                .ok_or_else(|| "module trajectory event missing module_source_hash".to_string())?;
            let recorded_decl_hash = payload.get("declaration_manifest_hash").and_then(|s| s.as_str())
                .ok_or_else(|| "module trajectory event missing declaration_manifest_hash".to_string())?;

            // Re-parse the structured action and re-assemble deterministically.
            let action: crate::models::action::TypedAction = serde_json::from_value(
                payload.get("action").cloned().unwrap_or(serde_json::Value::Null)
            ).map_err(|e| format!("corrupt module action in trajectory: {}", e))?;
            let crate::models::action::TypedAction::SubmitModule { module_items, root_theorem } = action else {
                return Err("submit_module event did not deserialize to a SubmitModule action".to_string());
            };

            let import_manifest_json: String = conn.query_row(
                "SELECT import_manifest_json FROM problem_versions WHERE id = ?1",
                [problem_version_id_str],
                |row| row.get(0),
            ).map_err(|e| e.to_string())?;
            let import_manifest: Vec<String> = serde_json::from_str(&import_manifest_json).unwrap_or_default();

            let ns16 = problem_version_id_str.replace('-', "");
            let problem_namespace = format!("ProofSearch.P_{}", &ns16[..16.min(ns16.len())]);

            let assembled = crate::lean::module::assemble_module(
                &problem_namespace, recorded_statement_hash, &module_items, &root_theorem, &import_manifest,
            ).map_err(|e| format!("replay re-assembly failed (module no longer passes policy): {}", e))?;

            if assembled.module_source_hash != recorded_source_hash {
                return Err(format!(
                    "replay detected changed module source: recorded module_source_hash={}, re-assembled={}",
                    recorded_source_hash, assembled.module_source_hash
                ));
            }
            if assembled.declaration_manifest_hash != recorded_decl_hash {
                return Err(format!(
                    "replay detected changed declaration manifest: recorded={}, re-assembled={}",
                    recorded_decl_hash, assembled.declaration_manifest_hash
                ));
            }

            let result = lean_gateway.verify_module(&assembled, &lean_environment_hash)
                .map_err(|e| format!("replay module verification failed: {}", e))?;
            let replayed_outcome = result.outcome.to_string();
            if replayed_outcome != recorded_outcome {
                return Err(format!(
                    "replay mismatch on module for obligation {}: recorded={}, replayed={}",
                    payload.get("obligation_id").and_then(|s| s.as_str()).unwrap_or("?"),
                    recorded_outcome, replayed_outcome
                ));
            }
            solve_events_checked += 1;
            continue;
        }

        let proof_term = payload.get("action").and_then(|a| a.get("proof_term")).and_then(|s| s.as_str())
            .ok_or_else(|| "trajectory event missing action.proof_term".to_string())?;
        // Issue #51: replay must re-verify with the SAME transport format the
        // original attempt used, or a raw_lean_block proof's recorded outcome
        // wouldn't reproduce. Absent (older trajectories) -> flat default.
        let proof_format: crate::models::action::ProofFormat = payload.get("action")
            .and_then(|a| a.get("proof_format"))
            .map(|v| serde_json::from_value(v.clone()))
            .transpose()
            .map_err(|e| format!("invalid action.proof_format in trajectory: {}", e))?
            .unwrap_or_default();
        let lean_statement = payload.get("lean_statement").and_then(|s| s.as_str())
            .ok_or_else(|| "trajectory event missing lean_statement".to_string())?;
        let statement_hash = payload.get("statement_hash").and_then(|s| s.as_str()).unwrap_or("").to_string();
        let obligation_id_str = payload.get("obligation_id").and_then(|s| s.as_str())
            .ok_or_else(|| "trajectory event missing obligation_id".to_string())?;
        let problem_version_id_str = payload.get("problem_version_id").and_then(|s| s.as_str())
            .ok_or_else(|| "trajectory event missing problem_version_id".to_string())?;
        let dep_ids: Vec<Uuid> = payload.get("dependency_obligation_ids")
            .and_then(|v| v.as_array())
            .map(|arr| arr.iter().filter_map(|v| v.as_str()).filter_map(|s| Uuid::parse_str(s).ok()).collect())
            .unwrap_or_default();

        let obl = crate::models::Obligation {
            id: Uuid::parse_str(obligation_id_str).map_err(|e| e.to_string())?,
            problem_version_id: Uuid::parse_str(problem_version_id_str).map_err(|e| e.to_string())?,
            kind: crate::models::ObligationKind::Proof,
            theorem_name: "replay".to_string(),
            lean_statement: lean_statement.to_string(),
            statement_hash,
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

        // The import manifest is immutable per problem_version — re-fetching it
        // here (rather than trusting anything in the payload) means replay always
        // verifies against the exact same import closure the original attempt used.
        let import_manifest_json: String = conn.query_row(
            "SELECT import_manifest_json FROM problem_versions WHERE id = ?1",
            [problem_version_id_str],
            |row| row.get(0),
        ).map_err(|e| e.to_string())?;
        let import_manifest: Vec<String> = serde_json::from_str(&import_manifest_json).unwrap_or_default();

        let result = lean_gateway
            .verify_exact(&obl, proof_term, &dep_ids, &lean_environment_hash, &import_manifest, proof_format)
            .map_err(|e| format!("replay verification failed: {}", e))?;

        let replayed_outcome = result.outcome.to_string();
        if replayed_outcome != recorded_outcome {
            return Err(format!(
                "replay mismatch on obligation {}: recorded={}, replayed={}",
                obligation_id_str, recorded_outcome, replayed_outcome
            ));
        }
        solve_events_checked += 1;
    }

    Ok(ReplayStatus::Matched(solve_events_checked))
}

pub fn scrub_value(val: &mut serde_json::Value) {
    if let Some(obj) = val.as_object_mut() {
        obj.remove("api_key");
        obj.remove("private_endpoint");
        obj.remove("auth_token");
        obj.remove("credentials");
        for (_, v) in obj.iter_mut() {
            scrub_value(v);
        }
    } else if let Some(arr) = val.as_array_mut() {
        for v in arr.iter_mut() {
            scrub_value(v);
        }
    }
}

#[cfg(test)]
mod module_replay_tests {
    use super::*;
    use crate::lean::LeanGateway;
    use crate::lean::module::{assemble_module, AssembledModule};
    use crate::models::action::{LeanModuleItem, ModuleTheorem, ProofFormat, TypedAction};
    use crate::models::{LeanVerificationResult, LeanModuleVerificationResult, LeanVerificationOutcome, Obligation};

    /// Minimal gateway: modules always kernel-pass (policy already ran in
    /// assemble). Lets replay exercise the re-assembly + hash-compare logic
    /// without a real Lean toolchain.
    struct PassGw;
    impl LeanGateway for PassGw {
        fn verify_exact(&self, _o: &Obligation, _s: &str, _d: &[Uuid], _e: &str, _m: &[String], _f: ProofFormat) -> Result<LeanVerificationResult, String> {
            Err("not used".to_string())
        }
        fn verify_module(&self, assembled: &AssembledModule, environment: &str) -> Result<LeanModuleVerificationResult, String> {
            Ok(LeanModuleVerificationResult {
                outcome: LeanVerificationOutcome::KernelPass,
                problem_namespace: assembled.namespace.clone(),
                root_lean_name: assembled.root_lean_name.clone(),
                module_source_hash: assembled.module_source_hash.clone(),
                declaration_manifest_hash: assembled.declaration_manifest_hash.clone(),
                environment_hash: environment.to_string(),
                kernel_result_hash: "k".to_string(),
                diagnostic: None,
                all_diagnostics: vec![],
                resource_policy: None,
                output_receipt: None,
                durability_job: None,
                wall_time_ms: 1,
            })
        }
    }

    fn manifest() -> Vec<String> { vec!["Mathlib.Tactic.Ring".to_string()] }

    /// Builds a DB with one committed module trajectory event. `source_hash_in_payload`
    /// lets a caller record a WRONG module_source_hash to simulate tampering.
    fn setup(conn: &Connection, source_hash_in_payload: Option<String>) -> (Uuid, String, String) {
        crate::db::schema_v1::initialize_v1_db(conn).unwrap();
        let pv_id = Uuid::new_v4();
        let ns16 = pv_id.to_string().replace('-', "");
        let namespace = format!("ProofSearch.P_{}", &ns16[..16]);
        let root_stmt = "True";
        let root_hash = crate::hashing::canonical_hash(&root_stmt.to_string()).unwrap();
        let manifest_json = serde_json::to_string(&manifest()).unwrap();

        conn.execute(
            "INSERT INTO problem_versions (id, source_problem_text, source_problem_hash, source_metadata_json,
                root_formal_statement, root_statement_hash, normalized_root_rendering, environment_hash,
                import_manifest_json, import_manifest_hash, fidelity_status, fidelity_method, state, created_at)
             VALUES (?1,'t','h','{}',?2,?3,?2,'env',?4,'mh','unreviewed','manual','CREATED','now')",
            (pv_id.to_string(), root_stmt, &root_hash, &manifest_json),
        ).unwrap();
        let ep_id = Uuid::new_v4();
        conn.execute(
            "INSERT INTO episodes (id, problem_version_id, state, current_revision, step_count, invalid_action_count, created_at)
             VALUES (?1, ?2, 'awaiting_external_action', 0, 0, 0, 'now')",
            (ep_id.to_string(), pv_id.to_string()),
        ).unwrap();

        let items = vec![LeanModuleItem::Def { name: "z".to_string(), type_signature: "Nat".to_string(), body: "0".to_string() }];
        let root = ModuleTheorem { name: "root".to_string(), statement: root_stmt.to_string(), proof_term: "trivial".to_string(), proof_format: ProofFormat::FlatTacticSequence };
        let asm = assemble_module(&namespace, &root_hash, &items, &root, &manifest()).unwrap();

        let action = TypedAction::SubmitModule { module_items: items, root_theorem: root };
        let recorded_source_hash = source_hash_in_payload.unwrap_or_else(|| asm.module_source_hash.clone());
        let payload = serde_json::json!({
            "obligation_id": Uuid::new_v4().to_string(),
            "problem_version_id": pv_id.to_string(),
            "statement_hash": root_hash,
            "action": action,
            "outcome": "kernel_pass",
            "disposition": "accepted",
            "accepted": true,
            "module_source_hash": recorded_source_hash,
            "declaration_manifest_hash": asm.declaration_manifest_hash,
        });

        let tx = conn.unchecked_transaction().unwrap();
        record_event(&tx, ep_id, "action_committed", "GENESIS", "after", "env", &payload.to_string()).unwrap();
        tx.commit().unwrap();
        (ep_id, asm.module_source_hash, root_hash)
    }

    #[test]
    fn replay_succeeds_for_successful_module() {
        let conn = Connection::open_in_memory().unwrap();
        let (ep_id, _src, _rh) = setup(&conn, None);
        let status = replay_trajectory(&conn, ep_id, &PassGw).unwrap();
        assert_eq!(status, ReplayStatus::Matched(1), "the module must re-assemble, re-hash, and re-verify");
    }

    #[test]
    fn replay_detects_changed_module_source() {
        let conn = Connection::open_in_memory().unwrap();
        // Record a module_source_hash that does NOT match what the action
        // re-assembles to — as if the stored artifact were tampered with.
        let (ep_id, _src, _rh) = setup(&conn, Some("deadbeef_tampered_hash".to_string()));
        let err = replay_trajectory(&conn, ep_id, &PassGw).unwrap_err();
        assert!(err.contains("changed module source"), "replay must fail on a source-hash mismatch, got: {}", err);
    }
}

pub fn export_dataset_trajectory(
    conn: &Connection,
    episode_id: Uuid
) -> Result<Vec<String>, String> {
    // Fetches the trajectory and scrubs private metadata
    let mut stmt = conn.prepare(
        "SELECT payload_json FROM trajectory_events 
         WHERE episode_id = ?1 ORDER BY event_sequence_number ASC"
    ).map_err(|e| e.to_string())?;

    let mut rows = stmt.query([episode_id.to_string()]).map_err(|e| e.to_string())?;
    
    let mut exported_events = Vec::new();
    while let Some(row) = rows.next().map_err(|e| e.to_string())? {
        let payload_str: String = row.get(0).map_err(|e| e.to_string())?;
        
        let mut val: serde_json::Value = serde_json::from_str(&payload_str)
            .map_err(|e| e.to_string())?;
        
        scrub_value(&mut val);
        exported_events.push(serde_json::to_string(&val).unwrap());
    }

    Ok(exported_events)
}
