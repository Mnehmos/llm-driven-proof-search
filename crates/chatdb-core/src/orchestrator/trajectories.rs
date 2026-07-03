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
        if action_type != "solve" {
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

        let proof_term = payload.get("action").and_then(|a| a.get("proof_term")).and_then(|s| s.as_str())
            .ok_or_else(|| "trajectory event missing action.proof_term".to_string())?;
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
            .verify_exact(&obl, proof_term, &dep_ids, &lean_environment_hash, &import_manifest)
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

fn scrub_value(val: &mut serde_json::Value) {
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
