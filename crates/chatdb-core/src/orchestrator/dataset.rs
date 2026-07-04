use rusqlite::{Connection, OptionalExtension};
use uuid::Uuid;
use chrono::Utc;
use std::collections::HashMap;
use sha2::{Sha256, Digest};
use crate::models::dataset::DatasetManifest;

fn sha256_hex(data: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data.as_bytes());
    let res = hasher.finalize();
    let mut s = String::with_capacity(res.len() * 2);
    for byte in res {
        use std::fmt::Write;
        write!(&mut s, "{:02x}", byte).unwrap();
    }
    s
}

/// SFT record: prompt/observation and chosen/accepted action
#[derive(serde::Serialize)]
pub struct SftRecord {
    pub prompt: serde_json::Value,
    pub completion: serde_json::Value,
}

/// RL tuple: (s, a, r, s', terminated, truncated, info)
#[derive(serde::Serialize)]
pub struct RlTuple {
    pub state: serde_json::Value,
    pub action: serde_json::Value,
    pub reward: f64,
    pub next_state: serde_json::Value,
    pub terminated: bool,
    pub truncated: bool,
    pub info: serde_json::Value,
}

/// DPO pair: prompt, chosen, rejected
#[derive(serde::Serialize)]
pub struct DpoPair {
    pub prompt: serde_json::Value,
    pub chosen: serde_json::Value,
    pub rejected: serde_json::Value,
}

pub fn assign_split(problem_id: Uuid) -> &'static str {
    // Deterministic split based on theorem lineage (problem UUID hash)
    let hash = sha256_hex(&problem_id.to_string());
    let bytes = hex::decode(hash).unwrap();
    let val = bytes[0] as u32;
    if val < 204 { // 80%
        "train"
    } else if val < 230 { // 10%
        "validation"
    } else { // 10%
        "test"
    }
}

pub fn export_sft(conn: &Connection, episode_id: Uuid) -> Result<Vec<SftRecord>, String> {
    let mut stmt = conn.prepare(
        "SELECT ar.observation_json, aa.submitted_action_json 
         FROM action_attempts aa
         JOIN action_requests ar ON aa.action_request_id = ar.id
         WHERE aa.episode_id = ?1 AND aa.status = 'committed'
         ORDER BY ar.request_sequence_number ASC"
    ).map_err(|e| e.to_string())?;

    let rows = stmt.query_map([episode_id.to_string()], |row| {
        let obs_str: String = row.get(0)?;
        let act_str: String = row.get(1)?;
        let prompt: serde_json::Value = serde_json::from_str(&obs_str).unwrap_or(serde_json::Value::Null);
        let completion: serde_json::Value = serde_json::from_str(&act_str).unwrap_or(serde_json::Value::Null);
        Ok(SftRecord { prompt, completion })
    }).map_err(|e| e.to_string())?;

    let mut records = Vec::new();
    for r in rows {
        records.push(r.map_err(|e| e.to_string())?);
    }
    Ok(records)
}

pub fn export_rl(conn: &Connection, episode_id: Uuid) -> Result<Vec<RlTuple>, String> {
    // The MCP runtime records step attempts as 'action_committed' (see
    // chatdb-mcp episode_step) — this previously queried the nonexistent
    // 'step_committed', which silently returned zero rows for every
    // MCP-driven episode's RL export.
    let mut stmt = conn.prepare(
        "SELECT state_hash_before, state_hash_after, payload_json
         FROM trajectory_events
         WHERE episode_id = ?1 AND event_type = 'action_committed'
         ORDER BY event_sequence_number ASC"
    ).map_err(|e| e.to_string())?;

    let rows = stmt.query_map([episode_id.to_string()], |row| {
        let hash_before: String = row.get(0)?;
        let hash_after: String = row.get(1)?;
        let payload_str: String = row.get(2)?;

        let mut payload: serde_json::Value = serde_json::from_str(&payload_str).unwrap_or(serde_json::Value::Null);
        let action = payload.get("action").cloned().unwrap_or(serde_json::Value::Null);
        let state = serde_json::json!({ "state_hash": hash_before });
        let next_state = serde_json::json!({ "state_hash": hash_after });

        // Make module solves first-class training data: tag each record so a
        // consumer can distinguish a single-theorem solve from a verified-module
        // solve without re-deriving it from the action shape (issue #4).
        let solve_kind = match action.get("type").and_then(|t| t.as_str()) {
            Some("submit_module") => Some("verified_module_solve"),
            Some("solve") => Some("single_theorem_solve"),
            _ => None,
        };
        if let (Some(kind), Some(obj)) = (solve_kind, payload.as_object_mut()) {
            obj.insert("solve_kind".to_string(), serde_json::Value::String(kind.to_string()));
        }

        // NOTE: the MCP runtime's action_committed payload does not currently carry
        // scalar_reward_micros/terminated/truncated fields (those live only in the
        // episode_step tool response, not the trajectory event) — this still
        // defaults them until the payload schema is extended to include them.
        // Tracked as a follow-up; not part of this fidelity-invariant fix.
        let reward_micros = payload.get("scalar_reward_micros").and_then(|v| v.as_i64()).unwrap_or(0);
        let terminated = payload.get("terminated").and_then(|v| v.as_bool()).unwrap_or(false);
        let truncated = payload.get("truncated").and_then(|v| v.as_bool()).unwrap_or(false);

        Ok(RlTuple {
            state,
            action,
            reward: (reward_micros as f64) / 1_000_000.0,
            next_state,
            terminated,
            truncated,
            info: payload,
        })
    }).map_err(|e| e.to_string())?;

    let mut records = Vec::new();
    for r in rows {
        records.push(r.map_err(|e| e.to_string())?);
    }
    Ok(records)
}

pub fn export_dpo(conn: &Connection, episode_id: Uuid) -> Result<Vec<DpoPair>, String> {
    let mut stmt = conn.prepare(
        "SELECT ar.id, ar.observation_json 
         FROM action_requests ar 
         WHERE ar.episode_id = ?1"
    ).map_err(|e| e.to_string())?;

    let requests = stmt.query_map([episode_id.to_string()], |row| {
        let req_id: String = row.get(0)?;
        let obs: String = row.get(1)?;
        Ok((req_id, obs))
    }).map_err(|e| e.to_string())?;

    let mut pairs = Vec::new();
    for r in requests {
        let (req_id, obs_str) = r.map_err(|e| e.to_string())?;
        
        let chosen_opt: Option<String> = conn.query_row(
            "SELECT submitted_action_json FROM action_attempts WHERE action_request_id = ?1 AND status = 'committed' LIMIT 1",
            [&req_id],
            |row| row.get(0),
        ).optional().map_err(|e| e.to_string())?;

        let rejected_opt: Option<String> = conn.query_row(
            "SELECT submitted_action_json FROM action_attempts WHERE action_request_id = ?1 AND status IN ('rejected', 'preflight_rejected') LIMIT 1",
            [&req_id],
            |row| row.get(0),
        ).optional().map_err(|e| e.to_string())?;

        if let (Some(chosen_str), Some(rejected_str)) = (chosen_opt, rejected_opt) {
            let prompt: serde_json::Value = serde_json::from_str(&obs_str).unwrap_or(serde_json::Value::Null);
            let chosen: serde_json::Value = serde_json::from_str(&chosen_str).unwrap_or(serde_json::Value::Null);
            let rejected: serde_json::Value = serde_json::from_str(&rejected_str).unwrap_or(serde_json::Value::Null);
            pairs.push(DpoPair { prompt, chosen, rejected });
        }
    }
    Ok(pairs)
}

pub fn generate_manifest(
    conn: &Connection,
    name: &str,
    description: &str,
    episode_ids: &[Uuid],
) -> Result<DatasetManifest, String> {
    let mut source_hashes = Vec::new();
    for ep_id in episode_ids {
        let last_hash: Option<String> = conn.query_row(
            "SELECT event_hash FROM trajectory_events WHERE episode_id = ?1 ORDER BY event_sequence_number DESC LIMIT 1",
            [ep_id.to_string()],
            |row| row.get(0),
        ).optional().map_err(|e| e.to_string())?;
        if let Some(h) = last_hash {
            source_hashes.push(h);
        }
    }

    let manifest = DatasetManifest {
        name: name.to_string(),
        description: description.to_string(),
        created_at: Utc::now().to_rfc3339(),
        sanitization_policy_version: "1.0".to_string(),
        removed_field_categories: vec!["api_keys".to_string(), "private_endpoints".to_string()],
        source_trajectory_root_hashes: source_hashes,
        output_checksums: HashMap::new(),
    };

    Ok(manifest)
}
