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
    // The MCP runtime records step attempts as 'action_committed'. Collect the
    // raw events first and drop the statement, so we can then query the
    // observation store per state hash (issue #231) without a borrow conflict.
    let raw: Vec<(String, String, String)> = {
        let mut stmt = conn.prepare(
            "SELECT state_hash_before, state_hash_after, payload_json
             FROM trajectory_events
             WHERE episode_id = ?1 AND event_type = 'action_committed'
             ORDER BY event_sequence_number ASC",
        ).map_err(|e| e.to_string())?;
        let rows = stmt.query_map([episode_id.to_string()], |row| {
            Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?, row.get::<_, String>(2)?))
        }).map_err(|e| e.to_string())?;
        let mut v = Vec::new();
        for r in rows {
            v.push(r.map_err(|e| e.to_string())?);
        }
        v
    };

    let mut records = Vec::new();
    for (hash_before, hash_after, payload_str) in raw {
        let mut payload: serde_json::Value =
            serde_json::from_str(&payload_str).unwrap_or(serde_json::Value::Null);
        let action = payload.get("action").cloned().unwrap_or(serde_json::Value::Null);

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

        // Issue #231: read the EXACT persisted reward + terminal signals, at the
        // reward policy's own scale factor. Old (pre-schema-1.1) events lack
        // them; mark that honestly in `info` rather than passing a default
        // zero/false off as a measured value.
        let has_reward = payload.get("reward_scaled").is_some();
        let reward = match (
            payload.get("reward_scaled").and_then(|v| v.as_i64()),
            payload.get("reward_scale_factor").and_then(|v| v.as_i64()),
        ) {
            (Some(scaled), Some(scale)) if scale != 0 => (scaled as f64) / (scale as f64),
            _ => 0.0,
        };
        let has_terminal = payload.get("terminated").is_some();
        let terminated = payload.get("terminated").and_then(|v| v.as_bool()).unwrap_or(false);
        let truncated = payload.get("truncated").and_then(|v| v.as_bool()).unwrap_or(false);

        if let Some(obj) = payload.as_object_mut() {
            obj.insert("reward_available".to_string(), serde_json::Value::Bool(has_reward));
            obj.insert("terminal_fields_available".to_string(), serde_json::Value::Bool(has_terminal));
            if !has_reward || !has_terminal {
                obj.insert(
                    "missing_data_note".to_string(),
                    serde_json::Value::String(
                        "pre-#231 trajectory event: reward/terminal not persisted; these are placeholders, not measured values".to_string(),
                    ),
                );
            }
        }

        // Issue #231: state/next-state are reconstructable without the live DB —
        // embed the bounded observation (#223) persisted for each state hash.
        let state = serde_json::json!({
            "state_hash": hash_before,
            "observation": observation_for_hash(conn, &hash_before),
        });
        let next_state = serde_json::json!({
            "state_hash": hash_after,
            "observation": observation_for_hash(conn, &hash_after),
        });

        records.push(RlTuple { state, action, reward, next_state, terminated, truncated, info: payload });
    }
    Ok(records)
}

#[cfg(test)]
mod issue231_tests {
    use super::*;
    use crate::db::initialize_db;
    use chrono::Utc;

    fn setup() -> (Connection, Uuid, Uuid) {
        let conn = Connection::open_in_memory().unwrap();
        initialize_db(&conn).unwrap();
        let pv = Uuid::new_v4();
        conn.execute(
            "INSERT INTO problem_versions (id, source_problem_text, source_problem_hash, source_metadata_json,
                root_formal_statement, root_statement_hash, normalized_root_rendering, environment_hash,
                fidelity_status, fidelity_method, state, created_at)
             VALUES (?1,'s','h','{}','stmt','rh','r','env','unreviewed','manual','CREATED',?2)",
            (pv.to_string(), Utc::now().to_rfc3339()),
        ).unwrap();
        let ep = Uuid::new_v4();
        conn.execute(
            "INSERT INTO episodes (id, problem_version_id, state, created_at) VALUES (?1,?2,'awaiting_external_action',?3)",
            (ep.to_string(), pv.to_string(), Utc::now().to_rfc3339()),
        ).unwrap();
        (conn, ep, pv)
    }

    fn seed_observation(conn: &Connection, ep: Uuid, pv: Uuid, obs_hash: &str, obs_json: &str) {
        conn.execute(
            "INSERT INTO action_requests (id, episode_id, problem_version_id, episode_revision,
                request_sequence_number, role, status, created_at, observation_hash, observation_json)
             VALUES (?1,?2,?3,0,1,'prover','pending',?4,?5,?6)",
            (Uuid::new_v4().to_string(), ep.to_string(), pv.to_string(), Utc::now().to_rfc3339(), obs_hash, obs_json),
        ).unwrap();
    }

    fn record_committed(conn: &mut Connection, ep: Uuid, sb: &str, sa: &str, payload: serde_json::Value) {
        let tx = conn.transaction().unwrap();
        super::super::trajectories::record_event(&tx, ep, "action_committed", sb, sa, "env", &payload.to_string()).unwrap();
        tx.commit().unwrap();
    }

    #[test]
    fn export_rl_reads_persisted_reward_terminal_and_embeds_observation() {
        let (mut conn, ep, pv) = setup();
        seed_observation(&conn, ep, pv, "state-before", "{\"root_theorem_signature\":\"T\"}");
        record_committed(&mut conn, ep, "state-before", "state-after", serde_json::json!({
            "action": {"type": "solve", "proof_term": "x"},
            "trajectory_schema_version": "1.1",
            "reward_scaled": 4900, "reward_scale_factor": 10000,
            "terminated": true, "truncated": false,
        }));
        let tuples = export_rl(&conn, ep).unwrap();
        assert_eq!(tuples.len(), 1);
        let t = &tuples[0];
        assert!((t.reward - 0.49).abs() < 1e-9, "reward must be scaled, not defaulted: {}", t.reward);
        assert!(t.terminated);
        assert!(!t.truncated);
        // State is reconstructable without the live DB: the observation is embedded.
        assert_eq!(t.state["observation"]["root_theorem_signature"], "T");
        assert_eq!(t.info["reward_available"], true);
        assert_eq!(t.info["terminal_fields_available"], true);
        assert_eq!(t.info["solve_kind"], "single_theorem_solve");
    }

    #[test]
    fn export_rl_marks_missing_data_for_old_events_without_silent_defaults() {
        let (mut conn, ep, _pv) = setup();
        // A pre-#231 event: no reward/terminal fields.
        record_committed(&mut conn, ep, "sb", "sa", serde_json::json!({
            "action": {"type": "solve", "proof_term": "y"},
        }));
        let tuples = export_rl(&conn, ep).unwrap();
        let t = &tuples[0];
        assert_eq!(t.reward, 0.0);
        // The zero is HONEST — flagged as unavailable, not passed off as measured.
        assert_eq!(t.info["reward_available"], false);
        assert_eq!(t.info["terminal_fields_available"], false);
        assert!(t.info["missing_data_note"].as_str().unwrap().contains("pre-#231"));
        // No observation was recorded for these hashes -> explicit unavailable marker.
        assert_eq!(t.state["observation"]["unavailable"], true);
    }
}

/// Issue #231: the bounded observation persisted for a given state hash, so an
/// exported RL record is self-contained (reconstructable without the live DB).
/// Returns an explicit unavailable marker when no observation was recorded for
/// that hash (e.g. a terminal next-state that never produced a new request).
fn observation_for_hash(conn: &Connection, state_hash: &str) -> serde_json::Value {
    let obs: Option<String> = conn
        .query_row(
            "SELECT observation_json FROM action_requests WHERE observation_hash = ?1 LIMIT 1",
            [state_hash],
            |row| row.get(0),
        )
        .optional()
        .ok()
        .flatten();
    match obs {
        Some(json) => serde_json::from_str(&json).unwrap_or(serde_json::Value::Null),
        None => serde_json::json!({ "unavailable": true, "state_hash": state_hash }),
    }
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

/// Issue #164: interactive tactic-step negative-space export, sibling to
/// [`export_rl`]'s whole-proof-path RL tuples. This repository has no
/// dedicated `MathCorpus`/`negative_example`-named export path elsewhere
/// (searched the crate for both terms — none found); [`export_rl`]'s
/// `RlTuple` (state/action/reward/next_state/terminated/truncated/info) is
/// the closest existing analog to a per-step training record for the
/// whole-proof path — including its own rejected/failed steps as ordinary
/// tuples rather than dropping them — so this function reuses that exact
/// shape for interactive sessions instead of inventing a new record type.
///
/// A FAILED tactic step (`interactive_proof_steps.outcome = 'failed'`) is a
/// first-class negative example here: never dropped, tagged via
/// `info.negative_example` / `info.outcome`, and (since this is the one case
/// raw tactic text is actually durably persisted — see
/// `interactive_proof_steps.diagnostic_json` / `ProofStateDiagnostic` in
/// `db::interactive`) carries the real failing tactic text and its full
/// diagnostic. A successful (`'applied'`) step carries only its
/// `tactic_text_hash` — the raw text of a successful interactive step is NOT
/// durably persisted server-side by design (issue #161), so this function
/// does not (and cannot) fabricate it.
///
/// TRUST BOUNDARY: `info.session_final_outcome` / `info.kernel_verified` are
/// derived ONLY from the owning session's reconstructed-script
/// `verified_attempt_id` / `verification_outcome` (never from a node's
/// `is_solved` or a script's `reports_complete` alone) — the same rule
/// `proofsearch-mcp`'s `proof_export`/`trajectory_export` interactive-session
/// sections apply. A session that never promoted reads as
/// `"search_in_progress"` or `"closed_without_promotion_*"` /
/// `"reconstructed_not_promoted"`, never as a verified proof.
pub fn export_interactive_rl(conn: &Connection, episode_id: Uuid) -> Result<Vec<RlTuple>, String> {
    use crate::db::interactive as idb;

    let mut stmt = conn
        .prepare("SELECT id FROM interactive_proof_sessions WHERE episode_id = ?1 ORDER BY created_at ASC")
        .map_err(|e| e.to_string())?;
    let session_ids: Vec<String> = stmt
        .query_map([episode_id.to_string()], |row| row.get(0))
        .map_err(|e| e.to_string())?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| e.to_string())?;
    drop(stmt);

    let mut tuples = Vec::new();
    for sid_str in session_ids {
        let sid = Uuid::parse_str(&sid_str).map_err(|e| e.to_string())?;
        let session = idb::get_session(conn, sid)
            .map_err(|e| e.to_string())?
            .ok_or_else(|| format!("interactive session {} vanished mid-export", sid))?;
        let nodes = idb::list_nodes_for_session(conn, sid).map_err(|e| e.to_string())?;
        let steps = idb::list_steps_for_session(conn, sid).map_err(|e| e.to_string())?;
        let reconstructions = idb::list_reconstructed_scripts_for_session(conn, sid).map_err(|e| e.to_string())?;

        let node_by_id: HashMap<Uuid, &idb::NodeRow> = nodes.iter().map(|n| (n.id, n)).collect();

        // Same derivation `proofsearch-mcp`'s interactive-session export
        // sections use — see the function doc's TRUST BOUNDARY paragraph.
        let promoted = reconstructions.iter().find(|r| r.verified_attempt_id.is_some());
        let (session_final_outcome, kernel_verified) = match promoted {
            Some(r) => {
                let outcome = r.verification_outcome.clone().unwrap_or_else(|| "unknown".to_string());
                let kv = outcome == "committed";
                (format!("promoted_{}", outcome), kv)
            }
            None if !reconstructions.is_empty() => ("reconstructed_not_promoted".to_string(), false),
            None if session.state == "closed" => (
                format!("closed_without_promotion_{}", session.close_reason.as_deref().unwrap_or("closed")),
                false,
            ),
            None => ("search_in_progress".to_string(), false),
        };

        for step in &steps {
            let parent_hash = node_by_id.get(&step.parent_node_id).map(|n| n.proof_state_hash.clone());
            let child_hash = step
                .child_node_id
                .and_then(|c| node_by_id.get(&c))
                .map(|n| n.proof_state_hash.clone());
            let negative = step.outcome == "failed";

            let (tactic_text, diagnostic_val) = if negative {
                let diag_val: serde_json::Value = step
                    .diagnostic_json
                    .as_deref()
                    .and_then(|j| serde_json::from_str(j).ok())
                    .unwrap_or(serde_json::Value::Null);
                let raw = diag_val.get("tactic_text").and_then(|v| v.as_str()).map(|s| s.to_string());
                (raw, diag_val)
            } else {
                (None, serde_json::Value::Null)
            };

            let action = serde_json::json!({
                "type": "interactive_tactic_step",
                "outcome": step.outcome,
                "tactic_text_hash": step.tactic_text_hash,
                "tactic_text": tactic_text,
            });
            let terminated = step
                .child_node_id
                .and_then(|c| node_by_id.get(&c))
                .map(|n| n.status == "solved")
                .unwrap_or(false);
            let info = serde_json::json!({
                "session_id": sid.to_string(),
                "episode_id": episode_id.to_string(),
                "obligation_id": session.obligation_id.to_string(),
                "step_id": step.id.to_string(),
                "negative_example": negative,
                "diagnostic": diagnostic_val,
                "wall_time_ms": step.wall_time_ms,
                "session_final_outcome": session_final_outcome,
                "kernel_verified": kernel_verified,
            });

            tuples.push(RlTuple {
                state: serde_json::json!({ "state_hash": parent_hash }),
                action,
                reward: if negative { -1.0 } else { 0.0 },
                next_state: serde_json::json!({ "state_hash": child_hash }),
                terminated,
                truncated: false,
                info,
            });
        }
    }
    Ok(tuples)
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
