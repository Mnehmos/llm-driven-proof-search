use rusqlite::Connection;
use uuid::Uuid;
use chatdb_proof_core::db::schema_v1::initialize_v1_db;
use chatdb_proof_core::orchestrator::dataset::{assign_split, export_sft, export_rl, export_dpo, generate_manifest};
use chatdb_proof_core::orchestrator::trajectories::{record_event, export_dataset_trajectory};

#[test]
fn test_contamination_safe_split() {
    let p1 = Uuid::new_v4();
    let s1 = assign_split(p1);
    let s2 = assign_split(p1);
    assert_eq!(s1, s2, "Deterministic splits must be stable");
    
    assert!(s1 == "train" || s1 == "validation" || s1 == "test");
}

#[test]
fn test_dataset_export_and_sanitization() {
    let conn = Connection::open_in_memory().unwrap();
    initialize_v1_db(&conn).unwrap();

    let ep_id = Uuid::new_v4();
    let pv_id = Uuid::new_v4();
    
    // Insert problem and episode
    conn.execute(
        "INSERT INTO problem_versions (id, source_problem_text, source_problem_hash, source_metadata_json, root_formal_statement, root_statement_hash, normalized_root_rendering, environment_hash, fidelity_status, fidelity_method, state, created_at)
         VALUES (?1, 'proof', 'h1', '{}', 'thm', 'h2', 'thm', 'env1', 'verified', 'human', 'PROVING', '2026-07-02T00:00:00Z')",
        (pv_id.to_string(),)
    ).unwrap();

    conn.execute(
        "INSERT INTO episodes (id, problem_version_id, state, current_revision, step_count, cost_budget_micros, invalid_action_count, created_at)
         VALUES (?1, ?2, 'awaiting_external_action', 1, 0, 1000000, 0, '2026-07-02T00:00:00Z')",
        (ep_id.to_string(), pv_id.to_string())
    ).unwrap();

    // Insert action request and committed attempt
    let req_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO action_requests (id, episode_id, problem_version_id, episode_revision, request_sequence_number, role, state_hash_before, status, created_at, observation_json, observation_hash)
         VALUES (?1, ?2, ?3, 1, 1, 'prover', 'dummy_hash', 'fulfilled', '2026-07-02T00:00:00Z', '{\"state\": \"initial\", \"api_key\": \"secret123\"}', 'obs_hash')",
        (req_id.to_string(), ep_id.to_string(), pv_id.to_string())
    ).unwrap();

    let attempt_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO action_attempts (id, episode_id, action_request_id, idempotency_key, expected_revision, claim_token, submitted_action_json, status, claimed_at, raw_external_response)
         VALUES (?1, ?2, ?3, 'ikey', 1, 'ctok', '{\"tactic\": \"rfl\", \"private_endpoint\": \"http://private.int\"}', 'committed', '2026-07-02T00:00:00Z', x'414243')",
        (attempt_id.to_string(), ep_id.to_string(), req_id.to_string())
    ).unwrap();

    // Record trajectory event
    let payload = serde_json::json!({
        "action": {
            "tactic": "rfl",
            "api_key": "secret123",
            "private_endpoint": "http://private.int"
        }
    });
    
    let tx = conn.unchecked_transaction().unwrap();
    // The MCP runtime records this event type as 'action_committed' (see
    // chatdb-mcp episode_step) — this fixture previously used the nonexistent
    // 'step_committed', which matched export_rl's identical bug rather than
    // catching it.
    let ev_hash = record_event(
        &tx,
        ep_id,
        "action_committed",
        "hash_before",
        "hash_after",
        "env_hash",
        &payload.to_string()
    ).unwrap();
    tx.commit().unwrap();

    // 1. Test SFT Export
    let sft = export_sft(&conn, ep_id).unwrap();
    assert_eq!(sft.len(), 1);
    assert_eq!(sft[0].prompt.get("state").unwrap().as_str().unwrap(), "initial");
    
    // 2. Test RL Export
    let rl = export_rl(&conn, ep_id).unwrap();
    assert_eq!(rl.len(), 1);
    assert_eq!(rl[0].action.get("tactic").unwrap().as_str().unwrap(), "rfl");
    
    // 3. Test sanitization in export_dataset_trajectory
    let traj = export_dataset_trajectory(&conn, ep_id).unwrap();
    assert_eq!(traj.len(), 1);
    let parsed: serde_json::Value = serde_json::from_str(&traj[0]).unwrap();
    assert!(parsed.get("action").unwrap().get("api_key").is_none(), "API keys must be scrubbed");
    assert!(parsed.get("action").unwrap().get("private_endpoint").is_none(), "Private endpoints must be scrubbed");

    // 4. Test Manifest Generation
    let manifest = generate_manifest(&conn, "RL Dataset", "DN", &[ep_id]).unwrap();
    assert_eq!(manifest.name, "RL Dataset");
    assert_eq!(manifest.source_trajectory_root_hashes.len(), 1);
    assert_eq!(manifest.source_trajectory_root_hashes[0], ev_hash);
}
