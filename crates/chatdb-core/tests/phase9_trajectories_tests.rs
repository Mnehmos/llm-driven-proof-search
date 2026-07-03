use chatdb_proof_core::orchestrator::{lifecycle, trajectories};
use rusqlite::Connection;
use uuid::Uuid;
use chrono::Utc;

#[test]
fn test_trajectory_recording_and_audit() {
    let mut conn = Connection::open_in_memory().unwrap();
    chatdb_proof_core::db::schema_v1::initialize_v1_db(&conn).unwrap();

    let pv_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, state, created_at
        ) VALUES (
            ?1, 'test', 'hash', '{}',
            'test_stmt', 'stmt_hash', 'rendering',
            'env_hash', 'verified', 'manual', 'COMPLETE', ?2
        )",
        (pv_id.to_string(), Utc::now().to_rfc3339()),
    ).unwrap();

    let tx = conn.transaction().unwrap();

    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();

    let event1_hash = trajectories::record_event(
        &tx, ep_id, "action_attempt", "state1", "state2", "env1", "{}"
    ).unwrap();

    let event2_hash = trajectories::record_event(
        &tx, ep_id, "action_attempt", "state2", "state3", "env1", "{}"
    ).unwrap();
    
    assert_ne!(event1_hash, event2_hash);

    tx.commit().unwrap();

    let is_valid = trajectories::audit_trajectory(&conn, ep_id).unwrap();
    assert!(is_valid);

    // Tamper with the trajectory
    conn.execute(
        "UPDATE trajectory_events SET payload_json = '{\"tampered\": true}' WHERE event_sequence_number = 1",
        [],
    ).unwrap();

    let is_valid_after_tamper = trajectories::audit_trajectory(&conn, ep_id).unwrap();
    assert!(!is_valid_after_tamper);
}
