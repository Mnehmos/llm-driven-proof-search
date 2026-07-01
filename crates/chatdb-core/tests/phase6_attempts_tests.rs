use chatdb_proof_core::orchestrator::{lifecycle, attempts};
use rusqlite::Connection;
use uuid::Uuid;
use chrono::Utc;

#[test]
fn test_attempts_state_machine() {
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
            'env_hash', 'approved', 'manual', 'COMPLETE', ?2
        )",
        (pv_id.to_string(), Utc::now().to_rfc3339()),
    ).unwrap();

    let tx = conn.transaction().unwrap();

    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    // 1. Claim the request
    let claim_res = attempts::attempt_claim(
        &tx, ep_id, req_id, "idempotency_123", 1
    ).unwrap().expect("Should be claimable");

    // Request should be claimed
    let req_status: String = tx.query_row(
        "SELECT status FROM action_requests WHERE id = ?1",
        [req_id.to_string()],
        |row| row.get(0)
    ).unwrap();
    assert_eq!(req_status, "claimed");

    // Can't claim it again
    let claim_res2 = attempts::attempt_claim(
        &tx, ep_id, req_id, "idempotency_456", 1
    ).unwrap();
    assert!(claim_res2.is_none());

    // 2. Recover expired attempt
    // Manually backdate the expiration to make it expired
    tx.execute(
        "UPDATE action_attempts SET claim_expiration = ?1 WHERE id = ?2",
        ((Utc::now() - chrono::Duration::hours(1)).to_rfc3339(), claim_res.attempt_id.to_string())
    ).unwrap();

    let recovered = attempts::attempt_recover_expired(&tx).unwrap();
    assert_eq!(recovered, 1);

    // Request should be pending again
    let req_status2: String = tx.query_row(
        "SELECT status FROM action_requests WHERE id = ?1",
        [req_id.to_string()],
        |row| row.get(0)
    ).unwrap();
    assert_eq!(req_status2, "pending");

    // Attempt should be expired
    let att_status: String = tx.query_row(
        "SELECT status FROM action_attempts WHERE id = ?1",
        [claim_res.attempt_id.to_string()],
        |row| row.get(0)
    ).unwrap();
    assert_eq!(att_status, "expired");

    tx.commit().unwrap();
}
