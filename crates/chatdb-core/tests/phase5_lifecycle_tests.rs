use rusqlite::Connection;
use uuid::Uuid;
use chrono::Utc;

use chatdb_proof_core::db::schema_v1;
use chatdb_proof_core::orchestrator::lifecycle;

fn setup_db() -> Connection {
    let conn = Connection::open_in_memory().unwrap();
    schema_v1::initialize_v1_db(&conn).unwrap();
    conn
}

#[test]
fn test_episode_lifecycle() {
    let mut conn = setup_db();
    
    // Insert a dummy problem_version and root obligation for seeding
    let pv_id = Uuid::new_v4();
    let root_obl_id = Uuid::new_v4();
    
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

    // 1. Test episode_create
    let ep_id = lifecycle::episode_create(
        &tx,
        pv_id,
    ).unwrap();

    let state: String = tx.query_row(
        "SELECT state FROM episodes WHERE id = ?1",
        [ep_id.to_string()],
        |row| row.get(0),
    ).unwrap();
    assert_eq!(state, "awaiting_external_action");

    // 2. Test advance() on a fresh episode
    let req_id1 = lifecycle::advance(&tx, ep_id).unwrap().expect("Should create a request");

    let req_status: String = tx.query_row(
        "SELECT status FROM action_requests WHERE id = ?1",
        [req_id1.to_string()],
        |row| row.get(0),
    ).unwrap();
    assert_eq!(req_status, "pending");

    let obl_count: i64 = tx.query_row(
        "SELECT count(*) FROM episode_obligations WHERE episode_id = ?1",
        [ep_id.to_string()],
        |row| row.get(0),
    ).unwrap();
    assert_eq!(obl_count, 1, "Should have seeded root obligation");

    // 3. Test nondestructive episode_reset()
    let new_ep_id = lifecycle::episode_reset(&tx, ep_id).unwrap();
    assert_ne!(ep_id, new_ep_id);
    
    let parent_id: Option<String> = tx.query_row(
        "SELECT parent_episode_id FROM episodes WHERE id = ?1",
        [new_ep_id.to_string()],
        |row| row.get(0),
    ).unwrap();
    assert_eq!(parent_id, Some(ep_id.to_string()));

    let new_state: String = tx.query_row(
        "SELECT state FROM episodes WHERE id = ?1",
        [new_ep_id.to_string()],
        |row| row.get(0),
    ).unwrap();
    assert_eq!(new_state, "awaiting_external_action");

    tx.commit().unwrap();
}
