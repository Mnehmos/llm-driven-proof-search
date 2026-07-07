use rusqlite::Connection;
use std::fs;
use std::path::Path;

use proofsearch_core::db;

#[test]
fn test_migrate_v0_to_v1() -> rusqlite::Result<()> {
    let mut conn = mut_connection();
    
    // Load V0 schema
    let v0_sql = "
        CREATE TABLE obligations (
            id TEXT PRIMARY KEY,
            problem_version_id TEXT NOT NULL,
            kind TEXT NOT NULL,
            theorem_name TEXT NOT NULL,
            lean_statement TEXT NOT NULL,
            statement_hash TEXT NOT NULL,
            natural_description TEXT NOT NULL,
            status TEXT NOT NULL,
            depth_from_root INTEGER NOT NULL,
            created_by TEXT NOT NULL,
            created_by_epoch_id TEXT,
            superseded_by_id TEXT,
            proved_lemma_id TEXT,
            refutation_lemma_id TEXT,
            failure_lesson TEXT,
            attempt_count INTEGER NOT NULL DEFAULT 0,
            created_at TEXT NOT NULL,
            closed_at TEXT
        );
        CREATE TABLE verified_lemmas (
            id TEXT PRIMARY KEY,
            obligation_id TEXT NOT NULL,
            polarity TEXT NOT NULL,
            theorem_name TEXT NOT NULL,
            statement_hash TEXT NOT NULL,
            proof_source_artifact_hash TEXT NOT NULL,
            compiled_artifact_hash TEXT NOT NULL,
            proof_term_hash TEXT NOT NULL,
            environment_hash TEXT NOT NULL,
            actual_dependency_ids_json TEXT NOT NULL,
            kernel_result_hash TEXT NOT NULL,
            verified_at TEXT NOT NULL
        );
    ";
    conn.execute_batch(v0_sql)?;

    // Verify V0 table exists
    let has_obligations: i64 = conn.query_row(
        "SELECT count(*) FROM sqlite_master WHERE type='table' AND name='obligations'",
        [],
        |row| row.get(0),
    )?;
    assert_eq!(has_obligations, 1);

    // Run Migration
    db::migrations::migrate_v0_to_v1(&mut conn)?;

    // Verify V0 tables dropped
    let has_obligations_post: i64 = conn.query_row(
        "SELECT count(*) FROM sqlite_master WHERE type='table' AND name='obligations'",
        [],
        |row| row.get(0),
    )?;
    assert_eq!(has_obligations_post, 0);

    // Verify V1 tables exist
    let has_episodes: i64 = conn.query_row(
        "SELECT count(*) FROM sqlite_master WHERE type='table' AND name='episodes'",
        [],
        |row| row.get(0),
    )?;
    assert_eq!(has_episodes, 1);

    let has_canonical: i64 = conn.query_row(
        "SELECT count(*) FROM sqlite_master WHERE type='table' AND name='canonical_verified_lemmas'",
        [],
        |row| row.get(0),
    )?;
    assert_eq!(has_canonical, 1);

    Ok(())
}

fn mut_connection() -> Connection {
    Connection::open_in_memory().unwrap()
}
