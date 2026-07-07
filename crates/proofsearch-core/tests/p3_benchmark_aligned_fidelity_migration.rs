use rusqlite::Connection;

use proofsearch_core::db;

/// A `problem_versions` / `problem_fidelity_reviews` pair at the CURRENT-minus-#43
/// vocabulary: the 5-value fidelity CHECK (has 'unreviewed' but not
/// 'benchmark_aligned') and the 2-value decision CHECK ('verified','rejected').
/// A database stuck here rejects every 'benchmark_aligned' write with a CHECK
/// constraint violation until migrate_expand_fidelity_status_benchmark_aligned
/// rebuilds both tables.
const PRE_BENCHMARK_ALIGNED_SCHEMA: &str = "
CREATE TABLE problem_versions (
    id TEXT PRIMARY KEY,
    source_problem_text TEXT NOT NULL,
    source_problem_hash TEXT NOT NULL,
    source_metadata_json TEXT NOT NULL,
    root_formal_statement TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    normalized_root_rendering TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    import_manifest_json TEXT NOT NULL DEFAULT '[\"Mathlib.Tactic.Ring\",\"Mathlib.Tactic.NormNum\"]',
    import_manifest_hash TEXT NOT NULL DEFAULT '',
    fidelity_status TEXT NOT NULL,
    fidelity_method TEXT NOT NULL,
    fidelity_approval_id TEXT,
    root_obligation_id TEXT,
    state TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(state NOT IN ('PROVING', 'ROOT_PROVED_COVERAGE_PENDING', 'ROOT_PROVED_COVERAGE_UNCONVERGED') OR fidelity_status IN ('verified', 'attested')),
    CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified'),
    CHECK(fidelity_status IN ('unreviewed', 'attested', 'verified', 'rejected', 'revoked'))
);
CREATE TABLE problem_fidelity_reviews (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    source_problem_hash TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    normalized_rendering_hash TEXT NOT NULL,
    decision TEXT NOT NULL,
    method TEXT NOT NULL,
    approver_id TEXT NOT NULL,
    rubric_version TEXT NOT NULL,
    evidence_json TEXT NOT NULL,
    notes TEXT,
    signature TEXT,
    created_at TEXT NOT NULL,
    revoked_at TEXT,
    CHECK(decision IN ('verified', 'rejected'))
);
";

fn seed_legacy_db(conn: &Connection) -> rusqlite::Result<()> {
    conn.execute_batch(PRE_BENCHMARK_ALIGNED_SCHEMA)?;
    // A pre-existing attested problem — must survive the rebuild untouched.
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES ('pv-old', 's', 'sh', '{}', 'r', 'rh', 'r', 'eh', 'attested', 'unsafe_dev_attestation', NULL, NULL, 'PROVING', '2026-01-01T00:00:00Z')",
        [],
    )?;
    Ok(())
}

/// A database that predates #43 must self-heal on startup so that a
/// `benchmark_aligned` problem_versions row and a `benchmark_aligned` review
/// row — both of which the current code writes via
/// `problem_record_benchmark_alignment` — become insertable, where they
/// previously failed 100% of the time with a CHECK constraint violation.
#[test]
fn test_legacy_database_migrates_benchmark_aligned_vocabulary_on_startup() -> rusqlite::Result<()> {
    let conn = Connection::open_in_memory().unwrap();
    seed_legacy_db(&conn)?;

    db::initialize_db(&conn)?;

    // Pre-existing row survived untouched.
    let old_status: String = conn.query_row(
        "SELECT fidelity_status FROM problem_versions WHERE id = 'pv-old'",
        [], |row| row.get(0),
    )?;
    assert_eq!(old_status, "attested");

    // The regression: a benchmark_aligned problem_versions row (state PROVING)
    // is now insertable.
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, import_manifest_json, import_manifest_hash,
            fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES (
            'pv-ba', 'src', 'srch', '{}', 'stmt', 'stmth', 'stmt', 'envh',
            '[\"Mathlib.Tactic.Ring\",\"Mathlib.Tactic.NormNum\"]', 'hash',
            'benchmark_aligned', 'formal_benchmark_hash_alignment', NULL, NULL, 'PROVING', '2026-01-01T00:00:00Z'
        )",
        [],
    )?;

    // ...and a benchmark_aligned review row.
    conn.execute(
        "INSERT INTO problem_fidelity_reviews (
            id, problem_version_id, source_problem_hash, root_statement_hash,
            normalized_rendering_hash, decision, method, approver_id, rubric_version,
            evidence_json, notes, signature, created_at
        ) VALUES (
            'rev-ba', 'pv-ba', 'srch', 'stmth', 'rh', 'benchmark_aligned',
            'formal_benchmark_hash_alignment', 'runner', 'formal_benchmark_hash_alignment/v1',
            '{}', NULL, NULL, '2026-01-01T00:00:00Z'
        )",
        [],
    )?;

    // The load-bearing guard is preserved: a benchmark_aligned COMPLETE row must
    // STILL be rejected — benchmark_aligned can never certify.
    let complete_attempt = conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, import_manifest_json, import_manifest_hash,
            fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES (
            'pv-bad', 'src', 'srch', '{}', 'stmt', 'stmth', 'stmt', 'envh',
            '[\"Mathlib.Tactic.Ring\",\"Mathlib.Tactic.NormNum\"]', 'hash',
            'benchmark_aligned', 'formal_benchmark_hash_alignment', NULL, NULL, 'COMPLETE', '2026-01-01T00:00:00Z'
        )",
        [],
    );
    assert!(complete_attempt.is_err(), "the COMPLETE-requires-verified guard must survive the migration: benchmark_aligned can never reach COMPLETE");

    // A second startup against the already-migrated database is a no-op.
    db::initialize_db(&conn)?;
    let row_count: i64 = conn.query_row("SELECT COUNT(*) FROM problem_versions", [], |row| row.get(0))?;
    assert_eq!(row_count, 2, "second startup must not duplicate or lose rows");

    Ok(())
}

/// A fresh database comes up with the #43 vocabulary directly from CREATE TABLE.
#[test]
fn test_fresh_database_accepts_benchmark_aligned_vocabulary() -> rusqlite::Result<()> {
    let conn = Connection::open_in_memory().unwrap();
    db::initialize_db(&conn)?;

    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES ('pv-ba', 's', 'sh', '{}', 'r', 'rh', 'r', 'eh', 'benchmark_aligned', 'formal_benchmark_hash_alignment', NULL, NULL, 'PROVING', '2026-01-01T00:00:00Z')",
        [],
    )?;
    Ok(())
}
