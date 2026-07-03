use rusqlite::Connection;

use chatdb_proof_core::db;

/// A pre-fidelity-split `problem_versions`/`episodes` pair — the exact shape
/// found in a real long-lived database in the wild: CHECK(fidelity_status IN
/// ('pending','approved','revoked')) and CHECK(outcome IN (... no
/// 'kernel_verified' ...)). Every `problem_create` against a database stuck at
/// this schema fails deterministically with a CHECK constraint violation,
/// since current code always inserts 'unreviewed'/'attested'/'verified'.
/// See docs/fix_plan_playtest_05.md.
const PRE_FIDELITY_SPLIT_SCHEMA: &str = "
CREATE TABLE problem_versions (
    id TEXT PRIMARY KEY,
    source_problem_text TEXT NOT NULL,
    source_problem_hash TEXT NOT NULL,
    source_metadata_json TEXT NOT NULL,
    root_formal_statement TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    normalized_root_rendering TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    fidelity_status TEXT NOT NULL,
    fidelity_method TEXT NOT NULL,
    fidelity_approval_id TEXT,
    root_obligation_id TEXT,
    state TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(state NOT IN ('PROVING', 'ROOT_PROVED_COVERAGE_PENDING', 'COMPLETE', 'ROOT_PROVED_COVERAGE_UNCONVERGED') OR fidelity_status = 'approved'),
    CHECK(fidelity_status IN ('pending', 'approved', 'revoked'))
);
CREATE TABLE episodes (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    task_id TEXT,
    task_revision INTEGER,
    environment_version TEXT,
    protocol_version TEXT,
    observation_schema_version TEXT,
    action_schema_version TEXT,
    reward_policy_version TEXT,
    verifier_version TEXT,
    lean_toolchain_version TEXT,
    seed INTEGER,
    state TEXT NOT NULL,
    current_revision INTEGER NOT NULL DEFAULT 0,
    initial_state_hash TEXT,
    current_state_hash TEXT,
    step_count INTEGER NOT NULL DEFAULT 0,
    max_steps INTEGER,
    token_budget INTEGER,
    cost_budget_micros INTEGER,
    wall_clock_deadline TEXT,
    invalid_action_count INTEGER NOT NULL DEFAULT 0,
    invalid_action_limit INTEGER,
    outcome TEXT,
    termination_reason TEXT,
    truncation_reason TEXT,
    run_id TEXT,
    parent_episode_id TEXT REFERENCES episodes(id),
    created_at TEXT NOT NULL,
    updated_at TEXT,
    completed_at TEXT,
    CHECK(state IN ('awaiting_external_action', 'executing_action', 'terminated', 'truncated')),
    CHECK(outcome IN ('certified', 'refuted', 'gave_up', 'timeout', 'budget_exhausted', 'model_error', 'infrastructure_error') OR outcome IS NULL),
    CHECK((state = 'terminated' AND outcome IS NOT NULL AND termination_reason IS NOT NULL) OR state <> 'terminated'),
    CHECK((state = 'truncated' AND outcome IS NOT NULL AND truncation_reason IS NOT NULL) OR state <> 'truncated'),
    CHECK(NOT (state = 'terminated' AND truncation_reason IS NOT NULL)),
    CHECK(NOT (state = 'truncated' AND termination_reason IS NOT NULL))
);
";

fn seed_legacy_db(conn: &Connection) -> rusqlite::Result<()> {
    conn.execute_batch(PRE_FIDELITY_SPLIT_SCHEMA)?;
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES ('pv-complete', 's', 'sh', '{}', 'r', 'rh', 'r', 'eh', 'approved', 'human_review', 'appr-1', NULL, 'COMPLETE', '2026-01-01T00:00:00Z')",
        [],
    )?;
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES ('pv-proving', 's2', 'sh2', '{}', 'r2', 'rh2', 'r2', 'eh2', 'approved', 'human_review', 'appr-2', NULL, 'PROVING', '2026-01-01T00:00:00Z')",
        [],
    )?;
    conn.execute(
        "INSERT INTO episodes (
            id, problem_version_id, state, current_revision, step_count,
            invalid_action_count, outcome, termination_reason, created_at
        ) VALUES ('ep-1', 'pv-proving', 'terminated', 1, 1, 0, 'certified', 'root_certified', '2026-01-01T00:00:00Z')",
        [],
    )?;
    Ok(())
}

/// The exact bug hit live: a database that predates the fidelity-vocabulary
/// rewrite must self-heal on startup — old rows get remapped to the current
/// vocabulary, and a fresh INSERT using the current vocabulary (what every
/// problem_create call does) must succeed afterward, where it previously
/// failed 100% of the time with a CHECK constraint violation.
#[test]
fn test_legacy_database_migrates_fidelity_vocabulary_on_startup() -> rusqlite::Result<()> {
    let conn = Connection::open_in_memory().unwrap();
    seed_legacy_db(&conn)?;

    db::initialize_db(&conn)?;

    let (complete_status, complete_state): (String, String) = conn.query_row(
        "SELECT fidelity_status, state FROM problem_versions WHERE id = 'pv-complete'",
        [],
        |row| Ok((row.get(0)?, row.get(1)?)),
    )?;
    assert_eq!(complete_status, "verified", "'approved' must map to 'verified', not 'attested' — an 'attested' COMPLETE row would violate the current CHECK constraint immediately");
    assert_eq!(complete_state, "COMPLETE");

    let proving_status: String = conn.query_row(
        "SELECT fidelity_status FROM problem_versions WHERE id = 'pv-proving'",
        [],
        |row| row.get(0),
    )?;
    assert_eq!(proving_status, "verified");

    // The actual regression: a fresh problem_create-shaped INSERT using the
    // CURRENT vocabulary must succeed post-migration, where it previously
    // failed unconditionally with "CHECK constraint failed: fidelity_status
    // IN ('pending', 'approved', 'revoked')".
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, import_manifest_json, import_manifest_hash,
            fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES (
            'pv-new', 'src', 'srch', '{}', 'stmt', 'stmth', 'stmt', 'envh',
            '[\"Mathlib.Tactic.Ring\",\"Mathlib.Tactic.NormNum\"]', 'hash',
            'unreviewed', 'none', NULL, NULL, 'CREATED', '2026-01-01T00:00:00Z'
        )",
        [],
    )?;

    // An episode reaching 'kernel_verified' — the exact outcome value missing
    // from the legacy CHECK — must also now be insertable.
    conn.execute(
        "INSERT INTO episodes (
            id, problem_version_id, state, current_revision, step_count,
            invalid_action_count, outcome, termination_reason, created_at
        ) VALUES ('ep-2', 'pv-new', 'terminated', 1, 1, 0, 'kernel_verified', 'root_kernel_verified', '2026-01-01T00:00:00Z')",
        [],
    )?;

    // A second startup against the already-migrated database must be a no-op,
    // not an error (rebuilding an already-current table would be wasteful but
    // must not be destructive or fail).
    db::initialize_db(&conn)?;
    let row_count: i64 = conn.query_row("SELECT COUNT(*) FROM problem_versions", [], |row| row.get(0))?;
    assert_eq!(row_count, 3, "second startup must not duplicate or lose rows");

    Ok(())
}

/// A fresh database must come up with the current CHECK constraints directly
/// from CREATE TABLE — the migration path must not interfere, and both
/// vocabularies must be usable immediately.
#[test]
fn test_fresh_database_accepts_current_fidelity_vocabulary() -> rusqlite::Result<()> {
    let conn = Connection::open_in_memory().unwrap();
    db::initialize_db(&conn)?;

    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES ('pv-1', 's', 'sh', '{}', 'r', 'rh', 'r', 'eh', 'unreviewed', 'none', NULL, NULL, 'CREATED', '2026-01-01T00:00:00Z')",
        [],
    )?;
    Ok(())
}
