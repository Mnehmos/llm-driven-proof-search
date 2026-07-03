use rusqlite::Connection;

use chatdb_proof_core::db;
use chatdb_proof_core::hashing::canonical_hash;

/// A v0.2.2-shaped `problem_versions` table — everything the current schema
/// has, minus the two import-manifest columns added in v0.2.3.
const PRE_V0_2_3_PROBLEM_VERSIONS: &str = "
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
    created_at TEXT NOT NULL
);
";

/// A v0.2.2 database that already has a problem row must, on the first
/// v0.2.3+ startup, gain the import_manifest columns AND have that existing
/// row backfilled with the real base-manifest hash — not left with an empty
/// hash, which would make a supposedly content-addressed manifest look
/// unhashed. See docs/fix_plan_playtest_04.md.
#[test]
fn test_v0_2_2_database_gains_import_manifest_columns_on_startup() -> rusqlite::Result<()> {
    let conn = Connection::open_in_memory().unwrap();
    conn.execute_batch(PRE_V0_2_3_PROBLEM_VERSIONS)?;
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        ) VALUES (
            'p1', 'src', 'srch', '{}', 'stmt', 'stmth', 'stmt',
            'envh', 'unreviewed', 'none', NULL, NULL, 'CREATED', '2026-01-01T00:00:00Z'
        )",
        [],
    )?;

    // The actual startup path (chatdb-mcp's init_db calls exactly this).
    db::initialize_db(&conn)?;

    let (manifest_json, manifest_hash): (String, String) = conn.query_row(
        "SELECT import_manifest_json, import_manifest_hash FROM problem_versions WHERE id = 'p1'",
        [],
        |row| Ok((row.get(0)?, row.get(1)?)),
    )?;

    let manifest: Vec<String> = serde_json::from_str(&manifest_json).unwrap();
    assert_eq!(manifest, vec!["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()]);

    let expected_hash = canonical_hash(&manifest).unwrap();
    assert_eq!(manifest_hash, expected_hash, "pre-existing rows must get the REAL hash of what they were actually checked against, not an empty placeholder");
    assert!(!manifest_hash.is_empty());

    // A second startup against the already-migrated database must be a no-op,
    // not an error (ALTER TABLE ADD COLUMN on an existing column would fail).
    db::initialize_db(&conn)?;
    Ok(())
}

/// A fresh (no prior data) database must come up with the columns present
/// from CREATE TABLE directly — the migration path must not interfere.
#[test]
fn test_fresh_database_has_import_manifest_columns() -> rusqlite::Result<()> {
    let conn = Connection::open_in_memory().unwrap();
    db::initialize_db(&conn)?;

    let has_column = conn
        .prepare("PRAGMA table_info(problem_versions)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .any(|name| name == "import_manifest_json");
    assert!(has_column);
    Ok(())
}
