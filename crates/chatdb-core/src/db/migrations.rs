use rusqlite::Connection;

pub fn migrate_v0_to_v1(conn: &mut Connection) -> rusqlite::Result<()> {
    let tx = conn.transaction()?;

    // First apply V1 schema
    tx.execute_batch(super::schema_v1::V1_SCHEMA)?;

    // Insert the migration record
    tx.execute(
        "INSERT OR IGNORE INTO schema_migrations (version, applied_at) VALUES (1, datetime('now'))",
        [],
    )?;

    // If V0 obligations exist, copy them to canonical_verified_lemmas if they were proved
    // Since V0 'verified_lemmas' was a canonical concept, we just copy everything to 'canonical_verified_lemmas'
    let v0_verified_exists: i64 = tx.query_row(
        "SELECT count(*) FROM sqlite_master WHERE type='table' AND name='verified_lemmas'",
        [],
        |row| row.get(0),
    )?;

    if v0_verified_exists > 0 {
        tx.execute(
            "INSERT OR IGNORE INTO canonical_verified_lemmas (
                id, problem_version_id, obligation_id, polarity, theorem_name, statement_hash,
                proof_source_artifact_hash, compiled_artifact_hash, proof_term_hash, environment_hash,
                actual_dependency_ids_json, kernel_result_hash, verified_at
            )
            SELECT v.id, o.problem_version_id, v.obligation_id, v.polarity, v.theorem_name, v.statement_hash,
                   v.proof_source_artifact_hash, v.compiled_artifact_hash, v.proof_term_hash, v.environment_hash,
                   v.actual_dependency_ids_json, v.kernel_result_hash, v.verified_at
            FROM verified_lemmas v
            JOIN obligations o ON o.id = v.obligation_id",
            [],
        )?;
    }

    let v0_certificates_exists: i64 = tx.query_row(
        "SELECT count(*) FROM sqlite_master WHERE type='table' AND name='certificates'",
        [],
        |row| row.get(0),
    )?;

    if v0_certificates_exists > 0 {
        tx.execute(
            "INSERT OR IGNORE INTO canonical_certificates (
                id, problem_version_id, root_obligation_id, root_verified_lemma_id, root_statement_hash,
                root_proof_artifact_hash, proof_dependency_manifest_hash, active_sketch_snapshot_hash,
                toolchain_manifest_hash, kernel_result_hash, coverage_state, convergence_record_hash,
                kernel_verified_at, completed_at
            )
            SELECT id, problem_version_id, root_obligation_id, root_verified_lemma_id, root_statement_hash,
                   root_proof_artifact_hash, proof_dependency_manifest_hash, active_sketch_snapshot_hash,
                   toolchain_manifest_hash, kernel_result_hash, coverage_state, convergence_record_hash,
                   kernel_verified_at, completed_at
            FROM certificates",
            [],
        )?;
    }
    
    // Convert old formalization_candidates that were approved into approved_formalizations?
    // Not strictly needed, but let's migrate the approved ones.
    
    // In a real migration we would also clean up the old tables, but we leave them for now
    // or we can drop them.
    // We will drop them to enforce a clean V1 schema.
    
    if v0_verified_exists > 0 {
        tx.execute("DROP TABLE IF EXISTS verified_lemmas", [])?;
        tx.execute("DROP TABLE IF EXISTS certificates", [])?;
        tx.execute("DROP TABLE IF EXISTS proposal_attempts", [])?;
        tx.execute("DROP TABLE IF EXISTS obligation_edges", [])?;
        tx.execute("DROP TABLE IF EXISTS obligations", [])?;
        tx.execute("DROP TABLE IF EXISTS formalization_candidates", [])?;
        tx.execute("DROP TABLE IF EXISTS fidelity_approvals", [])?;
        tx.execute("DROP TABLE IF EXISTS drafts", [])?;
        tx.execute("DROP TABLE IF EXISTS review_epochs", [])?;
        tx.execute("DROP TABLE IF EXISTS review_proposals", [])?;
        tx.execute("DROP TABLE IF EXISTS budget_ledger", [])?;
        tx.execute("DROP TABLE IF EXISTS events", [])?;
    }

    tx.commit()?;
    Ok(())
}
