use rusqlite::Connection;
use serde_json;

pub const V1_SCHEMA: &str = r#"
-- Canonical Tables
CREATE TABLE IF NOT EXISTS schema_migrations (
    version INTEGER PRIMARY KEY,
    applied_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS problem_versions (
    id TEXT PRIMARY KEY,
    source_problem_text TEXT NOT NULL,
    source_problem_hash TEXT NOT NULL,
    source_metadata_json TEXT NOT NULL,
    root_formal_statement TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    normalized_root_rendering TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    -- Immutable per problem_version: the exact Lean import closure the verifier
    -- compiles candidate proofs against. An 'unknown identifier' failure only
    -- ever establishes that a name didn't resolve under THIS manifest — never
    -- that it's absent from the pinned library. See lean_declaration_lookup and
    -- docs/fix_plan_playtest_03.md. Defaults preserve the pre-manifest behavior
    -- (Ring + NormNum) for rows/fixtures that predate this column.
    import_manifest_json TEXT NOT NULL DEFAULT '["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum"]',
    import_manifest_hash TEXT NOT NULL DEFAULT '',
    fidelity_status TEXT NOT NULL,
    fidelity_method TEXT NOT NULL,
    fidelity_approval_id TEXT,
    root_obligation_id TEXT,
    state TEXT NOT NULL,
    created_at TEXT NOT NULL,
    -- 'attested' (an honest, explicitly-named dev bypass — see problem_create's
    -- unsafe_dev_attestation) may enter proving, but only a real
    -- problem_submit_fidelity_review decision can reach 'verified', and only
    -- 'verified' may reach COMPLETE. This is the DB-level backstop for the
    -- proof-soundness-vs-statement-fidelity invariant; see docs/fix_plan_playtest_02.md.
    CHECK(state NOT IN ('PROVING', 'ROOT_PROVED_COVERAGE_PENDING', 'ROOT_PROVED_COVERAGE_UNCONVERGED') OR fidelity_status IN ('verified', 'attested')),
    CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified'),
    CHECK(fidelity_status IN ('unreviewed', 'attested', 'verified', 'rejected', 'revoked'))
);

-- Fidelity belongs to the problem version, not to any one proof episode: an
-- immutable record of who/what decided the formal statement represents the
-- source problem, bound to the exact hashes reviewed so a later edit can never
-- silently inherit an old approval.
CREATE TABLE IF NOT EXISTS problem_fidelity_reviews (
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

CREATE TABLE IF NOT EXISTS canonical_verified_lemmas (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
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
    verified_at TEXT NOT NULL,
    CHECK(polarity IN ('positive', 'negative'))
);

CREATE TABLE IF NOT EXISTS canonical_certificates (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    root_obligation_id TEXT NOT NULL,
    root_verified_lemma_id TEXT NOT NULL REFERENCES canonical_verified_lemmas(id),
    root_statement_hash TEXT NOT NULL,
    root_proof_artifact_hash TEXT NOT NULL,
    proof_dependency_manifest_hash TEXT NOT NULL,
    active_sketch_snapshot_hash TEXT NOT NULL,
    toolchain_manifest_hash TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    coverage_state TEXT NOT NULL,
    convergence_record_hash TEXT,
    kernel_verified_at TEXT NOT NULL,
    completed_at TEXT,
    CHECK(coverage_state IN ('pending', 'converged', 'unconverged', 'integrity_blocked'))
);

CREATE TABLE IF NOT EXISTS approved_formalizations (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    lean_statement TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    normalized_rendering TEXT NOT NULL,
    quantifiers_json TEXT NOT NULL,
    hypotheses_json TEXT NOT NULL,
    domain_restrictions_json TEXT NOT NULL,
    origin_type TEXT NOT NULL,
    origin_config_hash TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(problem_version_id, statement_hash)
);

-- Episode-Local Tables
CREATE TABLE IF NOT EXISTS episodes (
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
    -- 'kernel_verified': the root obligation passed the Lean kernel but the
    -- problem's statement fidelity is not (yet) 'verified' — proof soundness
    -- without statement fidelity. Distinct from 'certified', which requires both.
    -- Never treat 'kernel_verified' as a synonym for 'certified' downstream.
    CHECK(outcome IN ('certified', 'kernel_verified', 'refuted', 'gave_up', 'timeout', 'budget_exhausted', 'model_error', 'infrastructure_error') OR outcome IS NULL),
    CHECK((state = 'terminated' AND outcome IS NOT NULL AND termination_reason IS NOT NULL) OR state <> 'terminated'),
    CHECK((state = 'truncated' AND outcome IS NOT NULL AND truncation_reason IS NOT NULL) OR state <> 'truncated'),
    CHECK(NOT (state = 'terminated' AND truncation_reason IS NOT NULL)),
    CHECK(NOT (state = 'truncated' AND termination_reason IS NOT NULL))
);

CREATE TABLE IF NOT EXISTS episode_obligations (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    kind TEXT NOT NULL,
    theorem_name TEXT NOT NULL,
    lean_statement TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    natural_description TEXT NOT NULL,
    status TEXT NOT NULL,
    depth_from_root INTEGER NOT NULL,
    created_by TEXT NOT NULL,
    created_by_epoch_id TEXT,
    superseded_by_id TEXT REFERENCES episode_obligations(id),
    proved_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    refutation_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    failure_lesson TEXT,
    attempt_count INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL,
    closed_at TEXT,
    UNIQUE(episode_id, theorem_name),
    CHECK(status IN ('open', 'in_progress', 'proved', 'refuted', 'superseded', 'abandoned', 'blocked_needs_human')),
    CHECK(kind IN ('root', 'proof', 'coverage', 'counterexample')),
    CHECK(created_by IN ('initial_sketch', 'decomposition', 'reviewer', 'human')),
    CHECK(
      (status = 'proved' AND proved_lemma_id IS NOT NULL AND refutation_lemma_id IS NULL) OR
      (status = 'refuted' AND refutation_lemma_id IS NOT NULL AND proved_lemma_id IS NULL) OR
      (status NOT IN ('proved', 'refuted') AND proved_lemma_id IS NULL AND refutation_lemma_id IS NULL)
    )
);

CREATE TABLE IF NOT EXISTS episode_obligation_edges (
    parent_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    dependency_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    edge_kind TEXT NOT NULL,
    case_group TEXT,
    created_at TEXT NOT NULL,
    PRIMARY KEY(parent_obligation_id, dependency_obligation_id),
    CHECK(parent_obligation_id <> dependency_obligation_id),
    CHECK(edge_kind IN ('lemma', 'case_branch', 'witness', 'reduction'))
);

CREATE TABLE IF NOT EXISTS episode_proposal_attempts (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    role TEXT NOT NULL,
    model_config_hash TEXT,
    prompt_hash TEXT NOT NULL,
    context_manifest_hash TEXT NOT NULL,
    candidate_source_artifact_hash TEXT,
    diagnostic_json TEXT,
    outcome TEXT NOT NULL,
    input_tokens INTEGER NOT NULL,
    output_tokens INTEGER NOT NULL,
    cost_usd_micros INTEGER NOT NULL,
    wall_time_ms INTEGER NOT NULL,
    lean_cpu_time_ms INTEGER NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(outcome IN ('kernel_pass', 'kernel_fail', 'preflight_reject', 'model_invalid_output', 'infrastructure_error', 'budget_denied', 'timeout', 'cancelled'))
);

CREATE TABLE IF NOT EXISTS episode_verified_lemmas (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    polarity TEXT NOT NULL,
    theorem_name TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    proof_source_artifact_hash TEXT NOT NULL,
    compiled_artifact_hash TEXT NOT NULL,
    proof_term_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    actual_dependency_ids_json TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    verified_at TEXT NOT NULL,
    UNIQUE(obligation_id, polarity),
    CHECK(polarity IN ('positive', 'negative'))
);

-- A verified module submission (defs + helper theorems + root theorem checked
-- as one unit — see docs/submit_module.md). One row per successful SubmitModule.
-- Episode-local, like episode_verified_lemmas: canonical/promotion equivalents
-- can come later, but the verified development must be remembered as a
-- structured, replayable artifact NOW so module solves become training data,
-- not just a compiled side effect. module_items_json holds the exact structured
-- items + root theorem, so the precise Lean source re-assembles deterministically
-- (its hash must equal module_source_hash).
CREATE TABLE IF NOT EXISTS episode_verified_modules (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    root_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    root_statement_hash TEXT NOT NULL,
    import_manifest_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    module_source_hash TEXT NOT NULL,
    module_items_json TEXT NOT NULL,
    declaration_manifest_hash TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    verified_at TEXT NOT NULL,
    UNIQUE(episode_id, root_obligation_id, module_source_hash)
);

-- One row per declaration in a verified module, in dependency (assembly) order.
-- item_kind is 'def' | 'theorem' | 'root_theorem'; the single root_theorem row
-- is explicitly linked to the root obligation via its parent module row.
CREATE TABLE IF NOT EXISTS episode_verified_module_items (
    id TEXT PRIMARY KEY,
    module_id TEXT NOT NULL REFERENCES episode_verified_modules(id),
    item_order INTEGER NOT NULL,
    item_kind TEXT NOT NULL,
    lean_name TEXT NOT NULL,
    statement_or_type_hash TEXT NOT NULL,
    body_hash TEXT NOT NULL,
    depends_on_json TEXT NOT NULL,
    policy_result_json TEXT NOT NULL,
    UNIQUE(module_id, item_order),
    CHECK(item_kind IN ('def', 'theorem', 'root_theorem'))
);

CREATE TABLE IF NOT EXISTS episode_budget_ledger (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    obligation_id TEXT REFERENCES episode_obligations(id),
    call_kind TEXT NOT NULL,
    reservation_id TEXT NOT NULL,
    state TEXT NOT NULL,
    reserved_input_tokens INTEGER NOT NULL,
    reserved_output_tokens INTEGER NOT NULL,
    actual_input_tokens INTEGER,
    actual_output_tokens INTEGER,
    reserved_cost_usd_micros INTEGER NOT NULL,
    actual_cost_usd_micros INTEGER,
    reserved_wall_time_ms INTEGER NOT NULL,
    actual_wall_time_ms INTEGER,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS episode_review_epochs (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    epoch_number INTEGER NOT NULL,
    trigger TEXT NOT NULL,
    eligible BOOLEAN NOT NULL,
    reviewer_count INTEGER NOT NULL,
    diverse_family_count INTEGER NOT NULL,
    lens_count INTEGER NOT NULL,
    admitted_count INTEGER NOT NULL,
    surviving_count INTEGER,
    surviving_rate REAL,
    ema_rate REAL,
    created_at TEXT NOT NULL,
    completed_at TEXT,
    UNIQUE(episode_id, epoch_number)
);

CREATE TABLE IF NOT EXISTS episode_review_proposals (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    epoch_id TEXT NOT NULL REFERENCES episode_review_epochs(id),
    reviewer_config_hash TEXT NOT NULL,
    lens TEXT NOT NULL,
    natural_description TEXT NOT NULL,
    proposed_lean_statement TEXT NOT NULL,
    proposed_statement_hash TEXT NOT NULL,
    proposed_dependencies_json TEXT NOT NULL,
    proposal_kind TEXT NOT NULL,
    admission_outcome TEXT,
    admitted_obligation_id TEXT REFERENCES episode_obligations(id),
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS episode_certificate_candidates (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    root_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    root_verified_lemma_id TEXT NOT NULL REFERENCES episode_verified_lemmas(id),
    root_statement_hash TEXT NOT NULL,
    root_proof_artifact_hash TEXT NOT NULL,
    proof_dependency_manifest_hash TEXT NOT NULL,
    active_sketch_snapshot_hash TEXT NOT NULL,
    toolchain_manifest_hash TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    coverage_state TEXT NOT NULL,
    convergence_record_hash TEXT,
    kernel_verified_at TEXT NOT NULL,
    completed_at TEXT,
    CHECK(coverage_state IN ('pending', 'converged', 'unconverged', 'integrity_blocked'))
);

CREATE TABLE IF NOT EXISTS episode_drafts (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    model_config_hash TEXT NOT NULL,
    prompt_template_hash TEXT NOT NULL,
    content_artifact_hash TEXT NOT NULL,
    extracted_moves_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS episode_formalization_candidates (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    lean_statement TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    normalized_rendering TEXT NOT NULL,
    quantifiers_json TEXT NOT NULL,
    hypotheses_json TEXT NOT NULL,
    domain_restrictions_json TEXT NOT NULL,
    origin_type TEXT NOT NULL,
    origin_config_hash TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(episode_id, statement_hash)
);

CREATE TABLE IF NOT EXISTS episode_fidelity_reviews (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    source_problem_hash TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    rendering_hash TEXT NOT NULL,
    approval_method TEXT NOT NULL,
    approver_id TEXT NOT NULL,
    signature TEXT,
    notes TEXT,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS action_requests (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    episode_revision INTEGER NOT NULL,
    request_sequence_number INTEGER NOT NULL,
    role TEXT NOT NULL,
    action_schema_id TEXT,
    action_schema_version TEXT,
    environment_version TEXT,
    target_obligation_id TEXT REFERENCES episode_obligations(id),
    observation_json TEXT,
    observation_hash TEXT,
    state_hash_before TEXT,
    expected_response_type TEXT,
    allowed_action_variants_json TEXT,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    expiration_at TEXT,
    claimed_at TEXT,
    fulfilled_at TEXT,
    fulfilled_attempt_id TEXT,
    superseding_request_id TEXT,
    cancellation_reason TEXT,
    CHECK(status IN ('pending', 'claimed', 'fulfilled', 'expired', 'cancelled'))
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_active_request_per_revision
ON action_requests(episode_id, episode_revision)
WHERE status IN ('pending', 'claimed');

CREATE TABLE IF NOT EXISTS action_attempts (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    action_request_id TEXT NOT NULL REFERENCES action_requests(id),
    idempotency_key TEXT NOT NULL,
    expected_revision INTEGER NOT NULL,
    claim_token TEXT NOT NULL,
    submitted_action_json TEXT,
    raw_external_response BLOB,
    raw_external_response_content_type TEXT,
    raw_external_response_encoding TEXT,
    raw_external_response_byte_length INTEGER,
    raw_external_response_sha256 TEXT,
    status TEXT NOT NULL,
    claimed_at TEXT NOT NULL,
    claim_expiration TEXT,
    execution_started_at TEXT,
    execution_completed_at TEXT,
    preflight_result_json TEXT,
    lean_invocation_id TEXT,
    lean_result_json TEXT,
    commit_result_json TEXT,
    failure_reason TEXT,
    CHECK(status IN ('claimed', 'preflight_rejected', 'executing', 'verified', 'rejected', 'committed', 'abandoned', 'expired', 'infrastructure_failed'))
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_attempt_idempotency
ON action_attempts(episode_id, idempotency_key);

-- Partial index for active attempts
CREATE UNIQUE INDEX IF NOT EXISTS idx_one_active_attempt_per_request
ON action_attempts(action_request_id)
WHERE status IN ('claimed', 'executing', 'verified');

CREATE TABLE IF NOT EXISTS model_call_leases (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    action_attempt_id TEXT NOT NULL REFERENCES action_attempts(id),
    model_descriptor_json TEXT NOT NULL,
    reserved_cost_micros INTEGER NOT NULL,
    actual_cost_micros INTEGER,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    settled_at TEXT,
    CHECK(status IN ('reserved', 'settled', 'voided'))
);

CREATE TABLE IF NOT EXISTS trajectory_events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    event_sequence_number INTEGER NOT NULL,
    event_type TEXT NOT NULL,
    event_hash TEXT NOT NULL,
    previous_event_hash TEXT NOT NULL,
    state_hash_before TEXT NOT NULL,
    state_hash_after TEXT NOT NULL,
    lean_environment_hash TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    payload_hash TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(episode_id, event_sequence_number),
    UNIQUE(episode_id, event_hash)
);
"#;

pub fn initialize_v1_db(conn: &Connection) -> rusqlite::Result<()> {
    // Foreign keys stay OFF for the whole init sequence: the constraint-vocabulary
    // migrations below drop and recreate tables that other tables reference (e.g.
    // problem_fidelity_reviews -> problem_versions, episode_obligations ->
    // episodes), which foreign-key enforcement would otherwise block. Turned back
    // on at the end so normal operation still enforces them.
    conn.execute("PRAGMA foreign_keys = OFF;", [])?;
    // Must run BEFORE the CREATE TABLE IF NOT EXISTS batch below: that statement
    // is a no-op on a `problem_versions` table that already exists (from a
    // pre-v0.2.3 database), so a DB created before the import-manifest columns
    // existed would otherwise be left permanently missing them, and the first
    // query touching them would fail with "no such column".
    migrate_add_import_manifest_columns(conn)?;
    // CHECK constraints are baked into a table at creation and CREATE TABLE IF
    // NOT EXISTS cannot update them on a table that already exists — a database
    // that predates the fidelity-vocabulary rewrite (docs/fix_plan_playtest_02.md)
    // is otherwise left PERMANENTLY enforcing the old CHECK(fidelity_status IN
    // ('pending','approved','revoked')) / CHECK(outcome IN (...) — no
    // 'kernel_verified') constraints, silently rejecting every INSERT that uses
    // the current vocabulary. This is a harder failure than a missing column:
    // it's a deterministic, permanent rejection of the current code's writes,
    // not a one-time schema gap. See docs/fix_plan_playtest_05.md.
    migrate_fidelity_status_vocabulary(conn)?;
    migrate_episode_outcome_vocabulary(conn)?;
    conn.execute_batch(V1_SCHEMA)?;
    conn.execute("PRAGMA foreign_keys = ON;", [])?;
    Ok(())
}

/// Rebuilds `problem_versions` if it still carries the pre-fidelity-split CHECK
/// constraints (`fidelity_status IN ('pending','approved','revoked')`) — SQLite
/// has no `ALTER TABLE ... DROP CONSTRAINT`, so the only way to change a CHECK
/// is the standard create-copy-drop-rename sequence. No-op on a fresh database
/// or an already-migrated one (detected by checking whether the stored table
/// SQL already mentions the current vocabulary).
///
/// `'approved'` maps to `'verified'`, not `'attested'`: existing rows in state
/// `COMPLETE` already satisfy the (then-nonexistent) invariant "COMPLETE implies
/// verified" retroactively, and mapping to `'attested'` would make that INSERT
/// violate the current CHECK on the spot, failing the migration itself for any
/// database with a COMPLETE-state row.
fn migrate_fidelity_status_vocabulary(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='problem_versions'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let current_sql: String = conn.query_row(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name='problem_versions'",
        [],
        |row| row.get(0),
    )?;
    if current_sql.contains("'unreviewed'") {
        return Ok(());
    }

    conn.execute_batch(
        "CREATE TABLE problem_versions_migrating (
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
        INSERT INTO problem_versions_migrating (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, import_manifest_json, import_manifest_hash,
            fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        )
        SELECT
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, import_manifest_json, import_manifest_hash,
            CASE fidelity_status
                WHEN 'approved' THEN 'verified'
                WHEN 'pending' THEN 'unreviewed'
                WHEN 'revoked' THEN 'revoked'
                ELSE 'unreviewed'
            END,
            fidelity_method, fidelity_approval_id, root_obligation_id, state, created_at
        FROM problem_versions;
        DROP TABLE problem_versions;
        ALTER TABLE problem_versions_migrating RENAME TO problem_versions;",
    )?;
    Ok(())
}

/// Rebuilds `episodes` if it still carries the pre-fidelity-split CHECK on
/// `outcome` (missing `'kernel_verified'`) — same create-copy-drop-rename
/// technique as `migrate_fidelity_status_vocabulary`, and for the same reason:
/// a database that predates the fidelity split would otherwise reject every
/// episode reaching the `kernel_verified` outcome forever. The column set and
/// order are unchanged by this migration (only the CHECK differs), so this is
/// a straight `SELECT *` copy, unlike the `problem_versions` migration.
fn migrate_episode_outcome_vocabulary(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='episodes'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let current_sql: String = conn.query_row(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name='episodes'",
        [],
        |row| row.get(0),
    )?;
    if current_sql.contains("'kernel_verified'") {
        return Ok(());
    }

    conn.execute_batch(
        "CREATE TABLE episodes_migrating (
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
            CHECK(outcome IN ('certified', 'kernel_verified', 'refuted', 'gave_up', 'timeout', 'budget_exhausted', 'model_error', 'infrastructure_error') OR outcome IS NULL),
            CHECK((state = 'terminated' AND outcome IS NOT NULL AND termination_reason IS NOT NULL) OR state <> 'terminated'),
            CHECK((state = 'truncated' AND outcome IS NOT NULL AND truncation_reason IS NOT NULL) OR state <> 'truncated'),
            CHECK(NOT (state = 'terminated' AND truncation_reason IS NOT NULL)),
            CHECK(NOT (state = 'truncated' AND termination_reason IS NOT NULL))
        );
        INSERT INTO episodes_migrating SELECT * FROM episodes;
        DROP TABLE episodes;
        ALTER TABLE episodes_migrating RENAME TO episodes;",
    )?;
    Ok(())
}

/// Adds `import_manifest_json`/`import_manifest_hash` to a `problem_versions`
/// table that predates them (pre-v0.2.3 databases). No-op on a fresh database
/// (table doesn't exist yet — CREATE TABLE below brings it up to the current
/// shape with these columns already) and on an already-migrated one.
fn migrate_add_import_manifest_columns(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='problem_versions'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }

    let has_manifest_column = conn
        .prepare("PRAGMA table_info(problem_versions)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .any(|name| name == "import_manifest_json");
    if has_manifest_column {
        return Ok(());
    }

    let default_manifest: Vec<String> = vec!["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()];
    let default_manifest_json = serde_json::to_string(&default_manifest)
        .map_err(|e| rusqlite::Error::ToSqlConversionFailure(Box::new(e)))?;
    // Same value the base manifest constant hashes to at problem_create time —
    // pre-existing rows never had an explicit manifest, so this is the correct
    // (not merely default) backfill for what they were actually checked against.
    let default_manifest_hash = crate::hashing::canonical_hash(&default_manifest)
        .map_err(|e| rusqlite::Error::ToSqlConversionFailure(Box::new(std::io::Error::new(std::io::ErrorKind::Other, e))))?;

    conn.execute(
        &format!(
            "ALTER TABLE problem_versions ADD COLUMN import_manifest_json TEXT NOT NULL DEFAULT '{}'",
            default_manifest_json.replace('\'', "''")
        ),
        [],
    )?;
    conn.execute(
        "ALTER TABLE problem_versions ADD COLUMN import_manifest_hash TEXT NOT NULL DEFAULT ''",
        [],
    )?;
    conn.execute(
        "UPDATE problem_versions SET import_manifest_hash = ?1 WHERE import_manifest_hash = ''",
        [&default_manifest_hash],
    )?;
    Ok(())
}
