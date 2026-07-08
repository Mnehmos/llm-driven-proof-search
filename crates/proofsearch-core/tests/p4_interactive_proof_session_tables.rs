//! Migration/schema tests for issue #160: first-class persistence for
//! interactive (tactic-by-tactic) proof search, layered on top of #159's
//! `InteractiveProofGateway` trait and #162's canonical
//! `ProofStateObservation` / `ProofStateDiagnostic` model.
//!
//! Follows the `p0`/`p1`/`p2`/`p3` migration-test convention: exercise the
//! schema directly through `rusqlite` against a fresh
//! `db::initialize_db`-initialized in-memory database, the same way
//! `p3_benchmark_aligned_fidelity_migration.rs` does.
//!
//! Acceptance-criteria coverage, one test (or CHECK-constraint pair) per
//! bullet in issue #160:
//!  - insert a session                              -> test_insert_session
//!  - branches are non-destructive (two children)     -> test_branching_nodes_are_non_destructive
//!  - a failed tactic step remains visible             -> test_failed_tactic_step_remains_visible
//!  - close a session                                  -> test_close_session
//!  - a reconstructed script can exist unproved         -> test_reconstructed_script_without_verified_attempt
//!  - link to a verified attempt after the fact          -> test_link_reconstructed_script_to_verified_attempt_after_the_fact
//!  - trust-boundary CHECK constraints hold structurally -> test_trust_boundary_check_constraints

use chrono::Utc;
use rusqlite::Connection;
use uuid::Uuid;

use proofsearch_core::db;

// --- fixtures ---------------------------------------------------------

fn setup_db() -> Connection {
    let conn = Connection::open_in_memory().unwrap();
    db::initialize_db(&conn).unwrap();
    conn
}

fn seed_problem_version(conn: &Connection) -> Uuid {
    let id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, state, created_at
        ) VALUES (?1, 'src', 'srch', '{}', 'stmt', 'stmth', 'rendering', 'envh', 'unreviewed', 'manual', 'CREATED', ?2)",
        (id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();
    id
}

fn seed_episode(conn: &Connection, problem_version_id: Uuid) -> Uuid {
    let id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO episodes (
            id, problem_version_id, state, created_at
        ) VALUES (?1, ?2, 'awaiting_external_action', ?3)",
        (id.to_string(), problem_version_id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();
    id
}

fn seed_obligation(conn: &Connection, episode_id: Uuid, problem_version_id: Uuid, theorem_name: &str) -> Uuid {
    let id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO episode_obligations (
            id, episode_id, problem_version_id, kind, theorem_name, lean_statement, statement_hash,
            natural_description, status, depth_from_root, created_by, created_at
        ) VALUES (?1, ?2, ?3, 'root', ?4, 'theorem stmt', 'stmth', 'a test obligation', 'open', 0, 'initial_sketch', ?5)",
        (id.to_string(), episode_id.to_string(), problem_version_id.to_string(), theorem_name, Utc::now().to_rfc3339()),
    )
    .unwrap();
    id
}

/// Seeds an `action_requests` + `action_attempts` pair with `status =
/// 'verified'` — a real row from the EXISTING kernel-verification path that
/// `interactive_proof_reconstructed_scripts.verified_attempt_id` may later
/// point at.
fn seed_verified_action_attempt(conn: &Connection, episode_id: Uuid, problem_version_id: Uuid) -> Uuid {
    let request_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO action_requests (
            id, episode_id, problem_version_id, episode_revision, request_sequence_number,
            role, status, created_at
        ) VALUES (?1, ?2, ?3, 1, 1, 'prover', 'fulfilled', ?4)",
        (request_id.to_string(), episode_id.to_string(), problem_version_id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();

    let attempt_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO action_attempts (
            id, episode_id, action_request_id, idempotency_key, expected_revision, claim_token,
            status, claimed_at
        ) VALUES (?1, ?2, ?3, 'idem-1', 1, 'claim-token-1', 'verified', ?4)",
        (attempt_id.to_string(), episode_id.to_string(), request_id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();
    attempt_id
}

/// Inserts an `interactive_proof_sessions` row and returns its id. Mirrors
/// `InteractiveSessionStart`: a session always has a root node, so this also
/// inserts that root node and links `root_node_id` back onto the session --
/// the "create now, link later" two-step `problem_versions.root_obligation_id`
/// already uses elsewhere in this schema.
fn seed_session(conn: &Connection, episode_id: Uuid, problem_version_id: Uuid, obligation_id: Uuid) -> (Uuid, Uuid) {
    let session_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO interactive_proof_sessions (
            id, episode_id, problem_version_id, obligation_id, backend_kind, state, created_at
        ) VALUES (?1, ?2, ?3, ?4, 'mock', 'open', ?5)",
        (
            session_id.to_string(),
            episode_id.to_string(),
            problem_version_id.to_string(),
            obligation_id.to_string(),
            Utc::now().to_rfc3339(),
        ),
    )
    .unwrap();

    let root_node_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO interactive_proof_nodes (
            id, session_id, parent_node_id, depth, node_kind, proof_state_hash, goals_json,
            selected_goal_index, status, created_at
        ) VALUES (?1, ?2, NULL, 0, 'root', 'hash-root', '[{\"goal_index\":0,\"target\":{\"raw_rendering\":\"1 + 1 = 2\",\"pretty_rendering\":null},\"local_context\":null}]', 0, 'open', ?3)",
        (root_node_id.to_string(), session_id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();

    conn.execute(
        "UPDATE interactive_proof_sessions SET root_node_id = ?1 WHERE id = ?2",
        (root_node_id.to_string(), session_id.to_string()),
    )
    .unwrap();

    (session_id, root_node_id)
}

// --- tests --------------------------------------------------------------

/// A session can be inserted and links to the real episodes / problem_versions
/// / episode_obligations tables, not guessed FK targets.
#[test]
fn test_insert_session() {
    let conn = setup_db();
    let pv_id = seed_problem_version(&conn);
    let episode_id = seed_episode(&conn, pv_id);
    let obligation_id = seed_obligation(&conn, episode_id, pv_id, "test_thm");

    let (session_id, root_node_id) = seed_session(&conn, episode_id, pv_id, obligation_id);

    let (state, root, ep, pv, obl): (String, Option<String>, String, String, String) = conn
        .query_row(
            "SELECT state, root_node_id, episode_id, problem_version_id, obligation_id
             FROM interactive_proof_sessions WHERE id = ?1",
            [session_id.to_string()],
            |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?)),
        )
        .unwrap();

    assert_eq!(state, "open");
    assert_eq!(root, Some(root_node_id.to_string()));
    assert_eq!(ep, episode_id.to_string());
    assert_eq!(pv, pv_id.to_string());
    assert_eq!(obl, obligation_id.to_string());
}

/// Two tactics applied to the SAME parent node produce two sibling child
/// nodes, neither overwriting the other -- branches are non-destructive.
#[test]
fn test_branching_nodes_are_non_destructive() {
    let conn = setup_db();
    let pv_id = seed_problem_version(&conn);
    let episode_id = seed_episode(&conn, pv_id);
    let obligation_id = seed_obligation(&conn, episode_id, pv_id, "test_thm");
    let (session_id, root_node_id) = seed_session(&conn, episode_id, pv_id, obligation_id);

    let child_a = Uuid::new_v4();
    let child_b = Uuid::new_v4();
    for (child_id, tactic_hash) in [(child_a, "hash-tactic-a"), (child_b, "hash-tactic-b")] {
        conn.execute(
            "INSERT INTO interactive_proof_nodes (
                id, session_id, parent_node_id, depth, node_kind, proof_state_hash, goals_json,
                selected_goal_index, status, created_at
            ) VALUES (?1, ?2, ?3, 1, 'tactic_result', ?4, '[]', NULL, 'solved', ?5)",
            (child_id.to_string(), session_id.to_string(), root_node_id.to_string(), tactic_hash, Utc::now().to_rfc3339()),
        )
        .unwrap();

        conn.execute(
            "INSERT INTO interactive_proof_steps (
                id, session_id, parent_node_id, child_node_id, tactic_text_hash, outcome, created_at
            ) VALUES (?1, ?2, ?3, ?4, ?5, 'applied', ?6)",
            (
                Uuid::new_v4().to_string(),
                session_id.to_string(),
                root_node_id.to_string(),
                child_id.to_string(),
                tactic_hash,
                Utc::now().to_rfc3339(),
            ),
        )
        .unwrap();
    }

    // Both children survive as distinct rows under the same parent.
    let sibling_count: i64 = conn
        .query_row(
            "SELECT COUNT(*) FROM interactive_proof_nodes WHERE parent_node_id = ?1",
            [root_node_id.to_string()],
            |row| row.get(0),
        )
        .unwrap();
    assert_eq!(sibling_count, 2, "both branches must survive as distinct sibling nodes");

    let step_count: i64 = conn
        .query_row(
            "SELECT COUNT(*) FROM interactive_proof_steps WHERE parent_node_id = ?1",
            [root_node_id.to_string()],
            |row| row.get(0),
        )
        .unwrap();
    assert_eq!(step_count, 2, "both tactic-step edges must survive");

    // Neither child was overwritten by the other's insert.
    let ids: Vec<String> = {
        let mut stmt = conn
            .prepare("SELECT id FROM interactive_proof_nodes WHERE parent_node_id = ?1 ORDER BY id")
            .unwrap();
        let rows = stmt.query_map([root_node_id.to_string()], |row| row.get::<_, String>(0)).unwrap();
        rows.map(|r| r.unwrap()).collect()
    };
    let mut expected = vec![child_a.to_string(), child_b.to_string()];
    expected.sort();
    assert_eq!(ids, expected);
}

/// A failed tactic application is recorded as a normal, queryable step row
/// with `outcome = 'failed'` and a populated diagnostic -- never deleted or
/// hidden.
#[test]
fn test_failed_tactic_step_remains_visible() {
    let conn = setup_db();
    let pv_id = seed_problem_version(&conn);
    let episode_id = seed_episode(&conn, pv_id);
    let obligation_id = seed_obligation(&conn, episode_id, pv_id, "test_thm");
    let (session_id, root_node_id) = seed_session(&conn, episode_id, pv_id, obligation_id);

    let step_id = Uuid::new_v4();
    let diagnostic_json = r#"{"category":"tactic_failure","primary_message":"no goals remaining","source_span":null,"goal":null,"local_context":[],"unsolved_goals":[],"used_dependencies":[],"error_code":null,"canonical_goal_hash":null}"#;
    conn.execute(
        "INSERT INTO interactive_proof_steps (
            id, session_id, parent_node_id, child_node_id, tactic_text_hash, outcome,
            diagnostic_json, diagnostics_hash, created_at
        ) VALUES (?1, ?2, ?3, NULL, 'hash-bad-tactic', 'failed', ?4, 'hash-diag-1', ?5)",
        (step_id.to_string(), session_id.to_string(), root_node_id.to_string(), diagnostic_json, Utc::now().to_rfc3339()),
    )
    .unwrap();

    let (outcome, child, diag): (String, Option<String>, Option<String>) = conn
        .query_row(
            "SELECT outcome, child_node_id, diagnostic_json FROM interactive_proof_steps WHERE id = ?1",
            [step_id.to_string()],
            |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
        )
        .unwrap();
    assert_eq!(outcome, "failed");
    assert!(child.is_none());
    assert!(diag.is_some(), "failed step must still carry its diagnostic, not have it dropped");

    // Still queryable via the session's full step list, alongside any
    // successful steps -- nothing filters failed steps out structurally.
    let total: i64 = conn
        .query_row(
            "SELECT COUNT(*) FROM interactive_proof_steps WHERE session_id = ?1",
            [session_id.to_string()],
            |row| row.get(0),
        )
        .unwrap();
    assert_eq!(total, 1);
}

/// Closing a session sets state = 'closed' and closed_at, matching the
/// CHECK-enforced invariant that the two always move together.
#[test]
fn test_close_session() {
    let conn = setup_db();
    let pv_id = seed_problem_version(&conn);
    let episode_id = seed_episode(&conn, pv_id);
    let obligation_id = seed_obligation(&conn, episode_id, pv_id, "test_thm");
    let (session_id, _root_node_id) = seed_session(&conn, episode_id, pv_id, obligation_id);

    conn.execute(
        "UPDATE interactive_proof_sessions SET state = 'closed', closed_at = ?1 WHERE id = ?2",
        (Utc::now().to_rfc3339(), session_id.to_string()),
    )
    .unwrap();

    let (state, closed_at): (String, Option<String>) = conn
        .query_row(
            "SELECT state, closed_at FROM interactive_proof_sessions WHERE id = ?1",
            [session_id.to_string()],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )
        .unwrap();
    assert_eq!(state, "closed");
    assert!(closed_at.is_some());

    // Setting state = 'closed' WITHOUT closed_at must violate the CHECK.
    let session_id_2 = Uuid::new_v4();
    conn.execute(
        "INSERT INTO interactive_proof_sessions (
            id, episode_id, problem_version_id, obligation_id, backend_kind, state, created_at
        ) VALUES (?1, ?2, ?3, ?4, 'mock', 'open', ?5)",
        (
            session_id_2.to_string(),
            episode_id.to_string(),
            pv_id.to_string(),
            obligation_id.to_string(),
            Utc::now().to_rfc3339(),
        ),
    )
    .unwrap();
    let bad_close = conn.execute(
        "UPDATE interactive_proof_sessions SET state = 'closed' WHERE id = ?1",
        [session_id_2.to_string()],
    );
    assert!(bad_close.is_err(), "state='closed' without closed_at must violate the CHECK constraint");
}

/// A reconstructed script can be inserted with `verified_attempt_id = NULL`
/// (and `verification_outcome = NULL`): reconstruction alone never marks
/// anything proved.
#[test]
fn test_reconstructed_script_without_verified_attempt() {
    let conn = setup_db();
    let pv_id = seed_problem_version(&conn);
    let episode_id = seed_episode(&conn, pv_id);
    let obligation_id = seed_obligation(&conn, episode_id, pv_id, "test_thm");
    let (session_id, root_node_id) = seed_session(&conn, episode_id, pv_id, obligation_id);

    let script_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO interactive_proof_reconstructed_scripts (
            id, session_id, final_node_id, proof_format, proof_source_hash, reports_complete, created_at
        ) VALUES (?1, ?2, ?3, 'flat_tactic_sequence', 'hash-script-1', 1, ?4)",
        (script_id.to_string(), session_id.to_string(), root_node_id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();

    let (verified_attempt_id, verification_outcome): (Option<String>, Option<String>) = conn
        .query_row(
            "SELECT verified_attempt_id, verification_outcome FROM interactive_proof_reconstructed_scripts WHERE id = ?1",
            [script_id.to_string()],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )
        .unwrap();
    assert!(verified_attempt_id.is_none(), "reconstruction alone must not link a verified attempt");
    assert!(verification_outcome.is_none(), "reconstruction alone must not record a verification outcome");
}

/// A reconstructed script's `verified_attempt_id` / `verification_outcome`
/// can be populated AFTER creation, once the reconstructed proof is
/// resubmitted through the existing verifier -- proof authority only
/// attaches after the fact, never at creation.
#[test]
fn test_link_reconstructed_script_to_verified_attempt_after_the_fact() {
    let conn = setup_db();
    let pv_id = seed_problem_version(&conn);
    let episode_id = seed_episode(&conn, pv_id);
    let obligation_id = seed_obligation(&conn, episode_id, pv_id, "test_thm");
    let (session_id, root_node_id) = seed_session(&conn, episode_id, pv_id, obligation_id);

    let script_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO interactive_proof_reconstructed_scripts (
            id, session_id, final_node_id, proof_format, proof_source_hash, reports_complete, created_at
        ) VALUES (?1, ?2, ?3, 'flat_tactic_sequence', 'hash-script-2', 1, ?4)",
        (script_id.to_string(), session_id.to_string(), root_node_id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();

    // The reconstructed proof is resubmitted through the EXISTING
    // kernel-verification path (Solve/SubmitModule -> action_attempts),
    // unchanged by this migration, and comes back 'verified'.
    let attempt_id = seed_verified_action_attempt(&conn, episode_id, pv_id);

    conn.execute(
        "UPDATE interactive_proof_reconstructed_scripts
         SET verified_attempt_id = ?1, verification_outcome = 'verified'
         WHERE id = ?2",
        (attempt_id.to_string(), script_id.to_string()),
    )
    .unwrap();

    let (verified_attempt_id, verification_outcome): (Option<String>, Option<String>) = conn
        .query_row(
            "SELECT verified_attempt_id, verification_outcome FROM interactive_proof_reconstructed_scripts WHERE id = ?1",
            [script_id.to_string()],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )
        .unwrap();
    assert_eq!(verified_attempt_id.as_deref(), Some(attempt_id.to_string().as_str()));
    assert_eq!(verification_outcome.as_deref(), Some("verified"));

    // The obligation itself is untouched by this link -- interactive
    // evidence never directly proves an obligation.
    let obligation_status: String = conn
        .query_row(
            "SELECT status FROM episode_obligations WHERE id = ?1",
            [obligation_id.to_string()],
            |row| row.get(0),
        )
        .unwrap();
    assert_eq!(obligation_status, "open", "linking a reconstructed script must never itself change obligation status");
}

/// Structural trust-boundary guards: a `verification_outcome` can never be
/// recorded without a linked `verified_attempt_id`, and a step's
/// `diagnostic_json` presence must always match its `outcome`.
#[test]
fn test_trust_boundary_check_constraints() {
    let conn = setup_db();
    let pv_id = seed_problem_version(&conn);
    let episode_id = seed_episode(&conn, pv_id);
    let obligation_id = seed_obligation(&conn, episode_id, pv_id, "test_thm");
    let (session_id, root_node_id) = seed_session(&conn, episode_id, pv_id, obligation_id);

    // verification_outcome set without verified_attempt_id must fail.
    let script_id = Uuid::new_v4();
    let bad_script = conn.execute(
        "INSERT INTO interactive_proof_reconstructed_scripts (
            id, session_id, final_node_id, proof_format, proof_source_hash, verification_outcome, created_at
        ) VALUES (?1, ?2, ?3, 'flat_tactic_sequence', 'hash-script-3', 'verified', ?4)",
        (script_id.to_string(), session_id.to_string(), root_node_id.to_string(), Utc::now().to_rfc3339()),
    );
    assert!(bad_script.is_err(), "verification_outcome without verified_attempt_id must violate the CHECK constraint");

    // An 'applied' step with no child_node_id must fail.
    let bad_step = conn.execute(
        "INSERT INTO interactive_proof_steps (
            id, session_id, parent_node_id, child_node_id, tactic_text_hash, outcome, created_at
        ) VALUES (?1, ?2, ?3, NULL, 'hash-tactic', 'applied', ?4)",
        (Uuid::new_v4().to_string(), session_id.to_string(), root_node_id.to_string(), Utc::now().to_rfc3339()),
    );
    assert!(bad_step.is_err(), "an 'applied' step without a child_node_id must violate the CHECK constraint");

    // A 'failed' step with no diagnostic_json must fail.
    let bad_failed_step = conn.execute(
        "INSERT INTO interactive_proof_steps (
            id, session_id, parent_node_id, child_node_id, tactic_text_hash, outcome, created_at
        ) VALUES (?1, ?2, ?3, NULL, 'hash-tactic', 'failed', ?4)",
        (Uuid::new_v4().to_string(), session_id.to_string(), root_node_id.to_string(), Utc::now().to_rfc3339()),
    );
    assert!(bad_failed_step.is_err(), "a 'failed' step without diagnostic_json must violate the CHECK constraint");
}
