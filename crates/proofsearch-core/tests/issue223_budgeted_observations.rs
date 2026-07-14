//! Issue #223: budgeted observations with priorities and continuation tokens.
//!
//! End-to-end coverage that `CONTEXT_TOO_LARGE` is no longer a failure mode and
//! that omitted material is explicitly referenced and retrievable via the
//! deterministic pagination API (`CompactContextBuilder::expand_observation_field`).
//!
//!  - large root, real production path (advance -> build_episode -> observation_json):
//!      test_huge_root_is_referenced_and_pageable
//!  - large diagnostic under an exhausted budget keeps a head + references the rest,
//!    and pages back to the exact original:
//!      test_large_diagnostic_pages_back_to_original

use chrono::Utc;
use rusqlite::Connection;
use uuid::Uuid;

use proofsearch_core::db;
use proofsearch_core::orchestrator::context::{
    CompactContext, CompactContextBuilder, ObservationField, DIAGNOSTIC_HEAD_BYTES,
};
use proofsearch_core::orchestrator::lifecycle::advance;

fn setup_db() -> Connection {
    let conn = Connection::open_in_memory().unwrap();
    db::initialize_db(&conn).unwrap();
    conn
}

fn seed_problem_version(conn: &Connection, root_formal_statement: &str) -> Uuid {
    let id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO problem_versions (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, fidelity_status, fidelity_method, state, created_at
        ) VALUES (?1, 'src', 'srch', '{}', ?2, 'rooth', 'render', 'envh', 'unreviewed', 'manual', 'CREATED', ?3)",
        (id.to_string(), root_formal_statement, Utc::now().to_rfc3339()),
    )
    .unwrap();
    id
}

fn seed_episode(conn: &Connection, problem_version_id: Uuid) -> Uuid {
    let id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO episodes (id, problem_version_id, state, created_at)
         VALUES (?1, ?2, 'awaiting_external_action', ?3)",
        (
            id.to_string(),
            problem_version_id.to_string(),
            Utc::now().to_rfc3339(),
        ),
    )
    .unwrap();
    id
}

fn seed_obligation(conn: &Connection, episode_id: Uuid, problem_version_id: Uuid) -> Uuid {
    let id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO episode_obligations (
            id, episode_id, problem_version_id, kind, theorem_name, lean_statement, statement_hash,
            natural_description, status, depth_from_root, created_by, created_at
        ) VALUES (?1, ?2, ?3, 'root', 'root_theorem', 'True', 'stmth', 'the obligation', 'open', 0, 'initial_sketch', ?4)",
        (id.to_string(), episode_id.to_string(), problem_version_id.to_string(), Utc::now().to_rfc3339()),
    )
    .unwrap();
    id
}

/// Reassemble a full field by paging `expand_observation_field` in fixed chunks,
/// verifying termination (`next_offset == None`) and stable content hash.
fn page_full_field(
    builder: &CompactContextBuilder,
    conn: &Connection,
    episode_id: Uuid,
    obligation_id: Uuid,
    field: ObservationField,
    chunk: usize,
) -> (String, String) {
    let first = builder
        .expand_observation_field(conn, episode_id, obligation_id, field, 0, chunk)
        .unwrap();
    let hash = first.content_hash.clone();
    let mut acc = first.bytes;
    let mut next = first.next_offset;
    let mut prev = 0usize;
    while let Some(offset) = next {
        assert!(offset > prev, "pagination must advance");
        prev = offset;
        let page = builder
            .expand_observation_field(conn, episode_id, obligation_id, field, offset, chunk)
            .unwrap();
        assert_eq!(
            page.content_hash, hash,
            "content hash must be stable across pages"
        );
        acc.push_str(&page.bytes);
        next = page.next_offset;
    }
    (acc, hash)
}

#[test]
fn test_huge_root_is_referenced_and_pageable() {
    let mut conn = setup_db();
    // A root statement far larger than the default 16 KB byte budget.
    let huge_root = format!("theorem big : {}", "x".repeat(50_000));
    let pv = seed_problem_version(&conn, &huge_root);
    let episode = seed_episode(&conn, pv);

    // Real production path: advance() seeds the root obligation and generates
    // the action_request whose observation_json is the budgeted observation.
    let tx = conn.transaction().unwrap();
    let req_id = advance(&tx, episode)
        .unwrap()
        .expect("advance should create a request");
    let observation_json: String = tx
        .query_row(
            "SELECT observation_json FROM action_requests WHERE id = ?1",
            [req_id.to_string()],
            |row| row.get(0),
        )
        .unwrap();
    let obligation_id: String = tx
        .query_row(
            "SELECT id FROM episode_obligations WHERE episode_id = ?1 AND theorem_name = 'root_theorem'",
            [episode.to_string()],
            |row| row.get(0),
        )
        .unwrap();
    tx.commit().unwrap();

    // The observation was produced without CONTEXT_TOO_LARGE, and the oversized
    // root is referenced rather than silently dropped.
    let ctx: CompactContext = serde_json::from_str(&observation_json).unwrap();
    let root_ref = ctx
        .references
        .iter()
        .find(|r| r.field == ObservationField::RootTheorem)
        .expect("oversized root must be referenced");
    assert_eq!(root_ref.total_bytes, huge_root.len());
    assert!(ctx.budget.truncated);
    assert!(ctx.budget.referenced_bytes >= root_ref.total_bytes);

    // The full root is retrievable through pagination and reassembles byte-exact.
    let obligation_id = Uuid::parse_str(&obligation_id).unwrap();
    let builder = CompactContextBuilder::new(4000);
    let one_shot = builder
        .expand_observation_field(
            &conn,
            episode,
            obligation_id,
            ObservationField::RootTheorem,
            0,
            0,
        )
        .unwrap();
    assert_eq!(one_shot.bytes, huge_root);
    assert_eq!(one_shot.total_bytes, huge_root.len());
    assert_eq!(one_shot.next_offset, None);
    assert_eq!(one_shot.content_hash, root_ref.content_hash);

    let (paged, paged_hash) = page_full_field(
        &builder,
        &conn,
        episode,
        obligation_id,
        ObservationField::RootTheorem,
        4096,
    );
    assert_eq!(paged, huge_root);
    assert_eq!(paged_hash, root_ref.content_hash);
}

#[test]
fn test_large_diagnostic_pages_back_to_original() {
    let conn = setup_db();
    let pv = seed_problem_version(&conn, "theorem root : True");
    let episode = seed_episode(&conn, pv);
    let obligation = seed_obligation(&conn, episode, pv);

    // A rejected attempt with a large diagnostic blob.
    let big_diag = format!("{{\"messages\":\"{}\"}}", "e".repeat(8_000));
    let req_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO action_requests (
            id, episode_id, problem_version_id, episode_revision, request_sequence_number,
            role, target_obligation_id, status, created_at
        ) VALUES (?1, ?2, ?3, 0, 1, 'prover', ?4, 'fulfilled', ?5)",
        (
            req_id.to_string(),
            episode.to_string(),
            pv.to_string(),
            obligation.to_string(),
            Utc::now().to_rfc3339(),
        ),
    )
    .unwrap();
    let attempt_id = Uuid::new_v4();
    conn.execute(
        "INSERT INTO action_attempts (
            id, episode_id, action_request_id, idempotency_key, expected_revision, claim_token,
            status, claimed_at, execution_completed_at, lean_result_json
        ) VALUES (?1, ?2, ?3, ?4, 0, ?5, 'rejected', ?6, ?6, ?7)",
        (
            attempt_id.to_string(),
            episode.to_string(),
            req_id.to_string(),
            Uuid::new_v4().to_string(),
            Uuid::new_v4().to_string(),
            Utc::now().to_rfc3339(),
            &big_diag,
        ),
    )
    .unwrap();

    // Tiny byte budget forces the diagnostic down to its guaranteed head.
    let builder = CompactContextBuilder::with_bytes_per_token(4, 4); // 16-byte ceiling
    let ctx = builder
        .build_episode(
            &conn,
            episode,
            obligation,
            "envh",
            "manh",
            "theorem root : True",
        )
        .unwrap();

    let head = ctx
        .latest_diagnostic
        .as_ref()
        .expect("diagnostic head always present");
    assert_eq!(head.len(), DIAGNOSTIC_HEAD_BYTES);
    let diag_ref = ctx
        .references
        .iter()
        .find(|r| r.field == ObservationField::Diagnostics)
        .expect("truncated diagnostic must be referenced");
    assert_eq!(diag_ref.total_bytes, big_diag.len());
    assert_eq!(diag_ref.included_bytes, DIAGNOSTIC_HEAD_BYTES);
    assert_eq!(diag_ref.next_offset, DIAGNOSTIC_HEAD_BYTES);

    // The head plus the paged remainder reconstructs the exact original blob.
    let (paged, paged_hash) = page_full_field(
        &builder,
        &conn,
        episode,
        obligation,
        ObservationField::Diagnostics,
        1024,
    );
    assert_eq!(paged, big_diag);
    assert_eq!(paged_hash, diag_ref.content_hash);

    // And the inlined head is a true prefix of the paged full content.
    assert!(paged.starts_with(head.as_str()));
}
