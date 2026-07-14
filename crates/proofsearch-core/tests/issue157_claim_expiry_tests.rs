//! Issue #157 regression tests — claim expiry under burst claim/step batches.
//!
//! Field signature being locked in: a burst of attempt_claims queued behind
//! slow (Lean-verifying) steps can outlive CLAIM_TTL_MINUTES; the expiry sweep
//! then recovers the tail claims, and the subsequent episode_steps failed with
//! a blanket "Invalid attempt claim or status" while re-observation showed the
//! episodes pending at revision 0 — misread as a write-durability race. The
//! fixes under test:
//!   1. step (prepare) revives an expired-but-untaken claim in place;
//!   2. finalize revives an expired-mid-gateway claim in place;
//!   3. a superseded claim fails with the precise ClaimSuperseded error, and a
//!      superseded FINALIZE refunds the budget reserved at prepare (leak);
//!   4. attempt_claim with the same idempotency_key revives its expired
//!      attempt (same attempt_id, same token) instead of dead-ending;
//!   5. the whole burst pattern: claim N, expire all, step all — all commit.

use proofsearch_core::orchestrator::{lifecycle, attempts, step};
use proofsearch_core::lean::LeanGateway;
use proofsearch_core::models::{Obligation, LeanVerificationOutcome, LeanVerificationResult, action::TypedAction, action::ProofFormat};
use rusqlite::{Connection, Transaction};
use uuid::Uuid;
use chrono::Utc;

struct MockGateway;
impl LeanGateway for MockGateway {
    fn verify_exact(
        &self,
        _obligation: &Obligation,
        _candidate_source: &str,
        _approved_dependency_ids: &[Uuid],
        _environment: &str,
        _import_manifest: &[String],
        _proof_format: ProofFormat,
    ) -> Result<LeanVerificationResult, String> {
        Ok(pass_result())
    }
}

fn pass_result() -> LeanVerificationResult {
    LeanVerificationResult {
        outcome: LeanVerificationOutcome::KernelPass,
        attempt_id: Uuid::new_v4(),
        obligation_id: Uuid::new_v4(),
        theorem_name: "".to_string(),
        expected_statement_hash: "".to_string(),
        elaborated_statement_hash: None,
        environment_hash: "".to_string(),
        proof_source_hash: "".to_string(),
        compiled_artifact_hash: None,
        proof_term_hash: None,
        diagnostic: None,
        all_diagnostics: vec![],
        dependency_use_report: None,
        resource_policy: None,
        output_receipt: None,
        durability_job: None,
        wall_time_ms: 10,
        lean_cpu_time_ms: 10,
    }
}

fn insert_test_problem(conn: &Connection) -> Uuid {
    let pv_id = Uuid::new_v4();
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
    pv_id
}

/// Backdate the claim so the next sweep recovers it, then run the sweep and
/// assert it actually flipped this attempt to 'expired' + its request to 'pending'.
fn force_expire(tx: &Transaction, attempt_id: Uuid) {
    tx.execute(
        "UPDATE action_attempts SET claim_expiration = ?1 WHERE id = ?2",
        ((Utc::now() - chrono::Duration::hours(1)).to_rfc3339(), attempt_id.to_string()),
    ).unwrap();
    let recovered = attempts::attempt_recover_expired(tx).unwrap();
    assert!(recovered >= 1, "sweep should have recovered the backdated claim");
    let status: String = tx.query_row(
        "SELECT status FROM action_attempts WHERE id = ?1",
        [attempt_id.to_string()], |row| row.get(0),
    ).unwrap();
    assert_eq!(status, "expired");
}

fn attempt_request_id(tx: &Transaction, attempt_id: Uuid) -> String {
    tx.query_row(
        "SELECT action_request_id FROM action_attempts WHERE id = ?1",
        [attempt_id.to_string()], |row| row.get(0),
    ).unwrap()
}

/// Fix 1: the exact issue-#157 client experience, single episode. The step
/// arrives after the sweep expired its claim; the request is untaken, so the
/// step must revive the claim and commit — no re-claim, no fresh key.
#[test]
fn expired_claim_revives_on_step_when_request_untaken() {
    let mut conn = Connection::open_in_memory().unwrap();
    proofsearch_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    let claim = attempts::attempt_claim(&tx, ep_id, req_id, "revive-on-step", 1)
        .unwrap().expect("claimable");
    force_expire(&tx, claim.attempt_id);

    // The queued step now arrives with the original (expired) claim.
    let outcome = step::attempt_commit(
        &tx, claim.attempt_id, 0, &claim.claim_token, &TypedAction::GiveUp, &MockGateway, 10,
    ).expect("step must revive the expired-but-untaken claim");
    assert!(matches!(outcome, LeanVerificationOutcome::KernelPass));

    let (att_status, req_status, revision): (String, String, i64) = tx.query_row(
        "SELECT a.status, r.status, e.current_revision
         FROM action_attempts a
         JOIN action_requests r ON r.id = a.action_request_id
         JOIN episodes e ON e.id = a.episode_id
         WHERE a.id = ?1",
        [claim.attempt_id.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).unwrap();
    assert_eq!(att_status, "committed");
    assert_eq!(req_status, "fulfilled");
    assert_eq!(revision, 1);
    tx.commit().unwrap();
}

/// Fix 3 (prepare side): once ANOTHER attempt has taken the request, the old
/// claim must fail with the precise ClaimSuperseded error (not the blanket
/// InvalidAttempt), must not touch the budget, and the new claimant proceeds.
#[test]
fn expired_claim_superseded_step_gets_precise_error() {
    let mut conn = Connection::open_in_memory().unwrap();
    proofsearch_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    let old = attempts::attempt_claim(&tx, ep_id, req_id, "old-claimant", 1)
        .unwrap().expect("claimable");
    force_expire(&tx, old.attempt_id);

    // A rival re-claims the recovered request (the old workaround's fresh key).
    let rival = attempts::attempt_claim(&tx, ep_id, req_id, "rival-claimant", 1)
        .unwrap().expect("recovered request is claimable by a fresh key");

    // The old claimant's queued step must now fail precisely, without reviving.
    let err = step::attempt_commit(
        &tx, old.attempt_id, 0, &old.claim_token, &TypedAction::GiveUp, &MockGateway, 10,
    ).unwrap_err();
    assert!(
        matches!(err, step::StepError::ClaimSuperseded { .. }),
        "expected ClaimSuperseded, got {:?}", err
    );

    let budget: i64 = tx.query_row(
        "SELECT cost_budget_micros FROM episodes WHERE id = ?1",
        [ep_id.to_string()], |row| row.get(0),
    ).unwrap();
    assert_eq!(budget, 1000, "a superseded step rejected at prepare must not touch the budget");

    // And the rival's step commits normally.
    let outcome = step::attempt_commit(
        &tx, rival.attempt_id, 0, &rival.claim_token, &TypedAction::GiveUp, &MockGateway, 10,
    ).expect("rival step commits");
    assert!(matches!(outcome, LeanVerificationOutcome::KernelPass));
    tx.commit().unwrap();
}

/// Fix 4: idempotency across expiry — re-claiming with the SAME key revives the
/// SAME attempt (same id, same token, fresh expiration) when the request is
/// still untaken, and the revived claim steps normally.
#[test]
fn attempt_claim_same_key_revives_expired_claim() {
    let mut conn = Connection::open_in_memory().unwrap();
    proofsearch_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    let first = attempts::attempt_claim(&tx, ep_id, req_id, "same-key", 1)
        .unwrap().expect("claimable");
    force_expire(&tx, first.attempt_id);

    let revived = attempts::attempt_claim(&tx, ep_id, req_id, "same-key", 1)
        .unwrap().expect("same-key re-claim must revive the expired attempt");
    assert_eq!(revived.attempt_id, first.attempt_id, "same key must map to the same attempt");
    assert_eq!(revived.claim_token, first.claim_token, "revival must not mint a new token");
    assert!(revived.claim_expiration > Utc::now().to_rfc3339(), "revival must refresh the expiration");

    let req_status: String = tx.query_row(
        "SELECT status FROM action_requests WHERE id = ?1",
        [attempt_request_id(&tx, first.attempt_id)], |row| row.get(0),
    ).unwrap();
    assert_eq!(req_status, "claimed", "revival must re-take the request");

    let outcome = step::attempt_commit(
        &tx, revived.attempt_id, 0, &revived.claim_token, &TypedAction::GiveUp, &MockGateway, 10,
    ).expect("revived claim steps normally");
    assert!(matches!(outcome, LeanVerificationOutcome::KernelPass));
    tx.commit().unwrap();
}

/// Fix 4 boundary: after a rival takes the request, the same-key re-claim must
/// still be refused (no double-claim of one request under two live attempts).
#[test]
fn attempt_claim_same_key_after_supersede_refused() {
    let mut conn = Connection::open_in_memory().unwrap();
    proofsearch_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    let old = attempts::attempt_claim(&tx, ep_id, req_id, "loser-key", 1)
        .unwrap().expect("claimable");
    force_expire(&tx, old.attempt_id);
    let _rival = attempts::attempt_claim(&tx, ep_id, req_id, "winner-key", 1)
        .unwrap().expect("recovered request claimable");

    let refused = attempts::attempt_claim(&tx, ep_id, req_id, "loser-key", 1).unwrap();
    assert!(refused.is_none(), "superseded key must not revive over the rival's claim");

    // The rival's claim must be untouched by the refused revival probe.
    let rival_req: String = tx.query_row(
        "SELECT status FROM action_requests WHERE id = ?1",
        [req_id.to_string()], |row| row.get(0),
    ).unwrap();
    assert_eq!(rival_req, "claimed");
    tx.commit().unwrap();
}

/// Fix 2 + 3 (finalize side): the claim expires MID-GATEWAY. If the request is
/// untaken, finalize revives and commits the already-paid-for verdict; if a
/// rival took it, finalize must refuse AND refund the budget reserved at
/// prepare (the pre-fix leak), leaving the rival's world consistent.
#[test]
fn finalize_superseded_refunds_reservation() {
    let mut conn = Connection::open_in_memory().unwrap();
    proofsearch_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    let old = attempts::attempt_claim(&tx, ep_id, req_id, "mid-gateway", 1)
        .unwrap().expect("claimable");

    // Prepare a Solve: reserves budget, marks executing, returns NeedsGateway.
    let action = TypedAction::Solve { proof_term: "rfl".to_string(), proof_format: ProofFormat::FlatTacticSequence };
    let prep = step::attempt_prepare(&tx, old.attempt_id, 0, &old.claim_token, &action, 10)
        .expect("prepare succeeds");
    let ctx = match prep {
        step::PrepOutcome::NeedsGateway { ctx, .. } => ctx,
        step::PrepOutcome::Done { .. } => panic!("Solve must defer to the gateway"),
    };
    let budget_reserved: i64 = tx.query_row(
        "SELECT cost_budget_micros FROM episodes WHERE id = ?1",
        [ep_id.to_string()], |row| row.get(0),
    ).unwrap();
    assert_eq!(budget_reserved, 990, "prepare must reserve the step cost");

    // While the (conceptual) Lean call runs, the sweep expires the attempt and
    // a rival takes the request.
    force_expire(&tx, old.attempt_id);
    let _rival = attempts::attempt_claim(&tx, ep_id, req_id, "rival-mid-gateway", 1)
        .unwrap().expect("recovered request claimable");

    // The gateway verdict comes back — but the attempt is superseded.
    let err = step::attempt_finalize(
        &tx, old.attempt_id, &old.claim_token, 10, ctx, step::GatewayResponse::Solve(Ok(pass_result())),
    ).unwrap_err();
    assert!(
        matches!(err, step::StepError::ClaimSuperseded { .. }),
        "expected ClaimSuperseded, got {:?}", err
    );

    let (budget_after, revision, proved): (i64, i64, i64) = tx.query_row(
        "SELECT e.cost_budget_micros, e.current_revision,
                (SELECT COUNT(*) FROM episode_obligations o WHERE o.episode_id = e.id AND o.status = 'proved')
         FROM episodes e WHERE e.id = ?1",
        [ep_id.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).unwrap();
    assert_eq!(budget_after, 1000, "superseded finalize must refund the prepare-time reservation");
    assert_eq!(revision, 0, "superseded finalize must not commit a step");
    assert_eq!(proved, 0, "the discarded verdict must not close the obligation");
    tx.commit().unwrap();
}

/// Fix 2 happy path: expired mid-gateway but UNTAKEN — finalize revives and the
/// verified result lands (no verification work discarded).
#[test]
fn finalize_revives_expired_untaken_claim() {
    let mut conn = Connection::open_in_memory().unwrap();
    proofsearch_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    let claim = attempts::attempt_claim(&tx, ep_id, req_id, "mid-gateway-untaken", 1)
        .unwrap().expect("claimable");
    let action = TypedAction::Solve { proof_term: "rfl".to_string(), proof_format: ProofFormat::FlatTacticSequence };
    let prep = step::attempt_prepare(&tx, claim.attempt_id, 0, &claim.claim_token, &action, 10)
        .expect("prepare succeeds");
    let ctx = match prep {
        step::PrepOutcome::NeedsGateway { ctx, .. } => ctx,
        step::PrepOutcome::Done { .. } => panic!("Solve must defer to the gateway"),
    };

    force_expire(&tx, claim.attempt_id);

    let outcome = step::attempt_finalize(
        &tx, claim.attempt_id, &claim.claim_token, 10, ctx, step::GatewayResponse::Solve(Ok(pass_result())),
    ).expect("finalize must revive the expired-but-untaken attempt");
    assert!(matches!(outcome, LeanVerificationOutcome::KernelPass));

    let (att_status, revision): (String, i64) = tx.query_row(
        "SELECT a.status, e.current_revision FROM action_attempts a
         JOIN episodes e ON e.id = a.episode_id WHERE a.id = ?1",
        [claim.attempt_id.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?)),
    ).unwrap();
    assert_eq!(att_status, "committed");
    assert_eq!(revision, 1);
    tx.commit().unwrap();
}

/// Fix 5 — the issue's field pattern end-to-end: a burst of N claims all
/// outlive their TTL before any step runs (the serialized-verification tail);
/// after the sweep, every step with its ORIGINAL claim must still commit, and
/// no expired-attempt/pending-request debris may remain.
#[test]
fn burst_tail_expiry_regression() {
    const BURST: usize = 8;
    let mut conn = Connection::open_in_memory().unwrap();
    proofsearch_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let mut claims = Vec::new();
    for i in 0..BURST {
        let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
        tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
        let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();
        let claim = attempts::attempt_claim(&tx, ep_id, req_id, &format!("burst-{}", i), 1)
            .unwrap().expect("claimable");
        claims.push(claim);
    }

    // The whole burst outlives its TTL before any step gets a turn.
    for claim in &claims {
        tx.execute(
            "UPDATE action_attempts SET claim_expiration = ?1 WHERE id = ?2",
            ((Utc::now() - chrono::Duration::hours(1)).to_rfc3339(), claim.attempt_id.to_string()),
        ).unwrap();
    }
    let recovered = attempts::attempt_recover_expired(&tx).unwrap();
    assert_eq!(recovered, BURST, "sweep recovers the entire burst");

    // Every queued step now runs with its original claim — all must commit.
    for claim in &claims {
        let outcome = step::attempt_commit(
            &tx, claim.attempt_id, 0, &claim.claim_token, &TypedAction::GiveUp, &MockGateway, 10,
        ).expect("every burst step must revive and commit");
        assert!(matches!(outcome, LeanVerificationOutcome::KernelPass));
    }

    // No orphans: nothing left 'expired', no request stuck 'pending' or 'claimed'.
    let (expired_left, unfulfilled): (i64, i64) = tx.query_row(
        "SELECT
            (SELECT COUNT(*) FROM action_attempts WHERE status = 'expired'),
            (SELECT COUNT(*) FROM action_requests WHERE status != 'fulfilled')",
        [],
        |row| Ok((row.get(0)?, row.get(1)?)),
    ).unwrap();
    assert_eq!(expired_left, 0, "no attempt may remain expired after the burst commits");
    assert_eq!(unfulfilled, 0, "every request must be fulfilled — no wedged debris");
    tx.commit().unwrap();
}
