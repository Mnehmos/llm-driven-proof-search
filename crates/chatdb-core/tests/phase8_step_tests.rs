use chatdb_proof_core::orchestrator::{lifecycle, attempts, step};
use chatdb_proof_core::lean::LeanGateway;
use chatdb_proof_core::models::{Obligation, LeanVerificationOutcome, LeanVerificationResult, action::TypedAction};
use rusqlite::Connection;
use std::sync::{Arc, atomic::{AtomicUsize, Ordering}};
use uuid::Uuid;
use chrono::Utc;

struct MockGateway;
impl LeanGateway for MockGateway {
    fn verify_exact(
        &self,
        _obligation: &Obligation,
        candidate_source: &str,
        _approved_dependency_ids: &[Uuid],
        _environment: &str,
        _import_manifest: &[String],
    ) -> Result<LeanVerificationResult, String> {
        if candidate_source.contains("sorry") {
            Ok(LeanVerificationResult {
                outcome: LeanVerificationOutcome::KernelFail,
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
                wall_time_ms: 10,
                lean_cpu_time_ms: 10,
            })
        } else {
            Ok(LeanVerificationResult {
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
                wall_time_ms: 10,
                lean_cpu_time_ms: 10,
            })
        }
    }
}

struct CountingGateway {
    calls: Arc<AtomicUsize>,
}

impl LeanGateway for CountingGateway {
    fn verify_exact(
        &self,
        _obligation: &Obligation,
        _candidate_source: &str,
        _approved_dependency_ids: &[Uuid],
        _environment: &str,
        _import_manifest: &[String],
    ) -> Result<LeanVerificationResult, String> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        Ok(LeanVerificationResult {
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
            wall_time_ms: 10,
            lean_cpu_time_ms: 10,
        })
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

#[test]
fn test_atomic_step() {
    let mut conn = Connection::open_in_memory().unwrap();
    chatdb_proof_core::db::schema_v1::initialize_v1_db(&conn).unwrap();

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

    let tx = conn.transaction().unwrap();

    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    
    // Set some budget
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();

    let claim_res = attempts::attempt_claim(
        &tx, ep_id, req_id, "idempotency_step", 1
    ).unwrap().expect("Should be claimable");

    let gateway = MockGateway;
    
    // Action 1: solve with sorry (invalid)
    let action_bad = TypedAction::Solve { proof_term: "sorry".to_string() };
    
    let outcome = step::attempt_commit(
        &tx, claim_res.attempt_id, 0, &claim_res.claim_token, &action_bad, &gateway, 10
    ).unwrap();
    
    assert!(matches!(outcome, LeanVerificationOutcome::KernelFail));

    // Check budget and invalid_action_count
    let (budget, invalid, rev): (i64, i64, i64) = tx.query_row(
        "SELECT cost_budget_micros, invalid_action_count, current_revision FROM episodes WHERE id = ?1",
        [ep_id.to_string()],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).unwrap();
    assert_eq!(budget, 990);
    assert_eq!(invalid, 1);
    assert_eq!(rev, 1);

    tx.commit().unwrap();
}

#[test]
fn test_attempt_commit_rejects_negative_cost_without_budget_credit() {
    let mut conn = Connection::open_in_memory().unwrap();
    chatdb_proof_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();
    let claim_res = attempts::attempt_claim(
        &tx, ep_id, req_id, "negative_cost_core", 1
    ).unwrap().expect("Should be claimable");

    let gateway = MockGateway;
    let action = TypedAction::GiveUp;
    let err = step::attempt_commit(
        &tx, claim_res.attempt_id, 0, &claim_res.claim_token, &action, &gateway, -10
    ).unwrap_err();

    assert!(matches!(err, step::StepError::InvalidCost { cost_micros: -10 }));
    let (budget, steps, attempt_status): (i64, i64, String) = tx.query_row(
        "SELECT e.cost_budget_micros, e.step_count, a.status
         FROM episodes e JOIN action_attempts a ON a.episode_id = e.id
         WHERE e.id = ?1 AND a.id = ?2",
        (ep_id.to_string(), claim_res.attempt_id.to_string()),
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).unwrap();
    assert_eq!(budget, 1000, "negative cost must not credit the episode budget");
    assert_eq!(steps, 0, "negative cost must not commit an environment step");
    assert_eq!(attempt_status, "claimed", "core rejection happens before attempt mutation");
    tx.commit().unwrap();
}

#[test]
fn test_over_budget_solve_is_denied_before_gateway_execution() {
    let mut conn = Connection::open_in_memory().unwrap();
    chatdb_proof_core::db::schema_v1::initialize_v1_db(&conn).unwrap();
    let pv_id = insert_test_problem(&conn);

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 5 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();
    let claim_res = attempts::attempt_claim(
        &tx, ep_id, req_id, "over_budget_core", 1
    ).unwrap().expect("Should be claimable");

    let calls = Arc::new(AtomicUsize::new(0));
    let gateway = CountingGateway { calls: calls.clone() };
    let action = TypedAction::Solve { proof_term: "rfl".to_string() };
    let err = step::attempt_commit(
        &tx, claim_res.attempt_id, 0, &claim_res.claim_token, &action, &gateway, 10
    ).unwrap_err();

    assert!(matches!(
        err,
        step::StepError::BudgetExceeded { requested_cost_micros: 10, remaining_cost_micros: 5 }
    ));
    assert_eq!(calls.load(Ordering::SeqCst), 0, "gateway must not run for an over-budget step");
    let (budget, steps, attempt_status): (i64, i64, String) = tx.query_row(
        "SELECT e.cost_budget_micros, e.step_count, a.status
         FROM episodes e JOIN action_attempts a ON a.episode_id = e.id
         WHERE e.id = ?1 AND a.id = ?2",
        (ep_id.to_string(), claim_res.attempt_id.to_string()),
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).unwrap();
    assert_eq!(budget, 5, "failed reservation must leave the bounded budget unchanged");
    assert_eq!(steps, 0, "over-budget denial must not count as an environment step");
    assert_eq!(attempt_status, "claimed", "over-budget denial happens before attempt execution");
    tx.commit().unwrap();
}
