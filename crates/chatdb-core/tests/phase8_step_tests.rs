use chatdb_proof_core::orchestrator::{lifecycle, attempts, step};
use chatdb_proof_core::lean::LeanGateway;
use chatdb_proof_core::models::{Obligation, LeanVerificationOutcome, LeanVerificationResult, action::TypedAction};
use rusqlite::Connection;
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
