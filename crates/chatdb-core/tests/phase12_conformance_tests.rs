use chatdb_proof_core::orchestrator::{lifecycle, attempts, step, trajectories};
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
        _candidate_source: &str,
        _approved_dependency_ids: &[Uuid],
        _environment: &str,
    ) -> Result<LeanVerificationResult, String> {
        Ok(LeanVerificationResult {
            outcome: LeanVerificationOutcome::KernelPass,
            attempt_id: Uuid::new_v4(),
            obligation_id: Uuid::new_v4(),
            theorem_name: "thm".to_string(),
            expected_statement_hash: "hash".to_string(),
            elaborated_statement_hash: None,
            environment_hash: "env".to_string(),
            proof_source_hash: "".to_string(),
            compiled_artifact_hash: None,
            proof_term_hash: None,
            diagnostic: None,
            dependency_use_report: None,
            wall_time_ms: 10,
            lean_cpu_time_ms: 10,
        })
    }
}

#[test]
fn test_production_path_matches_replay_path() {
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
            'env_hash', 'approved', 'manual', 'COMPLETE', ?2
        )",
        (pv_id.to_string(), Utc::now().to_rfc3339()),
    ).unwrap();

    let tx = conn.transaction().unwrap();
    let ep_id = lifecycle::episode_create(&tx, pv_id).unwrap();
    tx.execute("UPDATE episodes SET cost_budget_micros = 1000 WHERE id = ?1", [ep_id.to_string()]).unwrap();
    let req_id = lifecycle::advance(&tx, ep_id).unwrap().unwrap();
    
    let claim_res = attempts::attempt_claim(
        &tx, ep_id, req_id, "idempotency_conformance", 1
    ).unwrap().expect("Claim ok");

    let gateway = MockGateway;
    let action = TypedAction::Solve { proof_term: "rfl".to_string() };
    
    // Live/Production step execution path
    let live_outcome = step::attempt_commit(
        &tx, claim_res.attempt_id, 0, &claim_res.claim_token, &action, &gateway, 10
    ).unwrap();
    
    assert!(matches!(live_outcome, LeanVerificationOutcome::KernelPass));
    tx.commit().unwrap();

    // Replay execution path: verify replay_trajectory and audit_trajectory match live execution results
    let audit_ok = trajectories::audit_trajectory(&conn, ep_id).unwrap();
    assert!(audit_ok, "Audit must pass on production-recorded trajectory");

    let replay_res = trajectories::replay_trajectory(&conn, ep_id, &gateway);
    assert!(replay_res.is_ok(), "Replay path must successfully execute without error");
}
