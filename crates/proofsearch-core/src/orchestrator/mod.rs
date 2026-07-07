pub mod scheduler;
pub mod budget;
pub mod context;
pub mod lifecycle;
pub mod attempts;
pub mod step;
pub mod trajectories;
pub mod dataset;

use rusqlite::Connection;
use uuid::Uuid;
use crate::models::{
    ProblemState, Obligation, ObligationStatus, ObligationKind, LeanVerificationOutcome,
    VerifiedLemma, Polarity, AttemptDiagnostic, AttemptOutcome
};
use crate::orchestrator::scheduler::next_ready;
use crate::orchestrator::budget::BudgetGovernor;
use crate::orchestrator::context::{CompactContextBuilder, CompactContext};
use crate::lean::LeanGateway;

pub trait Prover {
    fn propose_proof(
        &self,
        obligation: &Obligation,
        context: &CompactContext,
    ) -> Result<String, String>;
}

pub struct Orchestrator<'a, L: LeanGateway, P: Prover> {
    pub conn: &'a mut Connection,
    pub lean_gateway: &'a L,
    pub prover: &'a P,
    pub budget_governor: &'a BudgetGovernor,
    pub context_builder: &'a CompactContextBuilder,
}

impl<'a, L: LeanGateway, P: Prover> Orchestrator<'a, L, P> {
    pub fn new(
        conn: &'a mut Connection,
        lean_gateway: &'a L,
        prover: &'a P,
        budget_governor: &'a BudgetGovernor,
        context_builder: &'a CompactContextBuilder,
    ) -> Self {
        Self {
            conn,
            lean_gateway,
            prover,
            budget_governor,
            context_builder,
        }
    }

    pub fn run(&mut self, problem_version_id: Uuid) -> Result<(), String> {
        // 1. Load problem version
        let mut pv = crate::db::get_problem_version(self.conn, problem_version_id)
            .map_err(|e| format!("DB error loading problem version: {}", e))?
            .ok_or_else(|| format!("Problem version {} not found", problem_version_id))?;

        if pv.fidelity_status != crate::models::FidelityStatus::Approved {
            return Err("Problem not approved".to_string());
        }

        // Main Loop
        loop {
            // Reload problem version to get latest state
            pv = crate::db::get_problem_version(self.conn, problem_version_id)
                .map_err(|e| e.to_string())?
                .unwrap();

            if matches!(
                pv.state,
                ProblemState::Complete | ProblemState::StalledNeedsHuman | ProblemState::Cancelled | ProblemState::BudgetExhausted
            ) {
                return Ok(());
            }

            // Check budget
            let spent = self.budget_governor.get_spent_cost(self.conn, problem_version_id)?;
            if spent >= self.budget_governor.max_total_cost_usd_micros {
                crate::db::update_problem_version_state(self.conn, problem_version_id, ProblemState::BudgetExhausted)
                    .map_err(|e| e.to_string())?;
                return Ok(());
            }

            // Check if root is proved
            let obligations = crate::db::get_obligations_for_problem(self.conn, problem_version_id)
                .map_err(|e| e.to_string())?;
            let root_o = obligations.iter().find(|o| matches!(o.kind, ObligationKind::Root));
            
            if let Some(root) = root_o {
                if root.status == ObligationStatus::Proved {
                    crate::db::update_problem_version_state(self.conn, problem_version_id, ProblemState::Complete)
                        .map_err(|e| e.to_string())?;
                    return Ok(());
                }
            }

            // Get next ready obligation
            let remaining_budget = (self.budget_governor.max_total_cost_usd_micros - spent) as f64;
            let obligation_opt = next_ready(self.conn, problem_version_id, remaining_budget)?;

            let obligation = match obligation_opt {
                Some(o) => o,
                None => {
                    // No ready obligation. Are there open obligations?
                    let has_open = obligations.iter().any(|o| o.status == ObligationStatus::Open || o.status == ObligationStatus::InProgress);
                    if has_open {
                        crate::db::update_problem_version_state(self.conn, problem_version_id, ProblemState::StalledNeedsHuman)
                            .map_err(|e| e.to_string())?;
                        return Err("Open obligations exist but none are ready (cycle/unresolved dependency)".to_string());
                    } else {
                        if root_o.map(|r| r.status == ObligationStatus::Proved).unwrap_or(false) {
                            crate::db::update_problem_version_state(self.conn, problem_version_id, ProblemState::Complete)
                                .map_err(|e| e.to_string())?;
                        } else {
                            crate::db::update_problem_version_state(self.conn, problem_version_id, ProblemState::StalledNeedsHuman)
                                .map_err(|e| e.to_string())?;
                        }
                        return Ok(());
                    }
                }
            };

            // Transition obligation to in_progress
            crate::db::update_obligation_status(self.conn, obligation.id, ObligationStatus::InProgress)
                .map_err(|e| e.to_string())?;

            // Build context
            let context = match self.context_builder.build(self.conn, &obligation, &pv.environment_hash, &pv.root_formal_statement) {
                Ok(ctx) => ctx,
                Err(e) => {
                    crate::db::update_obligation_status(self.conn, obligation.id, ObligationStatus::Open)
                        .map_err(|e| e.to_string())?;
                    if e == "CONTEXT_TOO_LARGE" {
                        return Err("Context size exceeded limit".to_string());
                    } else {
                        return Err(e);
                    }
                }
            };

            // Reserve budget
            let reserved_cost = 50; // 50 micros
            let reservation = match self.budget_governor.reserve(
                self.conn,
                problem_version_id,
                Some(obligation.id),
                "prover_attempt",
                1000,
                1000,
                reserved_cost,
                5000,
            )? {
                Some(res) => res,
                None => {
                    crate::db::update_problem_version_state(self.conn, problem_version_id, ProblemState::BudgetExhausted)
                        .map_err(|e| e.to_string())?;
                    return Ok(());
                }
            };

            // Call prover
            let proposal_res = self.prover.propose_proof(&obligation, &context);
            let candidate_proof = match proposal_res {
                Ok(proof) => proof,
                Err(e) => {
                    self.budget_governor.commit(self.conn, &reservation.reservation_id, 0, 0, 0, 0)?;
                    crate::db::update_obligation_status(self.conn, obligation.id, ObligationStatus::Open)
                        .map_err(|e| e.to_string())?;
                    return Err(format!("Prover failed: {}", e));
                }
            };

            // Get direct dependencies
            let dep_ids = {
                let mut dep_stmt = self.conn.prepare(
                    "SELECT dependency_obligation_id FROM obligation_edges WHERE parent_obligation_id = ?1"
                ).map_err(|e| e.to_string())?;
                let dep_rows = dep_stmt.query_map([obligation.id.to_string()], |row| {
                    let id_str: String = row.get(0)?;
                    Ok(Uuid::parse_str(&id_str).unwrap())
                }).map_err(|e| e.to_string())?;
                let mut dep_ids = Vec::new();
                for r in dep_rows {
                    dep_ids.push(r.map_err(|e| e.to_string())?);
                }
                dep_ids
            };

            // Run verification. This legacy canonical-storage Orchestrator predates
            // per-problem import manifests; it isn't exercised by the MCP path, so
            // it keeps the historical default manifest rather than threading a new
            // field through ProblemVersion.
            let default_manifest = ["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()];
            let verify_result = self.lean_gateway.verify_exact(
                &obligation,
                &candidate_proof,
                &dep_ids,
                &pv.environment_hash,
                &default_manifest,
                crate::models::action::ProofFormat::FlatTacticSequence,
            );

            match verify_result {
                Ok(res) => {
                    // Commit budget
                    let actual_cost = 10; // 10 micros
                    self.budget_governor.commit(
                        self.conn,
                        &reservation.reservation_id,
                        500,
                        500,
                        actual_cost,
                        res.wall_time_ms as i64,
                    )?;

                    // Persist attempt diagnostic
                    let attempt_id = Uuid::new_v4();
                    let diag_json = res.diagnostic.as_ref().map(|d| serde_json::to_string(d).unwrap());
                    let outcome = if res.outcome == LeanVerificationOutcome::KernelPass {
                        AttemptOutcome::KernelPass
                    } else {
                        AttemptOutcome::KernelFail
                    };

                    let attempt = AttemptDiagnostic {
                        id: attempt_id,
                        obligation_id: obligation.id,
                        role: "prover".to_string(),
                        model_config_hash: None,
                        prompt_hash: "dummy_prompt_hash".to_string(),
                        context_manifest_hash: "dummy_context_manifest_hash".to_string(),
                        candidate_source_artifact_hash: Some("dummy_source_hash".to_string()),
                        diagnostic_json: diag_json,
                        outcome,
                        input_tokens: 500,
                        output_tokens: 500,
                        cost_usd_micros: actual_cost,
                        wall_time_ms: res.wall_time_ms as i64,
                        lean_cpu_time_ms: res.lean_cpu_time_ms as i64,
                        created_at: chrono::Utc::now(),
                    };
                    crate::db::insert_attempt(self.conn, &attempt).map_err(|e| e.to_string())?;

                    if res.outcome == LeanVerificationOutcome::KernelPass {
                        let lemma_id = Uuid::new_v4();
                        let lemma = VerifiedLemma {
                            id: lemma_id,
                            obligation_id: obligation.id,
                            polarity: Polarity::Positive,
                            theorem_name: res.theorem_name,
                            statement_hash: obligation.statement_hash.clone(),
                            proof_source_artifact_hash: "dummy_source_hash".to_string(),
                            compiled_artifact_hash: "dummy_compiled_hash".to_string(),
                            proof_term_hash: "dummy_proof_term_hash".to_string(),
                            environment_hash: pv.environment_hash.clone(),
                            actual_dependency_ids_json: "[]".to_string(),
                            kernel_result_hash: "dummy_kernel_hash".to_string(),
                            verified_at: chrono::Utc::now(),
                        };

                        // Commit kernel pass (using transactional db module)
                        crate::db::commit_kernel_pass(&mut *self.conn, obligation.id, &lemma)
                            .map_err(|e| e.to_string())?;
                    } else {
                        // Revert obligation to Open, and increment attempt_count
                        self.conn.execute(
                            "UPDATE obligations SET attempt_count = attempt_count + 1 WHERE id = ?1",
                            [obligation.id.to_string()]
                        ).map_err(|e| e.to_string())?;

                        crate::db::update_obligation_status(self.conn, obligation.id, ObligationStatus::Open)
                            .map_err(|e| e.to_string())?;
                    }
                }
                Err(e) => {
                    self.budget_governor.commit(self.conn, &reservation.reservation_id, 0, 0, 0, 0)?;
                    crate::db::update_obligation_status(self.conn, obligation.id, ObligationStatus::Open)
                        .map_err(|e| e.to_string())?;
                    return Err(format!("Verification system error: {}", e));
                }
            }
        }
    }
}

#[cfg(all(test, feature = "legacy_tests"))]
mod tests {
    use super::*;
    use crate::db::{initialize_db, insert_problem_version, insert_obligation};
    use crate::models::{FidelityStatus, ObligationCreator};
    use chrono::Utc;

    struct StubProver;
    impl Prover for StubProver {
        fn propose_proof(&self, _o: &Obligation, _c: &CompactContext) -> Result<String, String> {
            Ok("rfl".to_string())
        }
    }

    struct StubLeanGateway;
    impl LeanGateway for StubLeanGateway {
        fn verify_exact(
            &self,
            _o: &Obligation,
            _c: &str,
            _deps: &[Uuid],
            _env: &str,
            _import_manifest: &[String],
            _proof_format: crate::models::action::ProofFormat,
        ) -> Result<crate::models::LeanVerificationResult, String> {
            Ok(crate::models::LeanVerificationResult {
                outcome: LeanVerificationOutcome::KernelPass,
                attempt_id: Uuid::new_v4(),
                obligation_id: Uuid::new_v4(),
                theorem_name: "test".to_string(),
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
    fn test_orchestrator_success() {
        let mut conn = Connection::open_in_memory().unwrap();
        initialize_db(&conn).unwrap();

        let problem_id = Uuid::new_v4();
        let pv = ProblemVersion {
            id: problem_id,
            source_problem_text: "Prove x + 0 = x".to_string(),
            source_problem_hash: "hash1".to_string(),
            source_metadata_json: "{}".to_string(),
            root_formal_statement: "theorem root (x : Int) : x + 0 = x".to_string(),
            root_statement_hash: "hash2".to_string(),
            normalized_root_rendering: "x + 0 = x".to_string(),
            environment_hash: "envhash".to_string(),
            fidelity_status: FidelityStatus::Approved,
            fidelity_method: "human_authored".to_string(),
            fidelity_approval_id: None,
            root_obligation_id: None,
            state: ProblemState::Proving,
            created_at: Utc::now(),
        };
        insert_problem_version(&conn, &pv).unwrap();

        let root_id = Uuid::new_v4();
        let o_root = Obligation {
            id: root_id,
            problem_version_id: problem_id,
            kind: ObligationKind::Root,
            theorem_name: "O_root".to_string(),
            lean_statement: "x + 0 = x".to_string(),
            statement_hash: "hash2".to_string(),
            natural_description: "root".to_string(),
            status: ObligationStatus::Open,
            depth_from_root: 0,
            created_by: ObligationCreator::InitialSketch,
            created_by_epoch_id: None,
            superseded_by_id: None,
            proved_lemma_id: None,
            refutation_lemma_id: None,
            failure_lesson: None,
            attempt_count: 0,
            created_at: Utc::now(),
            closed_at: None,
        };
        insert_obligation(&conn, &o_root).unwrap();

        let prover = StubProver;
        let gateway = StubLeanGateway;
        let budget = BudgetGovernor::new(1000);
        let builder = CompactContextBuilder::new(1000);

        let mut orchestrator = Orchestrator::new(&mut conn, &gateway, &prover, &budget, &builder);
        let res = orchestrator.run(problem_id);
        assert!(res.is_ok(), "Expected run to succeed: {:?}", res);

        // Verify problem state is now Complete
        let pv_after = crate::db::get_problem_version(&conn, problem_id).unwrap().unwrap();
        assert_eq!(pv_after.state, ProblemState::Complete);

        // Verify obligation state is Proved
        let obligations = crate::db::get_obligations_for_problem(&conn, problem_id).unwrap();
        assert_eq!(obligations[0].status, ObligationStatus::Proved);
    }
}
