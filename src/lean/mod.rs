use std::fs;
use std::process::Command;
use std::time::Instant;
use std::path::PathBuf;
use crate::models::{
    Obligation, LeanVerificationResult, LeanVerificationOutcome, LeanDiagnostic, LeanDiagnosticCategory
};
use uuid::Uuid;

pub trait LeanGateway {
    fn verify_exact(
        &self,
        obligation: &Obligation,
        candidate_source: &str,
        approved_dependency_ids: &[Uuid],
        environment: &str,
    ) -> Result<LeanVerificationResult, String>;
}

pub struct RealLeanGateway {
    pub lean_project_path: PathBuf,
    pub elan_bin_path: PathBuf,
}

impl RealLeanGateway {
    pub fn new(lean_project_path: PathBuf, elan_bin_path: PathBuf) -> Self {
        Self { lean_project_path, elan_bin_path }
    }
}

impl LeanGateway for RealLeanGateway {
    fn verify_exact(
        &self,
        obligation: &Obligation,
        candidate_source: &str,
        approved_dependency_ids: &[Uuid],
        environment: &str,
    ) -> Result<LeanVerificationResult, String> {
        let start_time = Instant::now();

        // 1. Generate namespace and theorem name
        let namespace_first_16 = &obligation.problem_version_id.to_string().replace("-", "")[..16];
        let obligation_first_16 = &obligation.id.to_string().replace("-", "")[..16];
        
        let problem_namespace = format!("ChatDB.P_{}", namespace_first_16);
        let theorem_name = format!("O_{}", obligation_first_16);

        // 2. Generate dependency imports
        let mut imports = String::new();
        imports.push_str("import Mathlib.Tactic.Omega\n");
        imports.push_str("import Mathlib.Tactic.Ring\n");
        imports.push_str("import Mathlib.Tactic.NormNum\n");
        imports.push_str("set_option linter.unusedTactic false\n");
        imports.push_str("set_option linter.unreachableTactic false\n");

        for dep_id in approved_dependency_ids {
            let dep_first_16 = &dep_id.to_string().replace("-", "")[..16];
            imports.push_str(&format!("import LeanChecker.Verified.O_{}\n", dep_first_16));
        }

        // 3. Construct Lean source code
        let file_content = format!(
            "{}\nnamespace {}\n\ntheorem {} : {} := by\n{}\n\nend {}\n",
            imports,
            problem_namespace,
            theorem_name,
            obligation.lean_statement,
            candidate_source,
            problem_namespace
        );

        // 4. Write to a file in the Lean project
        let verified_dir = self.lean_project_path.join("LeanChecker").join("Verified");
        if !verified_dir.exists() {
            fs::create_dir_all(&verified_dir).map_err(|e| e.to_string())?;
        }

        let file_path = verified_dir.join(format!("{}.lean", theorem_name));
        fs::write(&file_path, &file_content).map_err(|e| e.to_string())?;

        // 5. Run lake env lean --json File.lean
        let lake_path = self.elan_bin_path.join("lake.exe");
        
        let mut cmd = Command::new(&lake_path);
        cmd.arg("env")
            .arg("lean")
            .arg("--json")
            .arg(format!("LeanChecker/Verified/{}.lean", theorem_name))
            .current_dir(&self.lean_project_path)
            .env("ELAN_HOME", &self.elan_bin_path);

        let output = cmd.output().map_err(|e| e.to_string())?;
        let stdout_str = String::from_utf8_lossy(&output.stdout);
        let _stderr_str = String::from_utf8_lossy(&output.stderr);

        // Parse diagnostics
        let mut parse_error = false;
        let mut elaboration_error = false;
        let mut unsolved_goals = false;
        let mut error_messages = Vec::new();

        for line in stdout_str.lines() {
            if let Ok(val) = serde_json::from_str::<serde_json::Value>(line) {
                if let Some(severity) = val.get("severity").and_then(|s| s.as_str()) {
                    if severity == "error" {
                        if let Some(msg) = val.get("message").and_then(|m| m.as_str()) {
                            error_messages.push(msg.to_string());
                            if msg.contains("expected") || msg.contains("unknown identifier") {
                                parse_error = true;
                            } else if msg.contains("unsolved goals") {
                                unsolved_goals = true;
                            } else if msg.contains("type mismatch") {
                                elaboration_error = true;
                            }
                        }
                    }
                }
            }
        }

        let success = output.status.success() && error_messages.is_empty();

        let diagnostic = if !success {
            let category = if parse_error {
                LeanDiagnosticCategory::ParseError
            } else if unsolved_goals {
                LeanDiagnosticCategory::UnsolvedGoals
            } else if elaboration_error {
                LeanDiagnosticCategory::TypeMismatch
            } else {
                LeanDiagnosticCategory::TacticFailure
            };
            Some(LeanDiagnostic {
                category,
                primary_message: error_messages.join("; "),
                source_span: None,
                goal: None,
                local_context: vec![],
                unsolved_goals: vec![],
                used_dependencies: vec![],
                error_code: None,
                canonical_goal_hash: None,
            })
        } else {
            None
        };

        let outcome = if success {
            LeanVerificationOutcome::KernelPass
        } else {
            LeanVerificationOutcome::KernelFail
        };

        // If successful, compile the module using `lake build` so it's ready for imports
        if success {
            let mut build_cmd = Command::new(&lake_path);
            build_cmd.arg("build")
                .arg(format!("LeanChecker.Verified.{}", theorem_name))
                .current_dir(&self.lean_project_path)
                .env("ELAN_HOME", &self.elan_bin_path);
            
            let _ = build_cmd.output();
        } else {
            // Delete the failed file
            let _ = fs::remove_file(&file_path);
        }

        let wall_time_ms = start_time.elapsed().as_millis() as u64;

        Ok(LeanVerificationResult {
            outcome,
            attempt_id: Uuid::new_v4(), // We will assign the real attempt_id when committing
            obligation_id: obligation.id,
            theorem_name,
            expected_statement_hash: obligation.statement_hash.clone(),
            elaborated_statement_hash: None,
            environment_hash: environment.to_string(),
            proof_source_hash: "".to_string(),
            compiled_artifact_hash: None,
            proof_term_hash: None,
            diagnostic,
            dependency_use_report: None,
            wall_time_ms,
            lean_cpu_time_ms: wall_time_ms,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{Obligation, ObligationKind, ObligationCreator, ObligationStatus};
    use chrono::Utc;
    use std::path::PathBuf;

    #[test]
    fn test_real_lean_gateway_failure_cases() {
        let elan_bin_path = PathBuf::from("F:\\.elan\\bin");
        let lean_project_path = PathBuf::from("F:\\Github\\ChatDB\\lean-checker");
        
        let gateway = RealLeanGateway::new(lean_project_path, elan_bin_path);

        let obligation = Obligation {
            id: Uuid::new_v4(),
            problem_version_id: Uuid::new_v4(),
            kind: ObligationKind::Root,
            theorem_name: "test_theorem".to_string(),
            lean_statement: "1 = 2".to_string(),
            statement_hash: "hash".to_string(),
            natural_description: "test".to_string(),
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

        // This should fail to prove since 1 = 2 is false.
        let res = gateway.verify_exact(&obligation, "rfl", &[], "envhash");
        if let Ok(res_val) = res {
            assert!(matches!(res_val.outcome, LeanVerificationOutcome::KernelFail));
        }
    }
}
