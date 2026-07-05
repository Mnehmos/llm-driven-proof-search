use std::fs;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use std::path::PathBuf;
use std::sync::{LazyLock, Mutex};
use crate::models::{
    Obligation, LeanVerificationResult, LeanVerificationOutcome, LeanDiagnostic, LeanDiagnosticCategory,
    DeclarationLookupResult, DeclarationLookupStatus, LeanModuleVerificationResult,
};
use uuid::Uuid;

pub mod module;
use module::{AssembledModule, normalize_and_indent};

pub trait LeanGateway {
    fn verify_exact(
        &self,
        obligation: &Obligation,
        candidate_source: &str,
        approved_dependency_ids: &[Uuid],
        environment: &str,
        import_manifest: &[String],
    ) -> Result<LeanVerificationResult, String>;

    /// Confirms every module in `imports` actually resolves (catches typos /
    /// renamed paths) before it's accepted into a problem's immutable import
    /// manifest. Default fails closed — a gateway that can't actually check an
    /// import shouldn't silently rubber-stamp it (imports are compiled into
    /// every subsequent proof file for that problem, so an unchecked one is an
    /// unchecked addition to the trusted base). `RealLeanGateway` overrides this
    /// with a real compile check; only a gateway that's deliberately vouching
    /// for arbitrary imports (e.g. a test double) should override this to `Ok`.
    fn validate_import_manifest(&self, _imports: &[String]) -> Result<(), String> {
        Err("this gateway cannot validate custom imports".to_string())
    }

    /// Fast pass (single Lean invocation, sub-second beyond process spawn): does
    /// `name` resolve under `import_manifest`? If `deep_check` is true AND a name
    /// fails that pass, ALSO checks under the full Mathlib umbrella — this
    /// second pass loads the entire library from a cold process and reliably
    /// takes 15-40+ seconds (there is no persistent Lean server), so it is
    /// opt-in, not the default. This is the fix for "environmental scope
    /// collapse": an `unknown identifier` elaboration error only ever proves a
    /// name didn't resolve under the exact import closure used for one attempt.
    /// It never proves the name is absent from the pinned library — but proving
    /// that costs real time, so callers choose when to pay for it. Default
    /// reports EnvironmentError honestly rather than guessing.
    fn lookup_declarations(&self, names: &[String], _import_manifest: &[String], _deep_check: bool) -> Result<Vec<DeclarationLookupResult>, String> {
        Ok(names.iter().map(|n| DeclarationLookupResult {
            query: n.clone(),
            status: DeclarationLookupStatus::EnvironmentError,
            diagnostics: vec!["this gateway does not support declaration lookup".to_string()],
        }).collect())
    }

    /// Kernel-checks a whole assembled module (defs + helper theorems + root
    /// theorem) as one unit, in a staged location. Returns `KernelPass` only if
    /// the process succeeds, no error diagnostics were emitted, AND no
    /// `sorry`/`admit` warning appears — the same soundness rule as
    /// `verify_exact`, applied to the module as a whole. On pass the gateway may
    /// write the verified source to `LeanChecker/Verified`; on failure it MUST
    /// NOT (no partial commit). Default fails closed for the same reason
    /// `validate_import_manifest` does — a gateway that can't actually run Lean
    /// must never report a module as verified.
    fn verify_module(
        &self,
        _assembled: &AssembledModule,
        _environment: &str,
    ) -> Result<LeanModuleVerificationResult, String> {
        Err("this gateway cannot verify modules".to_string())
    }
}

/// Serializes `lake build` invocations against the shared Lake workspace at
/// `lean_project_path`. The staged compile (`run_lean_json`, an isolated
/// tempdir per call) is safe under concurrency and stays unserialized — this
/// lock covers only the narrow post-success step that copies a verified
/// source into `LeanChecker/Verified` and runs `lake build` on it. Before the
/// two-phase DB-lock split (review feedback on #16/#17), the single
/// server-wide DB mutex incidentally serialized every `episode_step` call
/// end-to-end, which also serialized this step as a side effect; releasing
/// that mutex during the Lean gateway call means two sessions can now reach
/// `lake build` concurrently for the first time. Lake's build cache is not
/// documented as safe for concurrent cross-process invocations, and the
/// build's exit status is intentionally best-effort (`let _ =
/// build_cmd.output()`) — soundness of the kernel check is unaffected either
/// way (it already happened in the isolated staged compile), but a corrupted
/// or missing durable build artifact for one of two racing submissions would
/// otherwise go unnoticed.
static LAKE_BUILD_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

pub struct RealLeanGateway {
    pub lean_project_path: PathBuf,
    pub elan_bin_path: PathBuf,
}

impl RealLeanGateway {
    pub fn new(lean_project_path: PathBuf, elan_bin_path: PathBuf) -> Self {
        Self { lean_project_path, elan_bin_path }
    }

    /// Writes `file_content` to a temp file and runs `lake env lean --json` on it,
    /// returning the process's overall success, every parsed JSON diagnostic
    /// line, and raw stderr (Lake resolution/build failures land there, not in
    /// the `--json` stdout stream, so silently dropping it hides the actual
    /// cause of an otherwise-unexplained process failure). `Err` here means the
    /// invocation itself failed (spawn error or timeout) — not that Lean
    /// reported errors within the file, which is a normal, successful run that
    /// the caller inspects via the returned lines.
    fn run_lean_json(&self, file_content: &str, file_stem: &str, timeout: Duration) -> Result<(bool, Vec<serde_json::Value>, String), String> {
        let temp_dir = tempfile::tempdir().map_err(|e| e.to_string())?;
        let file_path = temp_dir.path().join(format!("{}.lean", file_stem));
        fs::write(&file_path, file_content).map_err(|e| e.to_string())?;

        let lake_path = self.elan_bin_path.join("lake.exe");
        let mut cmd = Command::new(&lake_path);
        cmd.arg("env")
            .arg("lean")
            .arg("--json")
            .arg(&file_path)
            .current_dir(&self.lean_project_path)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        // ELAN_HOME must be the elan root (where toolchains/ lives), NOT the bin dir.
        if let Ok(elan_home) = std::env::var("CHATDB_ELAN_HOME") {
            cmd.env("ELAN_HOME", elan_home);
        }

        let child = cmd.spawn().map_err(|e| e.to_string())?;
        let (tx, rx) = std::sync::mpsc::channel();
        let pid = child.id();
        std::thread::spawn(move || {
            let res = child.wait_with_output();
            let _ = tx.send(res);
        });

        let output = match rx.recv_timeout(timeout) {
            Ok(Ok(out)) => out,
            Ok(Err(e)) => return Err(format!("Process error: {}", e)),
            Err(_) => {
                #[cfg(target_os = "windows")]
                {
                    let _ = Command::new("taskkill")
                        .arg("/F").arg("/T").arg("/PID").arg(pid.to_string())
                        .status();
                }
                return Err(format!("Lean invocation timed out after {} seconds", timeout.as_secs()));
            }
        };

        let stdout_str = String::from_utf8_lossy(&output.stdout).to_string();
        let lines: Vec<serde_json::Value> = stdout_str.lines()
            .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
            .collect();
        let stderr_str = String::from_utf8_lossy(&output.stderr).to_string();
        Ok((output.status.success(), lines, stderr_str))
    }

    fn build_import_block(import_manifest: &[String], approved_dependency_ids: &[Uuid]) -> String {
        let mut imports = String::new();
        for module in import_manifest {
            imports.push_str(&format!("import {}\n", module));
        }
        for dep_id in approved_dependency_ids {
            let dep_first_16 = &dep_id.to_string().replace("-", "")[..16];
            imports.push_str(&format!("import LeanChecker.Verified.O_{}\n", dep_first_16));
        }
        imports
    }
}

/// Human-readable identity of the actual Lean+Mathlib environment the gateway
/// verifies against, plus a stable hash of it. Read from `lean-toolchain` and the
/// resolved (not just requested) Mathlib commit in `lake-manifest.json` — the
/// server is the only party that can know this, so it should never be a
/// client-supplied placeholder like "unspecified-env".
#[derive(Debug, Clone, serde::Serialize)]
pub struct LeanEnvironmentInfo {
    pub toolchain: String,
    pub mathlib_rev: String,
    pub descriptor: String,
    pub hash: String,
}

/// Returns `None` if `lean-toolchain` or a resolved mathlib manifest entry is
/// missing — i.e. the project isn't set up, matching `lean_available == false`.
pub fn detect_environment(lean_project_path: &std::path::Path) -> Option<LeanEnvironmentInfo> {
    let toolchain = fs::read_to_string(lean_project_path.join("lean-toolchain")).ok()?.trim().to_string();

    let manifest_str = fs::read_to_string(lean_project_path.join("lake-manifest.json")).ok()?;
    let manifest: serde_json::Value = serde_json::from_str(&manifest_str).ok()?;
    let mathlib_rev = manifest.get("packages")?.as_array()?.iter()
        .find(|p| p.get("name").and_then(|n| n.as_str()) == Some("mathlib"))?
        .get("rev")?.as_str()?.to_string();

    let descriptor = format!("{} + mathlib@{}", toolchain, mathlib_rev);
    let hash = crate::hashing::canonical_hash(&descriptor).ok()?;
    Some(LeanEnvironmentInfo { toolchain, mathlib_rev, descriptor, hash })
}

/// Extracts (message, kind, severity, line) from one Lean --json diagnostic line.
fn parse_diagnostic_line(val: &serde_json::Value) -> (String, String, String, Option<i64>) {
    let msg = val.get("data").or_else(|| val.get("message"))
        .and_then(|m| m.as_str()).unwrap_or("").to_string();
    let kind = val.get("kind").and_then(|k| k.as_str()).unwrap_or("").to_string();
    let severity = val.get("severity").and_then(|s| s.as_str()).unwrap_or("").to_string();
    let line = val.get("pos").and_then(|p| p.get("line")).and_then(|l| l.as_i64());
    (msg, kind, severity, line)
}

fn categorize(msg: &str, kind: &str) -> LeanDiagnosticCategory {
    if kind == "hasSorry" || msg.contains("declaration uses `sorry`") || msg.contains("declaration uses 'sorry'") {
        LeanDiagnosticCategory::ProhibitedConstruct
    } else if msg.contains("unknown identifier") || msg.contains("unknown constant") || msg.contains("unknown namespace") {
        // A name that failed to resolve. This says NOTHING about whether the name
        // exists anywhere in the pinned library — only that it didn't resolve
        // under the exact import closure this attempt used. Do not lump this in
        // with generic parse errors, and never let it justify a claim about
        // library capability without a lean_declaration_lookup to back it up.
        LeanDiagnosticCategory::UnknownDeclaration
    } else if msg.contains("unsolved goals") {
        LeanDiagnosticCategory::UnsolvedGoals
    } else if msg.contains("type mismatch") {
        LeanDiagnosticCategory::TypeMismatch
    } else if msg.contains("expected") {
        LeanDiagnosticCategory::ParseError
    } else {
        LeanDiagnosticCategory::TacticFailure
    }
}

fn source_span_of(val: &serde_json::Value) -> Option<String> {
    let pos = val.get("pos")?;
    let line = pos.get("line")?.as_i64()?;
    let col = pos.get("column")?.as_i64()?;
    match val.get("endPos").and_then(|e| e.as_object()) {
        Some(end) => {
            let end_line = end.get("line").and_then(|l| l.as_i64()).unwrap_or(line);
            let end_col = end.get("column").and_then(|c| c.as_i64()).unwrap_or(col);
            Some(format!("{}:{}-{}:{}", line, col, end_line, end_col))
        }
        None => Some(format!("{}:{}", line, col)),
    }
}

impl LeanGateway for RealLeanGateway {
    fn verify_exact(
        &self,
        obligation: &Obligation,
        candidate_source: &str,
        approved_dependency_ids: &[Uuid],
        environment: &str,
        import_manifest: &[String],
    ) -> Result<LeanVerificationResult, String> {
        let start_time = Instant::now();

        // 1. Generate namespace and theorem name
        let namespace_first_16 = &obligation.problem_version_id.to_string().replace("-", "")[..16];
        let obligation_first_16 = &obligation.id.to_string().replace("-", "")[..16];

        let problem_namespace = format!("ChatDB.P_{}", namespace_first_16);
        let theorem_name = format!("O_{}", obligation_first_16);

        // 2. Imports come from the problem's own immutable manifest — never
        // hardcoded here. ALL `import` lines must precede any other command, so
        // dependency imports go before set_option.
        let mut imports = Self::build_import_block(import_manifest, approved_dependency_ids);
        imports.push_str("set_option linter.unusedTactic false\n");
        imports.push_str("set_option linter.unreachableTactic false\n");

        // 3. Construct Lean source code
        // Lean 4.32+ requires the first tactic after `:= by` to be indented
        // relative to the theorem — a proof block at column 0 is parsed as an
        // empty `by` block followed by stray identifiers, failing every proof.
        // normalize_and_indent also fixes issue #41: a naturally-formatted
        // multi-line proof whose lines don't already share one indentation
        // level (e.g. the first tactic flush, the rest indented) was silently
        // reinterpreted by Lean's whitespace-sensitive parser as nesting
        // rather than sequencing — see its doc comment in lean/module.rs.
        let indented_proof = normalize_and_indent(candidate_source);
        let file_content = format!(
            "{}\nnamespace {}\n\ntheorem {} : {} := by\n{}\n\nend {}\n",
            imports,
            problem_namespace,
            theorem_name,
            obligation.lean_statement,
            indented_proof,
            problem_namespace
        );

        // 4/5. Write + run.
        let (proc_success, lines, stderr) = match self.run_lean_json(&file_content, &theorem_name, Duration::from_secs(60)) {
            Ok(v) => v,
            Err(timeout_or_spawn_err) => {
                return Ok(LeanVerificationResult {
                    outcome: LeanVerificationOutcome::KernelFail,
                    attempt_id: Uuid::new_v4(),
                    obligation_id: obligation.id,
                    theorem_name,
                    expected_statement_hash: obligation.statement_hash.clone(),
                    elaborated_statement_hash: None,
                    environment_hash: environment.to_string(),
                    proof_source_hash: "".to_string(),
                    compiled_artifact_hash: None,
                    proof_term_hash: None,
                    diagnostic: Some(LeanDiagnostic {
                        category: LeanDiagnosticCategory::TacticFailure,
                        primary_message: timeout_or_spawn_err.clone(),
                        source_span: None,
                        goal: None,
                        local_context: vec![],
                        unsolved_goals: vec![],
                        used_dependencies: vec![],
                        error_code: None,
                        canonical_goal_hash: None,
                    }),
                    all_diagnostics: vec![],
                    dependency_use_report: None,
                    wall_time_ms: start_time.elapsed().as_millis() as u64,
                    lean_cpu_time_ms: start_time.elapsed().as_millis() as u64,
                });
            }
        };

        // Parse every error-severity (or hasSorry-warning) diagnostic INDEPENDENTLY
        // — never collapsed into one joined string, so e.g. an unknown identifier
        // and a trailing-tactic error are distinguishable categories, not one
        // generic parse failure.
        let mut all_diagnostics: Vec<LeanDiagnostic> = Vec::new();
        let mut has_sorry = false;
        for val in &lines {
            let (msg, kind, severity, _line) = parse_diagnostic_line(val);
            let is_sorry = kind == "hasSorry" || msg.contains("declaration uses `sorry`") || msg.contains("declaration uses 'sorry'");
            if is_sorry {
                has_sorry = true;
            } else if severity != "error" || msg.is_empty() {
                continue;
            }
            all_diagnostics.push(LeanDiagnostic {
                category: categorize(&msg, &kind),
                primary_message: msg,
                source_span: source_span_of(val),
                goal: None,
                local_context: vec![],
                unsolved_goals: vec![],
                used_dependencies: vec![],
                error_code: None,
                canonical_goal_hash: None,
            });
        }

        // SOUNDNESS: `sorry`/`admit` compile with exit code 0 and only a hasSorry
        // WARNING. A proof containing sorryAx proves nothing — it must be a hard
        // rejection, never a KernelPass.
        let success = proc_success && all_diagnostics.is_empty() && !has_sorry;

        let diagnostic = if !success {
            if has_sorry && all_diagnostics.is_empty() {
                Some(LeanDiagnostic {
                    category: LeanDiagnosticCategory::ProhibitedConstruct,
                    primary_message: "declaration uses `sorry`".to_string(),
                    source_span: None,
                    goal: None,
                    local_context: vec![],
                    unsolved_goals: vec![],
                    used_dependencies: vec![],
                    error_code: None,
                    canonical_goal_hash: None,
                })
            } else if let Some(d) = all_diagnostics.first().cloned() {
                Some(d)
            } else if !stderr.trim().is_empty() {
                // Process failed but stdout's --json stream had nothing parseable
                // (e.g. a Lake resolution failure) — surface stderr rather than
                // reporting an unexplained failure with no diagnostic at all.
                Some(LeanDiagnostic {
                    category: LeanDiagnosticCategory::TacticFailure,
                    primary_message: stderr.trim().to_string(),
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
            }
        } else {
            None
        };

        let outcome = if success {
            LeanVerificationOutcome::KernelPass
        } else {
            LeanVerificationOutcome::KernelFail
        };

        // If successful, copy to main project and compile using `lake build` so it's ready for imports
        if success {
            let verified_dir = self.lean_project_path.join("LeanChecker").join("Verified");
            if !verified_dir.exists() {
                let _ = fs::create_dir_all(&verified_dir);
            }
            // The tempfile run_lean_json wrote to is already cleaned up by the
            // time we get here — re-write the same content directly into Verified/.
            let dest_path = verified_dir.join(format!("{}.lean", theorem_name));
            let _ = fs::write(&dest_path, &file_content);

            let lake_path = self.elan_bin_path.join("lake.exe");
            let mut build_cmd = Command::new(&lake_path);
            build_cmd.arg("build")
                .arg(format!("LeanChecker.Verified.{}", theorem_name))
                .current_dir(&self.lean_project_path);
            if let Ok(elan_home) = std::env::var("CHATDB_ELAN_HOME") {
                build_cmd.env("ELAN_HOME", elan_home);
            }
            let _build_lock = LAKE_BUILD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
            let _ = build_cmd.output();
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
            all_diagnostics,
            dependency_use_report: None,
            wall_time_ms,
            lean_cpu_time_ms: wall_time_ms,
        })
    }

    fn verify_module(
        &self,
        assembled: &AssembledModule,
        environment: &str,
    ) -> Result<LeanModuleVerificationResult, String> {
        let start_time = Instant::now();
        // Stem is derived from the source hash so a re-submission of the same
        // module lands on the same Verified/ file, and two different modules never
        // collide. The namespace inside the file is independent of the file name.
        let file_stem = format!("M_{}", &assembled.module_source_hash[..16.min(assembled.module_source_hash.len())]);

        let kernel_result_hash = crate::hashing::canonical_hash(&(
            assembled.module_source_hash.clone(),
            assembled.declaration_manifest_hash.clone(),
        )).unwrap_or_default();

        let mk_fail = |diag: LeanDiagnostic, all: Vec<LeanDiagnostic>, elapsed: u64| LeanModuleVerificationResult {
            outcome: LeanVerificationOutcome::KernelFail,
            problem_namespace: assembled.namespace.clone(),
            root_lean_name: assembled.root_lean_name.clone(),
            module_source_hash: assembled.module_source_hash.clone(),
            declaration_manifest_hash: assembled.declaration_manifest_hash.clone(),
            environment_hash: environment.to_string(),
            kernel_result_hash: kernel_result_hash.clone(),
            diagnostic: Some(diag),
            all_diagnostics: all,
            wall_time_ms: elapsed,
        };

        let (proc_success, lines, stderr) = match self.run_lean_json(&assembled.source, &file_stem, Duration::from_secs(120)) {
            Ok(v) => v,
            Err(timeout_or_spawn_err) => {
                return Ok(mk_fail(
                    LeanDiagnostic {
                        category: LeanDiagnosticCategory::TacticFailure,
                        primary_message: timeout_or_spawn_err,
                        source_span: None, goal: None, local_context: vec![], unsolved_goals: vec![],
                        used_dependencies: vec![], error_code: None, canonical_goal_hash: None,
                    },
                    vec![],
                    start_time.elapsed().as_millis() as u64,
                ));
            }
        };

        // Parse every error / hasSorry diagnostic independently — same policy as
        // verify_exact: a module with sorry/admit compiles (exit 0 + warning) yet
        // proves nothing, so it must be a hard rejection.
        let mut all_diagnostics: Vec<LeanDiagnostic> = Vec::new();
        let mut has_sorry = false;
        for val in &lines {
            let (msg, kind, severity, _line) = parse_diagnostic_line(val);
            let is_sorry = kind == "hasSorry" || msg.contains("declaration uses `sorry`") || msg.contains("declaration uses 'sorry'");
            if is_sorry {
                has_sorry = true;
            } else if severity != "error" || msg.is_empty() {
                continue;
            }
            all_diagnostics.push(LeanDiagnostic {
                category: categorize(&msg, &kind),
                primary_message: msg,
                source_span: source_span_of(val),
                goal: None, local_context: vec![], unsolved_goals: vec![],
                used_dependencies: vec![], error_code: None, canonical_goal_hash: None,
            });
        }

        let success = proc_success && all_diagnostics.is_empty() && !has_sorry;

        if !success {
            let elapsed = start_time.elapsed().as_millis() as u64;
            let diag = if has_sorry && all_diagnostics.is_empty() {
                LeanDiagnostic {
                    category: LeanDiagnosticCategory::ProhibitedConstruct,
                    primary_message: "module uses `sorry`/`admit` — proves nothing".to_string(),
                    source_span: None, goal: None, local_context: vec![], unsolved_goals: vec![],
                    used_dependencies: vec![], error_code: None, canonical_goal_hash: None,
                }
            } else if let Some(d) = all_diagnostics.first().cloned() {
                d
            } else {
                LeanDiagnostic {
                    category: LeanDiagnosticCategory::TacticFailure,
                    primary_message: if stderr.trim().is_empty() { "module verification failed with no diagnostic".to_string() } else { stderr.trim().to_string() },
                    source_span: None, goal: None, local_context: vec![], unsolved_goals: vec![],
                    used_dependencies: vec![], error_code: None, canonical_goal_hash: None,
                }
            };
            return Ok(mk_fail(diag, all_diagnostics, elapsed));
        }

        // Success: write the verified source into Verified/ ONLY now. No partial
        // commit — this line is reached only after the entire module passed.
        let verified_dir = self.lean_project_path.join("LeanChecker").join("Verified");
        if !verified_dir.exists() {
            let _ = fs::create_dir_all(&verified_dir);
        }
        let dest_path = verified_dir.join(format!("{}.lean", file_stem));
        let _ = fs::write(&dest_path, &assembled.source);
        let lake_path = self.elan_bin_path.join("lake.exe");
        let mut build_cmd = Command::new(&lake_path);
        build_cmd.arg("build")
            .arg(format!("LeanChecker.Verified.{}", file_stem))
            .current_dir(&self.lean_project_path);
        if let Ok(elan_home) = std::env::var("CHATDB_ELAN_HOME") {
            build_cmd.env("ELAN_HOME", elan_home);
        }
        let _build_lock = LAKE_BUILD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _ = build_cmd.output();

        Ok(LeanModuleVerificationResult {
            outcome: LeanVerificationOutcome::KernelPass,
            problem_namespace: assembled.namespace.clone(),
            root_lean_name: assembled.root_lean_name.clone(),
            module_source_hash: assembled.module_source_hash.clone(),
            declaration_manifest_hash: assembled.declaration_manifest_hash.clone(),
            environment_hash: environment.to_string(),
            kernel_result_hash,
            diagnostic: None,
            all_diagnostics: vec![],
            wall_time_ms: start_time.elapsed().as_millis() as u64,
        })
    }

    fn validate_import_manifest(&self, imports: &[String]) -> Result<(), String> {
        if imports.is_empty() {
            return Ok(());
        }
        let mut content = String::new();
        for module in imports {
            content.push_str(&format!("import {}\n", module));
        }
        // Validating imports means resolving them, which can itself pull in a
        // large chunk of Mathlib (e.g. NumberTheory modules) — give this more
        // room than the fast declaration-lookup pass, but well under
        // verify_exact's 60s since this only elaborates imports, not a proof.
        let (proc_success, lines, stderr) = self.run_lean_json(&content, "import_probe", Duration::from_secs(45))?;
        let errors: Vec<String> = lines.iter()
            .filter_map(|v| {
                let (msg, _kind, severity, _line) = parse_diagnostic_line(v);
                if severity == "error" && !msg.is_empty() { Some(msg) } else { None }
            })
            .collect();
        if !proc_success || !errors.is_empty() {
            let detail = if !errors.is_empty() {
                errors.join("; ")
            } else if !stderr.trim().is_empty() {
                stderr.trim().to_string()
            } else {
                "process failed with no diagnostic output".to_string()
            };
            return Err(format!(
                "one or more imports failed to resolve under the pinned environment: {}",
                detail
            ));
        }
        Ok(())
    }

    fn lookup_declarations(&self, names: &[String], import_manifest: &[String], deep_check: bool) -> Result<Vec<DeclarationLookupResult>, String> {
        if names.is_empty() {
            return Ok(vec![]);
        }

        // Pass 1: exactly the problem's own import manifest — mirrors what a
        // Solve attempt actually sees. Fast: no full-library load.
        let pass1 = self.check_pass(names, import_manifest, Duration::from_secs(20))?;

        let need_umbrella: Vec<String> = names.iter().enumerate()
            .filter(|(i, _)| !pass1[*i])
            .map(|(_, n)| n.clone())
            .collect();

        if !deep_check || need_umbrella.is_empty() {
            return Ok(names.iter().enumerate().map(|(i, name)| {
                if pass1[i] {
                    DeclarationLookupResult { query: name.clone(), status: DeclarationLookupStatus::Available, diagnostics: vec![] }
                } else {
                    DeclarationLookupResult {
                        query: name.clone(),
                        status: DeclarationLookupStatus::NotAvailableUnderCurrentManifest,
                        diagnostics: vec!["does not resolve under the current import manifest. This does NOT mean the declaration is absent from the pinned library \
                                           — call again with deep_check=true to distinguish 'needs an import' from 'genuinely absent' \
                                           (loads the full Mathlib umbrella; reliably takes 15-40+ seconds)".to_string()],
                    }
                }
            }).collect());
        }

        // deep_check, only for names that failed pass 1: the full Mathlib
        // umbrella. This is what distinguishes "not imported here" from
        // "genuinely absent" — and is the slow path (cold process, full library
        // load) callers must explicitly opt into.
        let umbrella_results = self.check_pass(&need_umbrella, &["Mathlib".to_string()], Duration::from_secs(90))?;
        let pass2: std::collections::HashMap<String, bool> = need_umbrella.into_iter().zip(umbrella_results).collect();

        Ok(names.iter().enumerate().map(|(i, name)| {
            if pass1[i] {
                DeclarationLookupResult { query: name.clone(), status: DeclarationLookupStatus::Available, diagnostics: vec![] }
            } else if pass2.get(name).copied().unwrap_or(false) {
                DeclarationLookupResult {
                    query: name.clone(),
                    status: DeclarationLookupStatus::NotInCurrentImportScope,
                    diagnostics: vec!["resolves under `import Mathlib` but not under the current manifest — add the module that provides it".to_string()],
                }
            } else {
                DeclarationLookupResult {
                    query: name.clone(),
                    status: DeclarationLookupStatus::UnknownDeclaration,
                    diagnostics: vec!["does not resolve even under the full Mathlib umbrella".to_string()],
                }
            }
        }).collect())
    }
}

impl RealLeanGateway {
    /// Checks each name's resolution in ONE compile pass (`#check` per name;
    /// Lean continues past an unresolved `#check` rather than aborting the file),
    /// returning true/false per name in the same order as `names`.
    fn check_pass(&self, names: &[String], imports: &[String], timeout: Duration) -> Result<Vec<bool>, String> {
        let mut content = String::new();
        for module in imports {
            content.push_str(&format!("import {}\n", module));
        }
        content.push('\n');
        let check_start_line = content.matches('\n').count() as i64 + 1; // 1-indexed line of the first #check
        for name in names {
            content.push_str(&format!("#check {}\n", name));
        }

        let check_end_line = check_start_line + names.len() as i64 - 1;
        let (proc_success, lines, stderr) = self.run_lean_json(&content, "decl_lookup", timeout)?;
        let mut failed_lines: std::collections::HashSet<i64> = std::collections::HashSet::new();
        // An error that lands OUTSIDE the #check lines (e.g. a bad import on
        // line 1) is an environment problem, not a per-declaration result — if
        // it were silently ignored, every name would fall through as "no
        // failure recorded" and get reported Available even though none of the
        // #check lines actually ran. That's the false-availability failure mode:
        // a broken environment must never look like a clean resolution.
        let mut environment_errors: Vec<String> = Vec::new();
        for val in &lines {
            let (msg, _kind, severity, line) = parse_diagnostic_line(val);
            if severity == "error" && !msg.is_empty() {
                match line {
                    Some(l) if l >= check_start_line && l <= check_end_line => {
                        failed_lines.insert(l);
                    }
                    _ => environment_errors.push(msg),
                }
            }
        }
        if !environment_errors.is_empty() {
            return Err(format!(
                "declaration lookup environment failed (error outside the #check lines, likely a bad import): {}",
                environment_errors.join("; ")
            ));
        }
        // The process can legitimately exit non-zero purely because one or more
        // #check lines failed (an unresolved name IS an error) — that's the
        // normal per-name failure path above, not an environment problem. But if
        // it failed AND produced no diagnostics we could attribute to anything —
        // no #check failures, no environment errors — there's nothing to
        // distinguish "everything resolved" from "the process crashed before
        // producing output"; don't guess "Available" in that case.
        if !proc_success && failed_lines.is_empty() && environment_errors.is_empty() {
            let detail = if !stderr.trim().is_empty() { stderr.trim().to_string() } else { "process failed with no parseable diagnostics".to_string() };
            return Err(format!("declaration lookup environment failed: {}", detail));
        }
        Ok((0..names.len() as i64)
            .map(|i| !failed_lines.contains(&(check_start_line + i)))
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{Obligation, ObligationKind, ObligationCreator, ObligationStatus};
    use chrono::Utc;
    use std::path::PathBuf;

    fn default_manifest() -> Vec<String> {
        vec!["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()]
    }

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
        let res = gateway.verify_exact(&obligation, "rfl", &[], "envhash", &default_manifest());
        if let Ok(res_val) = res {
            assert!(matches!(res_val.outcome, LeanVerificationOutcome::KernelFail));
        }
    }

    /// THE CORE OF THE FIX: an unresolved name must categorize as
    /// UnknownDeclaration, never as the generic ParseError it was lumped into
    /// before — those are different claims (name resolution vs. syntax) and
    /// conflating them is exactly what let a model claim "the library lacks this
    /// capability" from what was actually a syntax-shaped error path.
    #[test]
    fn test_unknown_identifier_is_not_categorized_as_parse_error() {
        assert_eq!(categorize("unknown identifier 'Nat.factorization'", ""), LeanDiagnosticCategory::UnknownDeclaration);
        assert_eq!(categorize("unknown constant 'Foo.bar'", ""), LeanDiagnosticCategory::UnknownDeclaration);
        assert_eq!(categorize("unknown namespace 'Foo'", ""), LeanDiagnosticCategory::UnknownDeclaration);
    }

    /// The staging trust boundary: a module that fails verification must NEVER
    /// write to LeanChecker/Verified. Here the gateway can't even spawn lake (bogus
    /// elan path), so verify_module returns KernelFail — and the Verified/ tree must
    /// be untouched. No partial commit.
    #[test]
    fn verify_module_does_not_write_on_failure() {
        use crate::models::action::ModuleTheorem;
        let tmp = tempfile::tempdir().unwrap();
        let lean_project = tmp.path().to_path_buf();
        let gateway = RealLeanGateway::new(lean_project.clone(), PathBuf::from("Z:\\definitely\\nonexistent\\bin"));

        let stmt = "1 + 1 = 2";
        let root_hash = crate::hashing::canonical_hash(&stmt.to_string()).unwrap();
        let root = ModuleTheorem { name: "r".to_string(), statement: stmt.to_string(), proof_term: "norm_num".to_string() };
        let asm = module::assemble_module("ChatDB.P_test", &root_hash, &[], &root, &default_manifest()).unwrap();

        let res = gateway.verify_module(&asm, "envhash").unwrap();
        assert!(matches!(res.outcome, LeanVerificationOutcome::KernelFail), "a gateway that can't run Lean must fail closed");

        let verified = lean_project.join("LeanChecker").join("Verified");
        let wrote_any = verified.exists()
            && std::fs::read_dir(&verified).map(|mut d| d.next().is_some()).unwrap_or(false);
        assert!(!wrote_any, "a failed module must not write any artifact to LeanChecker/Verified");
    }

    #[test]
    fn test_diagnostic_categories_stay_distinct() {
        assert_eq!(categorize("type mismatch, term has type...", ""), LeanDiagnosticCategory::TypeMismatch);
        assert_eq!(categorize("unsolved goals\n⊢ True", ""), LeanDiagnosticCategory::UnsolvedGoals);
        assert_eq!(categorize("expected ';' or line break", ""), LeanDiagnosticCategory::ParseError);
        assert_eq!(categorize("declaration uses `sorry`", "hasSorry"), LeanDiagnosticCategory::ProhibitedConstruct);
        assert_eq!(categorize("no goals", ""), LeanDiagnosticCategory::TacticFailure);
    }
}
