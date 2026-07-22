use std::fs;
use std::collections::HashSet;
use std::io::{BufRead, BufReader, Read, Write};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use std::path::PathBuf;
use std::sync::{Condvar, LazyLock, Mutex};
use crate::models::{
    Obligation, LeanVerificationResult, LeanVerificationOutcome, LeanDiagnostic, LeanDiagnosticCategory,
    DeclarationLookupResult, DeclarationLookupStatus, LeanModuleVerificationResult,
    DurabilityJobReceipt, VerificationPolicyReceipt, VerifierOutputReceipt, VerifierResourcePolicy,
};
use uuid::Uuid;

pub mod module;
use module::{AssembledModule, normalize_proof};
use crate::models::action::ProofFormat;

/// Interactive (tactic-by-tactic) proof-state sessions — issue #159. Additive
/// and separate from `LeanGateway`: see `interactive`'s module doc for the
/// trust-boundary rule (results there are search evidence, never proof
/// authority) and for why Pantograph is an optional future backend, not the
/// API surface itself.
pub mod interactive;

/// Canonical observation data model for interactive proof-state sessions —
/// issue #162. Separate module from `interactive` because #159's module is
/// about the LIVE session trait/backends and #162 is about the STORED,
/// hashed, MCP-schema'd shape those live results get formalized into for
/// `proof_session_observe` / `proof_session_tactic_step` (not implemented in
/// this module — this module defines the data they will return). See
/// `observation`'s module doc for the hashing rules and the trust-boundary
/// reminder (still search evidence, never proof authority).
pub mod observation;

/// Interactive-independent: issue #220's asynchronous verifier-job engine. It is
/// pure transport over the SAME `verify_exact` this trait already exposes — a
/// submitted job produces exactly the result the synchronous path would. See the
/// module doc for the file-based persistence and trust-boundary rules.
pub mod verification;

pub trait LeanGateway {
    fn verify_exact(
        &self,
        obligation: &Obligation,
        candidate_source: &str,
        approved_dependency_ids: &[Uuid],
        environment: &str,
        import_manifest: &[String],
        proof_format: ProofFormat,
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

    /// Issue #245: ELABORATE a formal statement under the pinned environment and
    /// return its normalized structural fingerprint (conclusion head, binder
    /// count, hypothesis head multiset, used-constant set). Read-only — changes no
    /// proof state and no imports. Default fails closed: a gateway that can't run
    /// Lean must never fabricate an elaborated fingerprint.
    fn structural_fingerprint(&self, _statement: &str) -> Result<serde_json::Value, String> {
        Err("this gateway cannot elaborate structural fingerprints".to_string())
    }

    /// Issue #245: bulk-fingerprint the pinned Mathlib library in ONE process,
    /// returning the harness stdout (one `FP:{json}` line per theorem). `limit`
    /// caps the count (0 = whole library — minutes). Read-only. Default fails
    /// closed.
    fn mathlib_fingerprint_index(&self, _limit: usize) -> Result<String, String> {
        Err("this gateway cannot build a Mathlib fingerprint index".to_string())
    }

    /// Effective server-owned resource policy, when the gateway executes real
    /// verifier subprocesses. Test/search-only gateways return `None`.
    fn resource_policy(&self) -> Option<VerifierResourcePolicy> {
        None
    }

    fn durability_job_status(&self, _job_id: &str) -> Result<serde_json::Value, String> {
        Err("this gateway does not support durability jobs".to_string())
    }

    fn durability_job_retry(&self, _job_id: &str) -> Result<DurabilityJobReceipt, String> {
        Err("this gateway does not support durability jobs".to_string())
    }

    // -- Issue #220: asynchronous verifier jobs ---------------------------
    //
    // An ADDITIVE transport path over this same trait's `verify_exact`: submit
    // returns a durable job id immediately, then status/result/cancel/events run
    // across separate requests while the verifier works on its own thread.
    // Defaults fail closed for the same reason the durability ones do — a
    // gateway that cannot actually run Lean must never pretend to run a job.

    /// Launches an asynchronous verification job and returns immediately with a
    /// durable receipt (job id + source/environment hashes + queued state), never
    /// a verdict. Reuses an identical completed job when one already exists.
    fn verification_submit(
        &self,
        _request: verification::VerificationJobRequest,
    ) -> Result<crate::models::VerificationJobReceipt, String> {
        Err("this gateway does not support asynchronous verification jobs".to_string())
    }

    /// Lightweight polling metadata for a job — phase, timestamps, heartbeat,
    /// hashes, cancellation state, and `result_artifact_hash` once complete —
    /// never the full result payload.
    fn verification_status(&self, _job_id: &str) -> Result<serde_json::Value, String> {
        Err("this gateway does not support asynchronous verification jobs".to_string())
    }

    /// The full verification payload for a completed/failed job. The only action
    /// that returns the heavy result; `verification_status` never does.
    fn verification_result(&self, _job_id: &str) -> Result<serde_json::Value, String> {
        Err("this gateway does not support asynchronous verification jobs".to_string())
    }

    /// Cancels a job and terminates the complete subprocess tree of any live
    /// verifier run for it; a terminal job is a no-op.
    fn verification_cancel(&self, _job_id: &str) -> Result<serde_json::Value, String> {
        Err("this gateway does not support asynchronous verification jobs".to_string())
    }

    /// The ordered phase-transition history for a job.
    fn verification_events(&self, _job_id: &str) -> Result<serde_json::Value, String> {
        Err("this gateway does not support asynchronous verification jobs".to_string())
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
static PROCESS_LIMITER: LazyLock<ProcessLimiter> = LazyLock::new(ProcessLimiter::default);
static ACTIVE_VERIFIER_PIDS: LazyLock<Mutex<HashSet<u32>>> = LazyLock::new(|| Mutex::new(HashSet::new()));
static DURABILITY_STATE_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));
#[cfg(not(test))]
const PROCESS_CLEANUP_GRACE: Duration = Duration::from_secs(2);
#[cfg(test)]
const PROCESS_CLEANUP_GRACE: Duration = Duration::from_millis(200);

const MAX_TIMEOUT_MS: u64 = 3_600_000;
const MAX_SOURCE_BYTES: usize = 16 * 1024 * 1024;
const MAX_OUTPUT_BYTES: usize = 16 * 1024 * 1024;
const MAX_DIAGNOSTICS: usize = 10_000;
const MAX_CONCURRENT_PROCESSES: usize = 64;

impl Default for VerifierResourcePolicy {
    fn default() -> Self {
        Self {
            proof_timeout_ms: 300_000,
            module_timeout_ms: 1_800_000,
            import_validation_timeout_ms: 600_000,
            declaration_lookup_timeout_ms: 60_000,
            deep_declaration_lookup_timeout_ms: 300_000,
            durability_build_timeout_ms: 600_000,
            max_source_bytes: 4 * 1024 * 1024,
            max_output_bytes: 4 * 1024 * 1024,
            max_diagnostics: 1_000,
            max_concurrent_processes: 4,
        }
    }
}

impl VerifierResourcePolicy {
    /// Reads operator configuration. Invalid, zero, or over-ceiling values are
    /// rejected instead of silently becoming unlimited.
    pub fn from_env() -> Result<Self, String> {
        Self::from_lookup(|name| std::env::var(name).ok())
    }

    fn from_lookup(mut lookup: impl FnMut(&str) -> Option<String>) -> Result<Self, String> {
        let mut p = Self::default();
        p.proof_timeout_ms = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_PROOF_TIMEOUT_MS", p.proof_timeout_ms, MAX_TIMEOUT_MS)?;
        p.module_timeout_ms = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_MODULE_TIMEOUT_MS", p.module_timeout_ms, MAX_TIMEOUT_MS)?;
        p.import_validation_timeout_ms = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_IMPORT_TIMEOUT_MS", p.import_validation_timeout_ms, MAX_TIMEOUT_MS)?;
        p.declaration_lookup_timeout_ms = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_LOOKUP_TIMEOUT_MS", p.declaration_lookup_timeout_ms, MAX_TIMEOUT_MS)?;
        p.deep_declaration_lookup_timeout_ms = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_DEEP_LOOKUP_TIMEOUT_MS", p.deep_declaration_lookup_timeout_ms, MAX_TIMEOUT_MS)?;
        p.durability_build_timeout_ms = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_BUILD_TIMEOUT_MS", p.durability_build_timeout_ms, MAX_TIMEOUT_MS)?;
        p.max_source_bytes = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_MAX_SOURCE_BYTES", p.max_source_bytes as u64, MAX_SOURCE_BYTES as u64)? as usize;
        p.max_output_bytes = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_MAX_OUTPUT_BYTES", p.max_output_bytes as u64, MAX_OUTPUT_BYTES as u64)? as usize;
        p.max_diagnostics = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_MAX_DIAGNOSTICS", p.max_diagnostics as u64, MAX_DIAGNOSTICS as u64)? as usize;
        p.max_concurrent_processes = configured_limit(&mut lookup, "PROOFSEARCH_VERIFY_MAX_CONCURRENT_PROCESSES", p.max_concurrent_processes as u64, MAX_CONCURRENT_PROCESSES as u64)? as usize;
        if p.max_diagnostics < 3 {
            return Err("PROOFSEARCH_VERIFY_MAX_DIAGNOSTICS must be at least 3 so first, last, and prohibited-construct diagnostics can all be retained".to_string());
        }
        Ok(p)
    }

    pub fn receipt(&self) -> VerificationPolicyReceipt {
        VerificationPolicyReceipt {
            requested: self.clone(),
            effective: self.clone(),
            policy_hash: crate::hashing::canonical_hash(self).unwrap_or_default(),
        }
    }
}

fn configured_limit(
    lookup: &mut impl FnMut(&str) -> Option<String>,
    name: &str,
    default: u64,
    ceiling: u64,
) -> Result<u64, String> {
    let Some(raw) = lookup(name) else { return Ok(default) };
    let value = raw.parse::<u64>().map_err(|_| format!("{name} must be a positive integer, got {raw:?}"))?;
    if value == 0 || value > ceiling {
        return Err(format!("{name} must be between 1 and {ceiling}, got {value}"));
    }
    Ok(value)
}

#[derive(Default)]
struct ProcessLimiter {
    active: Mutex<usize>,
    changed: Condvar,
}

struct ProcessPermit<'a> {
    limiter: &'a ProcessLimiter,
}

fn wait_for_status_with_timeout(
    mut child: std::process::Child,
    timeout: Duration,
) -> Result<std::process::ExitStatus, String> {
    let (tx, rx) = std::sync::mpsc::channel();
    let pid = child.id();
    ACTIVE_VERIFIER_PIDS.lock().unwrap_or_else(|e| e.into_inner()).insert(pid);
    struct ActivePidGuard(u32);
    impl Drop for ActivePidGuard {
        fn drop(&mut self) {
            ACTIVE_VERIFIER_PIDS.lock().unwrap_or_else(|e| e.into_inner()).remove(&self.0);
        }
    }
    let _active = ActivePidGuard(pid);
    // Issue #220: if this verifier subprocess is running under an asynchronous
    // verification job (thread-local set by that job's worker), attribute its pid
    // to the job so `verification_cancel` can kill exactly this job's process
    // tree — never another job's. This is None on the synchronous `episode_step`
    // path, which is therefore entirely unaffected.
    struct JobPidGuard(Option<String>, u32);
    impl Drop for JobPidGuard {
        fn drop(&mut self) {
            if let Some(job) = &self.0 {
                verification::deregister_job_pid(job, self.1);
            }
        }
    }
    let job_ctx = verification::current_job();
    if let Some(job) = &job_ctx {
        verification::register_job_pid(job, pid);
    }
    let _job_pid = JobPidGuard(job_ctx, pid);
    std::thread::spawn(move || {
        let res = child.wait();
        let _ = tx.send(res);
    });
    match rx.recv_timeout(timeout) {
        Ok(Ok(out)) => Ok(out),
        Ok(Err(e)) => Err(format!("Process error: {e}")),
        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
            Err("verifier wait thread disconnected before reporting process status".to_string())
        }
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
            let graceful = terminate_process_tree(pid, false);
            if let Ok(waited) = rx.recv_timeout(PROCESS_CLEANUP_GRACE) {
                return match waited {
                    Ok(status) => Err(format!(
                        "Lean invocation timed out after {} ms; termination_method={}; cleanup=reaped; exit_status={status}",
                        timeout.as_millis(), graceful,
                    )),
                    Err(e) => Err(format!("Lean invocation timed out; cleanup wait failed: {e}")),
                };
            }
            let forced = terminate_process_tree(pid, true);
            match rx.recv_timeout(PROCESS_CLEANUP_GRACE) {
                Ok(Ok(status)) => Err(format!(
                    "Lean invocation timed out after {} ms; termination_method={graceful}->{forced}; cleanup=reaped; exit_status={status}",
                    timeout.as_millis(),
                )),
                Ok(Err(e)) => Err(format!("Lean invocation timed out; forced cleanup wait failed: {e}")),
                Err(_) => Err(format!(
                    "infrastructure integrity error: verifier process tree {pid} was not reaped after timeout; termination_method={graceful}->{forced}; cleanup=failed"
                )),
            }
        }
    }
}

#[cfg(target_os = "windows")]
fn configure_process_containment(_command: &mut Command) {}

#[cfg(unix)]
fn configure_process_containment(command: &mut Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

#[cfg(target_os = "windows")]
fn terminate_process_tree(pid: u32, force: bool) -> String {
    let mut command = Command::new("taskkill");
    if force { command.arg("/F"); }
    let status = command.arg("/T").arg("/PID").arg(pid.to_string())
        .stdout(Stdio::null()).stderr(Stdio::null()).status();
    format!("taskkill_tree_{}({})", if force { "force" } else { "graceful" },
        status.map(|s| s.to_string()).unwrap_or_else(|e| format!("spawn_error:{e}")))
}

#[cfg(unix)]
fn terminate_process_tree(pid: u32, force: bool) -> String {
    let signal = if force { "-KILL" } else { "-TERM" };
    let status = Command::new("kill").arg(signal).arg("--").arg(format!("-{pid}"))
        .stdout(Stdio::null()).stderr(Stdio::null()).status();
    format!("process_group_{signal}({})",
        status.map(|s| s.to_string()).unwrap_or_else(|e| format!("spawn_error:{e}")))
}

/// Issue #220: crate-internal accessor so `verification::cancel` can kill the
/// complete process tree of a job's live verifier subprocess, reusing the exact
/// same `taskkill /F /T` (Windows) / process-group signal (unix) mechanism the
/// timeout path uses — never a second, divergent kill implementation.
pub(crate) fn kill_verifier_process_tree(pid: u32, force: bool) -> String {
    terminate_process_tree(pid, force)
}

/// Terminates all registered verifier trees during server shutdown and waits
/// a bounded interval for their owning waiters to reap the direct children.
pub fn terminate_active_verifier_processes() -> Result<(), String> {
    let pids: Vec<u32> = ACTIVE_VERIFIER_PIDS.lock().unwrap_or_else(|e| e.into_inner()).iter().copied().collect();
    for pid in &pids { terminate_process_tree(*pid, false); }
    let start = Instant::now();
    while start.elapsed() < PROCESS_CLEANUP_GRACE {
        if ACTIVE_VERIFIER_PIDS.lock().unwrap_or_else(|e| e.into_inner()).is_empty() { return Ok(()) }
        std::thread::sleep(Duration::from_millis(10));
    }
    let remaining: Vec<u32> = ACTIVE_VERIFIER_PIDS.lock().unwrap_or_else(|e| e.into_inner()).iter().copied().collect();
    for pid in &remaining { terminate_process_tree(*pid, true); }
    let force_start = Instant::now();
    while force_start.elapsed() < PROCESS_CLEANUP_GRACE {
        if ACTIVE_VERIFIER_PIDS.lock().unwrap_or_else(|e| e.into_inner()).is_empty() { return Ok(()) }
        std::thread::sleep(Duration::from_millis(10));
    }
    Err(format!("infrastructure integrity error: failed to reap verifier process trees during shutdown: {remaining:?}"))
}

struct CapturedStream {
    retained: Vec<u8>,
    total_bytes: u64,
    raw: tempfile::NamedTempFile,
}

fn capture_stream(mut reader: impl Read, limit: usize) -> std::io::Result<CapturedStream> {
    let mut retained = Vec::with_capacity(limit.min(64 * 1024));
    let mut raw = tempfile::NamedTempFile::new()?;
    let mut total_bytes = 0_u64;
    let mut buffer = [0_u8; 8192];
    loop {
        let read = reader.read(&mut buffer)?;
        if read == 0 { break }
        raw.write_all(&buffer[..read])?;
        total_bytes += read as u64;
        let remaining = limit.saturating_sub(retained.len());
        retained.extend_from_slice(&buffer[..read.min(remaining)]);
        // Continue draining after the retention limit so a noisy child cannot
        // block on a full OS pipe, while verifier memory remains bounded.
    }
    raw.flush()?;
    Ok(CapturedStream { retained, total_bytes, raw })
}

fn parse_lean_json_file(path: &std::path::Path, limit: usize) -> Result<(Vec<serde_json::Value>, u64), String> {
    let file = fs::File::open(path).map_err(|e| e.to_string())?;
    let mut reader = BufReader::new(file);
    let mut raw_line = Vec::new();
    let mut first: Option<serde_json::Value> = None;
    let mut middle = Vec::new();
    let mut last: Option<serde_json::Value> = None;
    let mut sorry: Option<serde_json::Value> = None;
    let mut total = 0_u64;
    loop {
        raw_line.clear();
        let read = reader.read_until(b'\n', &mut raw_line).map_err(|e| e.to_string())?;
        if read == 0 { break }
        let Ok(value) = serde_json::from_slice::<serde_json::Value>(&raw_line) else { continue };
        total += 1;
        if first.is_none() { first = Some(value.clone()); }
        let (message, kind, _, _) = parse_diagnostic_line(&value);
        if kind == "hasSorry" || message.contains("declaration uses `sorry`") || message.contains("declaration uses 'sorry'") {
            sorry = Some(value.clone());
        }
        if middle.len() < limit.saturating_sub(3) { middle.push(value.clone()); }
        last = Some(value);
    }
    let mut retained = Vec::new();
    for value in first.into_iter().chain(middle).chain(sorry).chain(last) {
        if retained.len() >= limit { break }
        if !retained.iter().any(|existing| existing == &value) { retained.push(value); }
    }
    Ok((retained, total))
}

/// Version of the elaborated structural-fingerprint representation (#245).
/// Bumped whenever the harness or the recorded fields change, so an index record
/// can be invalidated/namespaced by (toolchain, fingerprint_version).
pub const STRUCTURAL_FINGERPRINT_VERSION: &str = "structural_fp/1.0";

/// The Lean meta-program that ELABORATES a term and prints its normalized
/// structural fingerprint (issue #245) — head symbols, binder count, hypothesis
/// head multiset, and the used-constant set. This is real elaboration under the
/// pinned environment, never a parser approximation.
const FP_HARNESS_PREAMBLE: &str = r##"import Mathlib
open Lean Elab Meta

private def _fpConstHeads (e : Expr) : NameSet := Id.run do
  let mut s : NameSet := {}
  for c in e.getUsedConstants do s := s.insert c
  return s

private def _fpFingerprint (e : Expr) : MetaM Json := do
  let e ← instantiateMVars e
  forallTelescopeReducing e fun xs concl => do
    let binderCount := xs.size
    let conclHeadName := match concl.getAppFn.constName? with | some n => n.toString | none => "«nonconst»"
    let consts := (_fpConstHeads e).toList.map (·.toString)
    let hypHeads ← xs.mapM fun x => do
      let t ← inferType x
      pure (match t.getAppFn.constName? with | some n => n.toString | none => "«var»")
    pure <| Json.mkObj [
      ("binder_count", Json.num binderCount),
      ("conclusion_head", Json.str conclHeadName),
      ("hypothesis_heads", Json.arr (hypHeads.map Json.str)),
      ("constants", Json.arr (consts.toArray.map Json.str))
    ]

elab "#fingerprint " t:term : command => Command.liftTermElabM do
  let e ← Term.elabTerm t none
  let j ← _fpFingerprint e
  IO.println s!"FINGERPRINT:{j.compress}"
"##;

/// Version of the Mathlib structural-signature index (#245). Each entry stores a
/// binder count + conclusion head + hypothesis-head multiset (NOT the full
/// constant set — that would be prohibitive at Mathlib scale); the exact-match key
/// is a `signature_hash` over those three fields.
pub const MATHLIB_FINGERPRINT_INDEX_VERSION: &str = "mathlib_fp_index/1.0";

/// The Lean meta-program that BULK-fingerprints every Mathlib theorem in ONE
/// process (issue #245): it iterates `(← getEnv).constants`, and for each
/// non-internal theorem elaborates its type and prints one `FP:{json}` line
/// (name, binder count, conclusion head, hypothesis-head multiset). `LIMIT_N`
/// caps the count for a fast verification run; 0 means the whole library.
const MATHLIB_FP_HARNESS: &str = r##"import Mathlib
open Lean Elab Meta

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let limit := LIMIT_N
  let mut n := 0
  for (nm, ci) in env.constants.toList do
    if limit != 0 && n >= limit then break
    if ci.isUnsafe then continue
    if nm.isInternal then continue
    match ci with
    | .thmInfo _ =>
      let res ← (do try
          let r ← forallTelescopeReducing ci.type fun xs concl => do
            let ch := match concl.getAppFn.constName? with | some c => c.toString | none => "«nonconst»"
            let hyps ← xs.mapM fun x => do
              let t ← inferType x
              pure (match t.getAppFn.constName? with | some c => c.toString | none => "«var»")
            pure (Json.mkObj [("name", Json.str nm.toString), ("binder_count", Json.num xs.size),
                              ("conclusion_head", Json.str ch), ("hypothesis_heads", Json.arr (hyps.map Json.str))])
          pure (some r.compress)
        catch _ => pure none)
      match res with
      | some s => n := n + 1; IO.println s!"FP:{s}"
      | none => pure ()
    | _ => pure ()
  IO.println s!"FPDONE:{n}"
"##;

/// Run the bulk Mathlib fingerprint harness (#245) in one Lean process and return
/// its raw stdout (one `FP:{json}` line per theorem, ending `FPDONE:{count}`).
/// `limit` caps the number of theorems (0 = the whole library — minutes). The
/// caller parses the lines and computes each signature hash. Read-only.
pub fn run_mathlib_fingerprint_harness(
    lean_project_path: &std::path::Path,
    elan_bin_path: &std::path::Path,
    limit: usize,
    timeout: Duration,
) -> Result<String, String> {
    let harness = MATHLIB_FP_HARNESS.replace("LIMIT_N", &limit.to_string());
    let temp_dir = tempfile::tempdir().map_err(|e| e.to_string())?;
    let file_path = temp_dir.path().join("_mathlib_fp.lean");
    fs::write(&file_path, &harness).map_err(|e| e.to_string())?;
    let lake_path = elan_bin_path.join("lake.exe");
    let mut cmd = Command::new(&lake_path);
    cmd.arg("env").arg("lean").arg(&file_path)
        .current_dir(lean_project_path)
        .stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Ok(elan_home) = std::env::var("PROOFSEARCH_ELAN_HOME") {
        cmd.env("ELAN_HOME", elan_home);
    }
    configure_process_containment(&mut cmd);
    let mut child = cmd.spawn().map_err(|e| format!("spawn lean: {e}"))?;
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait().map_err(|e| e.to_string())? {
            Some(_) => break,
            None => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    return Err(format!("mathlib fingerprint harness timed out after {:?}", timeout));
                }
                std::thread::sleep(Duration::from_millis(200));
            }
        }
    }
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    if !stdout.contains("FPDONE:") {
        return Err(format!("harness did not complete: stderr={}",
            String::from_utf8_lossy(&out.stderr).chars().take(800).collect::<String>()));
    }
    Ok(stdout)
}

/// Compute the elaborated structural fingerprint of a formal `statement` (#245)
/// under the pinned Lean environment (imports the Mathlib umbrella so any symbol
/// resolves). Returns the fingerprint JSON with `constants` and `hypothesis_heads`
/// sorted for a stable, canonical representation, plus a `binder_count` and
/// `conclusion_head`. `Err` when the statement doesn't elaborate. This is
/// read-only: it changes no proof state and no imports.
pub fn compute_structural_fingerprint(
    lean_project_path: &std::path::Path,
    elan_bin_path: &std::path::Path,
    statement: &str,
    timeout: Duration,
) -> Result<serde_json::Value, String> {
    let harness = format!("{}\n#fingerprint ({})\n", FP_HARNESS_PREAMBLE, statement);
    let temp_dir = tempfile::tempdir().map_err(|e| e.to_string())?;
    let file_path = temp_dir.path().join("_fp_probe.lean");
    fs::write(&file_path, &harness).map_err(|e| e.to_string())?;

    let lake_path = elan_bin_path.join("lake.exe");
    let mut cmd = Command::new(&lake_path);
    cmd.arg("env").arg("lean").arg(&file_path)
        .current_dir(lean_project_path)
        .stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Ok(elan_home) = std::env::var("PROOFSEARCH_ELAN_HOME") {
        cmd.env("ELAN_HOME", elan_home);
    }
    configure_process_containment(&mut cmd);

    let mut child = cmd.spawn().map_err(|e| format!("spawn lean: {e}"))?;
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait().map_err(|e| e.to_string())? {
            Some(_) => break,
            None => {
                if Instant::now() >= deadline {
                    let _ = child.kill();
                    return Err(format!("fingerprint elaboration timed out after {:?}", timeout));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    }
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    for line in stdout.lines() {
        if let Some(js) = line.strip_prefix("FINGERPRINT:") {
            let mut v: serde_json::Value = serde_json::from_str(js.trim())
                .map_err(|e| format!("bad fingerprint json: {e}"))?;
            // Canonicalize: sort the constant set and hypothesis-head multiset so
            // exact-type equality is order-independent.
            if let Some(arr) = v.get_mut("constants").and_then(|c| c.as_array_mut()) {
                arr.sort_by(|a, b| a.as_str().unwrap_or("").cmp(b.as_str().unwrap_or("")));
            }
            if let Some(arr) = v.get_mut("hypothesis_heads").and_then(|c| c.as_array_mut()) {
                arr.sort_by(|a, b| a.as_str().unwrap_or("").cmp(b.as_str().unwrap_or("")));
            }
            return Ok(v);
        }
    }
    Err(format!(
        "no fingerprint produced (statement failed to elaborate?): stderr={}",
        String::from_utf8_lossy(&out.stderr).chars().take(600).collect::<String>()
    ))
}

fn persist_verifier_output(
    root: &std::path::Path,
    stdout: &CapturedStream,
    stderr: &CapturedStream,
    total_diagnostics: u64,
    retained_diagnostics: u64,
) -> Result<VerifierOutputReceipt, String> {
    use sha2::{Digest, Sha256};
    let dir = root.join(".proofsearch").join("artifacts").join("sha256");
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let mut staged = tempfile::NamedTempFile::new_in(&dir).map_err(|e| e.to_string())?;
    let header = format!("PSVERIFIERLOG1\nstdout-bytes:{}\nstderr-bytes:{}\n\n", stdout.total_bytes, stderr.total_bytes);
    let mut hasher = Sha256::new();
    staged.write_all(header.as_bytes()).map_err(|e| e.to_string())?;
    hasher.update(header.as_bytes());
    for source in [stdout.raw.path(), stderr.raw.path()] {
        let mut file = fs::File::open(source).map_err(|e| e.to_string())?;
        let mut buffer = [0_u8; 64 * 1024];
        loop {
            let read = file.read(&mut buffer).map_err(|e| e.to_string())?;
            if read == 0 { break }
            staged.write_all(&buffer[..read]).map_err(|e| e.to_string())?;
            hasher.update(&buffer[..read]);
        }
    }
    staged.flush().map_err(|e| e.to_string())?;
    let hex_hash = hex::encode(hasher.finalize());
    let artifact_hash = format!("sha256:{hex_hash}");
    let final_path = dir.join(format!("{hex_hash}.bin"));
    if !final_path.exists() {
        match staged.persist_noclobber(&final_path) {
            Ok(_) => {}
            Err(error) if final_path.exists() => { drop(error.file); }
            Err(error) => return Err(error.error.to_string()),
        }
    }
    let artifact_size = fs::metadata(&final_path).map_err(|e| e.to_string())?.len();
    let sidecar = serde_json::json!({
        "artifact_hash": artifact_hash,
        "media_type": "application/vnd.proofsearch.verifier-log",
        "byte_size": artifact_size,
        "creator": "lean_gateway",
        "created_at": chrono::Utc::now().to_rfc3339()
    });
    let sidecar_path = dir.join(format!("{hex_hash}.json"));
    if !sidecar_path.exists() {
        fs::write(&sidecar_path, serde_json::to_vec(&sidecar).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    }
    let raw_bytes = stdout.total_bytes + stderr.total_bytes;
    let retained_bytes = stdout.retained.len() as u64 + stderr.retained.len() as u64;
    Ok(VerifierOutputReceipt {
        artifact_hash,
        media_type: "application/vnd.proofsearch.verifier-log".to_string(),
        total_bytes: raw_bytes,
        stdout_bytes: stdout.total_bytes,
        stderr_bytes: stderr.total_bytes,
        retained_stdout_bytes: stdout.retained.len() as u64,
        retained_stderr_bytes: stderr.retained.len() as u64,
        truncated_bytes: raw_bytes.saturating_sub(retained_bytes),
        total_diagnostics,
        retained_diagnostics,
    })
}

struct LeanInvocationFailure {
    message: String,
    output_receipt: Option<VerifierOutputReceipt>,
}

impl std::fmt::Display for LeanInvocationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(receipt) = &self.output_receipt { write!(f, "; raw_output_artifact_hash={}", receipt.artifact_hash)?; }
        Ok(())
    }
}

impl Drop for ProcessPermit<'_> {
    fn drop(&mut self) {
        let mut active = self.limiter.active.lock().unwrap_or_else(|e| e.into_inner());
        *active -= 1;
        self.limiter.changed.notify_one();
    }
}

impl ProcessLimiter {
    fn acquire(&self, limit: usize) -> ProcessPermit<'_> {
        let mut active = self.active.lock().unwrap_or_else(|e| e.into_inner());
        while *active >= limit {
            active = self.changed.wait(active).unwrap_or_else(|e| e.into_inner());
        }
        *active += 1;
        ProcessPermit { limiter: self }
    }
}

pub struct RealLeanGateway {
    pub lean_project_path: PathBuf,
    pub elan_bin_path: PathBuf,
    pub resource_policy: VerifierResourcePolicy,
}

impl RealLeanGateway {
    pub fn new(lean_project_path: PathBuf, elan_bin_path: PathBuf) -> Self {
        Self::with_resource_policy(lean_project_path, elan_bin_path, VerifierResourcePolicy::default())
    }

    pub fn with_resource_policy(lean_project_path: PathBuf, elan_bin_path: PathBuf, resource_policy: VerifierResourcePolicy) -> Self {
        Self { lean_project_path, elan_bin_path, resource_policy }
    }

    /// Writes `file_content` to a temp file and runs `lake env lean --json` on it,
    /// returning the process's overall success, every parsed JSON diagnostic
    /// line, and raw stderr (Lake resolution/build failures land there, not in
    /// the `--json` stdout stream, so silently dropping it hides the actual
    /// cause of an otherwise-unexplained process failure). `Err` here means the
    /// invocation itself failed (spawn error or timeout) — not that Lean
    /// reported errors within the file, which is a normal, successful run that
    /// the caller inspects via the returned lines.
    fn run_lean_json(&self, file_content: &str, file_stem: &str, timeout: Duration) -> Result<(bool, Vec<serde_json::Value>, String, VerifierOutputReceipt), LeanInvocationFailure> {
        if file_content.len() > self.resource_policy.max_source_bytes {
            return Err(LeanInvocationFailure { message: format!("verifier source exceeds effective limit: {} > {} bytes", file_content.len(), self.resource_policy.max_source_bytes), output_receipt: None });
        }
        let _permit = PROCESS_LIMITER.acquire(self.resource_policy.max_concurrent_processes);
        let fail = |message: String| LeanInvocationFailure { message, output_receipt: None };
        let temp_dir = tempfile::tempdir().map_err(|e| fail(e.to_string()))?;
        let file_path = temp_dir.path().join(format!("{}.lean", file_stem));
        fs::write(&file_path, file_content).map_err(|e| fail(e.to_string()))?;

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
        if let Ok(elan_home) = std::env::var("PROOFSEARCH_ELAN_HOME") {
            cmd.env("ELAN_HOME", elan_home);
        }
        configure_process_containment(&mut cmd);

        let mut child = cmd.spawn().map_err(|e| fail(e.to_string()))?;
        let stdout = child.stdout.take().ok_or_else(|| fail("Lean stdout pipe was unavailable".to_string()))?;
        let stderr = child.stderr.take().ok_or_else(|| fail("Lean stderr pipe was unavailable".to_string()))?;
        let output_limit = self.resource_policy.max_output_bytes;
        let stdout_reader = std::thread::spawn(move || capture_stream(stdout, output_limit));
        let stderr_reader = std::thread::spawn(move || capture_stream(stderr, output_limit));
        let status_result = wait_for_status_with_timeout(child, timeout);
        let stdout = stdout_reader.join().map_err(|_| fail("Lean stdout reader panicked".to_string()))?
            .map_err(|e| fail(e.to_string()))?;
        let stderr = stderr_reader.join().map_err(|_| fail("Lean stderr reader panicked".to_string()))?
            .map_err(|e| fail(e.to_string()))?;
        let (lines, total_diagnostics) = parse_lean_json_file(stdout.raw.path(), self.resource_policy.max_diagnostics)
            .map_err(fail)?;
        let receipt = persist_verifier_output(
            &self.lean_project_path, &stdout, &stderr, total_diagnostics, lines.len() as u64,
        ).map_err(fail)?;
        let status = match status_result {
            Ok(status) => status,
            Err(message) => return Err(LeanInvocationFailure { message, output_receipt: Some(receipt) }),
        };
        if receipt.truncated_bytes > 0 {
            return Err(LeanInvocationFailure {
                message: format!(
                    "verifier_output_limit_exceeded: {} byte(s) exceeded the bounded inline diagnostic capture; complete output is in the attached artifact",
                    receipt.truncated_bytes,
                ),
                output_receipt: Some(receipt),
            });
        }
        let stderr_str = String::from_utf8_lossy(&stderr.retained).to_string();
        Ok((status.success(), lines, stderr_str, receipt))
    }

    /// Issue #261: ensure each imported certified child's durability olean exists
    /// before a parent that imports it compiles, building any missing one on
    /// demand (synchronously) with the same single-file `lake env lean -o` the
    /// durability build now uses. Best-effort: a genuinely missing/failing child
    /// is surfaced by the parent's own compile as a real graph error rather than
    /// fabricated here.
    fn ensure_dependency_oleans_built(&self, approved_dependency_ids: &[Uuid]) {
        for dep_id in approved_dependency_ids {
            let dep_first_16 = &dep_id.to_string().replace('-', "")[..16];
            let olean_rel = format!(".lake/build/lib/lean/LeanChecker/Verified/O_{}.olean", dep_first_16);
            if self.lean_project_path.join(&olean_rel).exists() {
                continue;
            }
            let source_rel = format!("LeanChecker/Verified/O_{}.lean", dep_first_16);
            if !self.lean_project_path.join(&source_rel).exists() {
                continue; // no verified source to build — a real graph error, left to surface.
            }
            let _ = self.run_durability_build(&format!("LeanChecker.Verified.O_{}", dep_first_16));
        }
    }

    fn run_durability_build(&self, target: &str) -> Result<(std::process::ExitStatus, VerifierOutputReceipt), LeanInvocationFailure> {
        let _permit = PROCESS_LIMITER.acquire(self.resource_policy.max_concurrent_processes);
        let _build_lock = LAKE_BUILD_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let fail = |message: String| LeanInvocationFailure { message, output_receipt: None };
        let lake_path = self.elan_bin_path.join("lake.exe");
        // Issue #261: compile the single verified file against the ALREADY-BUILT
        // dependency oleans via `lake env lean -o <olean> <source>`, NOT
        // `lake build <target>`. `lake build` re-traverses the whole dependency
        // graph (re-checking Mathlib/proofwidgets/etc.), which on some platforms
        // fails outright (e.g. the ProofWidgets JS-cache rebuild on Windows) and
        // is far slower — leaving the child's `LeanChecker/Verified/O_*.olean`
        // unbuilt, so a parent SubmitModule assembly that imports it fails on the
        // missing artifact. The single-file compile hits the SAME pinned Lean
        // kernel on the SAME source against the SAME dependency oleans, so the
        // durability olean is byte-for-byte what a full build would produce — this
        // changes nothing about any proof or kernel result, it only materializes
        // the artifact reliably.
        let rel = target.replace('.', "/");
        let source_rel = format!("{}.lean", rel);
        let olean_rel = format!(".lake/build/lib/lean/{}.olean", rel);
        if let Some(parent) = self.lean_project_path.join(&olean_rel).parent() {
            let _ = fs::create_dir_all(parent);
        }
        let mut cmd = Command::new(&lake_path);
        cmd.arg("env").arg("lean").arg("-o").arg(&olean_rel).arg(&source_rel)
            .current_dir(&self.lean_project_path)
            .stdout(Stdio::piped()).stderr(Stdio::piped());
        if let Ok(elan_home) = std::env::var("PROOFSEARCH_ELAN_HOME") {
            cmd.env("ELAN_HOME", elan_home);
        }
        configure_process_containment(&mut cmd);
        let mut child = cmd.spawn().map_err(|e| fail(format!("durability build spawn failed: {e}")))?;
        let stdout = child.stdout.take().ok_or_else(|| fail("durability build stdout pipe unavailable".to_string()))?;
        let stderr = child.stderr.take().ok_or_else(|| fail("durability build stderr pipe unavailable".to_string()))?;
        let output_limit = self.resource_policy.max_output_bytes;
        let stdout_reader = std::thread::spawn(move || capture_stream(stdout, output_limit));
        let stderr_reader = std::thread::spawn(move || capture_stream(stderr, output_limit));
        let timeout = Duration::from_millis(self.resource_policy.durability_build_timeout_ms);
        let status_result = wait_for_status_with_timeout(child, timeout);
        let stdout = stdout_reader.join().map_err(|_| fail("durability stdout reader panicked".to_string()))?
            .map_err(|e| fail(e.to_string()))?;
        let stderr = stderr_reader.join().map_err(|_| fail("durability stderr reader panicked".to_string()))?
            .map_err(|e| fail(e.to_string()))?;
        let receipt = persist_verifier_output(&self.lean_project_path, &stdout, &stderr, 0, 0).map_err(fail)?;
        match status_result {
            Ok(status) => Ok((status, receipt)),
            Err(message) => Err(LeanInvocationFailure { message, output_receipt: Some(receipt) }),
        }
    }

    fn durability_job_dir(&self) -> PathBuf {
        self.lean_project_path.join(".proofsearch").join("durability-jobs")
    }

    /// Issue #220: sibling of `durability_job_dir` — where asynchronous
    /// verification job state (and result artifacts) live. On disk under the same
    /// `.proofsearch` root, so jobs survive a restart for free.
    fn verification_job_dir(&self) -> PathBuf {
        self.lean_project_path.join(".proofsearch").join("verification-jobs")
    }

    fn write_durability_state(&self, job_id: &str, state: &serde_json::Value) -> Result<(), String> {
        let _state_lock = DURABILITY_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let dir = self.durability_job_dir();
        fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        fs::write(dir.join(format!("{job_id}.json")), serde_json::to_vec(state).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())
    }

    fn enqueue_durability_build(&self, target: String, prior_job_id: Option<String>) -> Result<DurabilityJobReceipt, String> {
        let job_id = Uuid::new_v4().to_string();
        let queued_at = chrono::Utc::now().to_rfc3339();
        self.write_durability_state(&job_id, &serde_json::json!({
            "job_id": job_id, "target": target, "status": "queued", "kernel_verified": true,
            "artifact_persisted": true, "queued_at": queued_at, "prior_job_id": prior_job_id,
            "effective_timeout_ms": self.resource_policy.durability_build_timeout_ms
        }))?;
        let gateway = RealLeanGateway::with_resource_policy(
            self.lean_project_path.clone(), self.elan_bin_path.clone(), self.resource_policy.clone(),
        );
        let thread_job_id = job_id.clone();
        let thread_target = target.clone();
        let thread_prior_job_id = prior_job_id.clone();
        std::thread::spawn(move || {
            let started = Instant::now();
            let _ = gateway.write_durability_state(&thread_job_id, &serde_json::json!({
                "job_id": thread_job_id, "target": thread_target, "status": "running", "kernel_verified": true,
                "artifact_persisted": true, "started_at": chrono::Utc::now().to_rfc3339(),
                "prior_job_id": thread_prior_job_id,
                "effective_timeout_ms": gateway.resource_policy.durability_build_timeout_ms
            }));
            let result = gateway.run_durability_build(&thread_target);
            let duration_ms = started.elapsed().as_millis() as u64;
            let state = match result {
                Ok((status, output)) if status.success() => serde_json::json!({
                    "job_id": thread_job_id, "target": thread_target, "status": "complete", "kernel_verified": true,
                    "artifact_persisted": true, "durability_build_complete": true, "exit_status": status.to_string(),
                    "duration_ms": duration_ms, "output_receipt": output, "completed_at": chrono::Utc::now().to_rfc3339()
                    , "prior_job_id": thread_prior_job_id
                }),
                Ok((status, output)) => serde_json::json!({
                    "job_id": thread_job_id, "target": thread_target, "status": "failed", "kernel_verified": true,
                    "artifact_persisted": true, "durability_build_failed": true, "exit_status": status.to_string(),
                    "duration_ms": duration_ms, "output_receipt": output, "completed_at": chrono::Utc::now().to_rfc3339()
                    , "prior_job_id": thread_prior_job_id
                }),
                Err(error) => serde_json::json!({
                    "job_id": thread_job_id, "target": thread_target, "status": "failed", "kernel_verified": true,
                    "artifact_persisted": true, "durability_build_failed": true, "error": error.to_string(),
                    "output_receipt": error.output_receipt, "duration_ms": duration_ms,
                    "prior_job_id": thread_prior_job_id,
                    "completed_at": chrono::Utc::now().to_rfc3339()
                }),
            };
            let _ = gateway.write_durability_state(&thread_job_id, &state);
        });
        Ok(DurabilityJobReceipt { job_id, target, status: "queued".to_string(), error: None })
    }

    /// Renders the manifest's module paths as `import` lines (plus approved
    /// dependency imports) and returns the manifest's `open` directives
    /// (issue #62) separately — `import` lines must precede every other
    /// command, while `open` lines belong after the imports/namespace, so the
    /// two render at different positions in the file.
    fn build_import_block(import_manifest: &[String], approved_dependency_ids: &[Uuid]) -> (String, Vec<String>) {
        let (module_imports, open_directives) = crate::lean::module::partition_import_manifest(import_manifest);
        let mut imports = String::new();
        for module in &module_imports {
            imports.push_str(&format!("import {}\n", module));
        }
        for dep_id in approved_dependency_ids {
            let dep_first_16 = &dep_id.to_string().replace("-", "")[..16];
            imports.push_str(&format!("import LeanChecker.Verified.O_{}\n", dep_first_16));
        }
        (imports, open_directives)
    }

    /// Assembles the exact Lean source `verify_exact` submits to the kernel —
    /// pulled out into its own pure, unit-testable function (issue #141) so
    /// the whitespace contract between `:= by` and the proof body can be
    /// checked directly, without spawning a real Lean subprocess.
    ///
    /// The literal `by\n` in the format string is load-bearing: it puts a
    /// real newline between `by` and `proof_term` unconditionally, so the
    /// first proof line can NEVER land on the same physical source line as
    /// `by` — regardless of `statement`'s length or whether `proof_term`
    /// itself starts with a leading `\n`. That is the exact failure mode
    /// issue #141 reported (a long statement pushed `by` far enough right
    /// that a proof_term with no leading newline shared its line, breaking
    /// Lean 4's indentation-sensitive tactic parser). See
    /// `assemble_root_theorem_source_never_shares_by_line_regardless_of_statement_length_or_leading_newline`
    /// below for the regression test.
    fn assemble_root_theorem_source(
        imports: &str,
        problem_namespace: &str,
        open_block: &str,
        theorem_name: &str,
        statement: &str,
        proof_term: &str,
        proof_format: ProofFormat,
    ) -> String {
        let indented_proof = normalize_proof(proof_term, proof_format);
        format!(
            "{}\nnamespace {}\n\n{}theorem {} : {} := by\n{}\n\nend {}\n",
            imports, problem_namespace, open_block, theorem_name, statement, indented_proof, problem_namespace,
        )
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
    fn resource_policy(&self) -> Option<VerifierResourcePolicy> {
        Some(self.resource_policy.clone())
    }

    fn structural_fingerprint(&self, statement: &str) -> Result<serde_json::Value, String> {
        compute_structural_fingerprint(
            &self.lean_project_path,
            &self.elan_bin_path,
            statement,
            Duration::from_millis(self.resource_policy.proof_timeout_ms.max(60_000)),
        )
    }

    fn mathlib_fingerprint_index(&self, limit: usize) -> Result<String, String> {
        // The whole-library pass runs for many minutes; a capped run is fast.
        let timeout = if limit == 0 { Duration::from_secs(2400) } else { Duration::from_secs(300) };
        run_mathlib_fingerprint_harness(&self.lean_project_path, &self.elan_bin_path, limit, timeout)
    }

    fn durability_job_status(&self, job_id: &str) -> Result<serde_json::Value, String> {
        Uuid::parse_str(job_id).map_err(|e| format!("invalid durability job id: {e}"))?;
        let _state_lock = DURABILITY_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let path = self.durability_job_dir().join(format!("{job_id}.json"));
        let bytes = fs::read(path).map_err(|e| format!("unknown durability job {job_id}: {e}"))?;
        serde_json::from_slice(&bytes).map_err(|e| format!("corrupt durability job {job_id}: {e}"))
    }

    fn durability_job_retry(&self, job_id: &str) -> Result<DurabilityJobReceipt, String> {
        let state = self.durability_job_status(job_id)?;
        let status = state["status"].as_str().unwrap_or("unknown");
        if matches!(status, "queued" | "running") {
            return Err(format!("durability job {job_id} is still {status}"));
        }
        let target = state["target"].as_str().ok_or_else(|| format!("durability job {job_id} has no target"))?;
        self.enqueue_durability_build(target.to_string(), Some(job_id.to_string()))
    }

    fn verification_submit(
        &self,
        request: verification::VerificationJobRequest,
    ) -> Result<crate::models::VerificationJobReceipt, String> {
        let dir = self.verification_job_dir();
        // The worker runs on a background thread, so the runner must own an
        // independent gateway — clone this one, exactly as `enqueue_durability_build`
        // clones itself into its own build thread.
        let gateway = RealLeanGateway::with_resource_policy(
            self.lean_project_path.clone(),
            self.elan_bin_path.clone(),
            self.resource_policy.clone(),
        );
        let runner: verification::VerificationRunner = Box::new(move |req: &verification::VerificationJobRequest| {
            // The SAME `verify_exact` the synchronous `episode_step` path uses —
            // this async path changes nothing about proof authority.
            gateway.verify_exact(
                &req.obligation,
                &req.candidate_source,
                &req.approved_dependency_ids,
                &req.environment,
                &req.import_manifest,
                req.proof_format,
            )
        });
        verification::submit(&dir, &self.resource_policy, request, runner)
    }

    fn verification_status(&self, job_id: &str) -> Result<serde_json::Value, String> {
        verification::status(&self.verification_job_dir(), job_id)
    }

    fn verification_result(&self, job_id: &str) -> Result<serde_json::Value, String> {
        verification::result(&self.verification_job_dir(), job_id)
    }

    fn verification_cancel(&self, job_id: &str) -> Result<serde_json::Value, String> {
        verification::cancel(&self.verification_job_dir(), job_id)
    }

    fn verification_events(&self, job_id: &str) -> Result<serde_json::Value, String> {
        verification::events(&self.verification_job_dir(), job_id)
    }

    fn verify_exact(
        &self,
        obligation: &Obligation,
        candidate_source: &str,
        approved_dependency_ids: &[Uuid],
        environment: &str,
        import_manifest: &[String],
        proof_format: ProofFormat,
    ) -> Result<LeanVerificationResult, String> {
        let start_time = Instant::now();

        // 1. Generate namespace and theorem name
        let namespace_first_16 = &obligation.problem_version_id.to_string().replace("-", "")[..16];
        let obligation_first_16 = &obligation.id.to_string().replace("-", "")[..16];

        let problem_namespace = format!("ProofSearch.P_{}", namespace_first_16);
        let theorem_name = format!("O_{}", obligation_first_16);

        // 2. Imports come from the problem's own immutable manifest — never
        // hardcoded here. ALL `import` lines must precede any other command, so
        // dependency imports go before set_option. The manifest's `open`
        // directives (issue #62) render inside the namespace instead, matching
        // where the upstream benchmark file's own `open` lines sat.
        let (mut imports, open_directives) = Self::build_import_block(import_manifest, approved_dependency_ids);
        // Issue #261: a parent importing certified children needs each child's
        // `LeanChecker/Verified/O_*.olean` to EXIST at compile time. The child's
        // durability build runs in a detached thread that may not have finished
        // yet, so materialize any missing imported child olean on demand here,
        // before this parent compiles. Deterministic and idempotent — same
        // source, same deps, same pinned kernel; it only builds the artifact,
        // never changes a proof or verdict.
        self.ensure_dependency_oleans_built(approved_dependency_ids);
        imports.push_str("set_option linter.unusedTactic false\n");
        imports.push_str("set_option linter.unreachableTactic false\n");
        let open_block = if open_directives.is_empty() {
            String::new()
        } else {
            format!("{}\n\n", open_directives.join("\n"))
        };

        // 3. Construct Lean source code
        // Lean 4.32+ requires the first tactic after `:= by` to be indented
        // relative to the theorem — a proof block at column 0 is parsed as an
        // empty `by` block followed by stray identifiers, failing every proof.
        // normalize_proof applies the caller's declared transport format
        // (issue #51): the default flat_tactic_sequence also fixes issue #41 (a
        // naturally-formatted multi-line proof whose lines don't already share
        // one indentation level was silently reinterpreted by Lean's
        // whitespace-sensitive parser as nesting rather than sequencing);
        // raw_lean_block instead preserves relative indentation for proofs that
        // intentionally use it. Whitespace only — the kernel still decides.
        let file_content = Self::assemble_root_theorem_source(
            &imports, &problem_namespace, &open_block, &theorem_name,
            &obligation.lean_statement, candidate_source, proof_format,
        );

        // 4/5. Write + run.
        let (proc_success, lines, stderr, output_receipt) = match self.run_lean_json(
            &file_content,
            &theorem_name,
            Duration::from_millis(self.resource_policy.proof_timeout_ms),
        ) {
            Ok(v) => v,
            Err(failure) => {
                let message = failure.to_string();
                return Ok(LeanVerificationResult {
                    outcome: LeanVerificationOutcome::InfrastructureError,
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
                        primary_message: message,
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
                    resource_policy: Some(self.resource_policy.receipt()),
                    output_receipt: failure.output_receipt,
                    durability_job: None,
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

        // Kernel validity and durability are separate states. Persist the
        // verified source, then enqueue (never await) the bounded Lake build.
        let durability_job = if success {
            let verified_dir = self.lean_project_path.join("LeanChecker").join("Verified");
            let dest_path = verified_dir.join(format!("{}.lean", theorem_name));
            let persisted = fs::create_dir_all(&verified_dir).and_then(|_| fs::write(&dest_path, &file_content));
            let target = format!("LeanChecker.Verified.{}", theorem_name);
            Some(match persisted {
                Ok(()) => self.enqueue_durability_build(target.clone(), None).unwrap_or_else(|error| DurabilityJobReceipt {
                    job_id: String::new(), target, status: "queue_failed".to_string(), error: Some(error),
                }),
                Err(error) => DurabilityJobReceipt {
                    job_id: String::new(), target, status: "artifact_persist_failed".to_string(), error: Some(error.to_string()),
                },
            })
        } else { None };

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
            resource_policy: Some(self.resource_policy.receipt()),
            output_receipt: Some(output_receipt),
            durability_job,
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

        let mk_fail = |diag: LeanDiagnostic, all: Vec<LeanDiagnostic>, output_receipt: Option<VerifierOutputReceipt>, elapsed: u64| LeanModuleVerificationResult {
            outcome: LeanVerificationOutcome::KernelFail,
            problem_namespace: assembled.namespace.clone(),
            root_lean_name: assembled.root_lean_name.clone(),
            module_source_hash: assembled.module_source_hash.clone(),
            declaration_manifest_hash: assembled.declaration_manifest_hash.clone(),
            environment_hash: environment.to_string(),
            kernel_result_hash: kernel_result_hash.clone(),
            diagnostic: Some(diag),
            all_diagnostics: all,
            resource_policy: Some(self.resource_policy.receipt()),
            output_receipt,
            durability_job: None,
            wall_time_ms: elapsed,
        };

        let (proc_success, lines, stderr, output_receipt) = match self.run_lean_json(
            &assembled.source,
            &file_stem,
            Duration::from_millis(self.resource_policy.module_timeout_ms),
        ) {
            Ok(v) => v,
            Err(failure) => {
                let message = failure.to_string();
                let mut result = mk_fail(
                    LeanDiagnostic {
                        category: LeanDiagnosticCategory::TacticFailure,
                        primary_message: message,
                        source_span: None, goal: None, local_context: vec![], unsolved_goals: vec![],
                        used_dependencies: vec![], error_code: None, canonical_goal_hash: None,
                    },
                    vec![],
                    failure.output_receipt,
                    start_time.elapsed().as_millis() as u64,
                );
                result.outcome = LeanVerificationOutcome::InfrastructureError;
                return Ok(result);
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
            return Ok(mk_fail(diag, all_diagnostics, Some(output_receipt), elapsed));
        }

        // Success: write the verified source into Verified/ ONLY now. No partial
        // commit — this line is reached only after the entire module passed.
        let verified_dir = self.lean_project_path.join("LeanChecker").join("Verified");
        if !verified_dir.exists() {
            let _ = fs::create_dir_all(&verified_dir);
        }
        let dest_path = verified_dir.join(format!("{}.lean", file_stem));
        let target = format!("LeanChecker.Verified.{}", file_stem);
        let durability_job = match fs::write(&dest_path, &assembled.source) {
            Ok(()) => self.enqueue_durability_build(target.clone(), None).unwrap_or_else(|error| DurabilityJobReceipt {
                job_id: String::new(), target, status: "queue_failed".to_string(), error: Some(error),
            }),
            Err(error) => DurabilityJobReceipt {
                job_id: String::new(), target, status: "artifact_persist_failed".to_string(), error: Some(error.to_string()),
            },
        };

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
            resource_policy: Some(self.resource_policy.receipt()),
            output_receipt: Some(output_receipt),
            durability_job: Some(durability_job),
            wall_time_ms: start_time.elapsed().as_millis() as u64,
        })
    }

    fn validate_import_manifest(&self, imports: &[String]) -> Result<(), String> {
        if imports.is_empty() {
            return Ok(());
        }
        let (module_imports, open_directives) = crate::lean::module::partition_import_manifest(imports);
        let mut content = String::new();
        for module in &module_imports {
            content.push_str(&format!("import {}\n", module));
        }
        // `open` manifest entries (issue #62) are validated by the same probe:
        // an unknown namespace in an `open` line is a compile error here, so a
        // bad open entry is rejected at problem_create rather than surfacing as
        // a confusing failure on the first proof attempt.
        for open_directive in &open_directives {
            content.push_str(open_directive);
            content.push('\n');
        }
        // Validating imports means resolving them, which can itself pull in a
        // large chunk of Mathlib (e.g. the full `Mathlib` umbrella) — issue #66:
        // a COLD elaboration cache makes `import Mathlib` alone take over two
        // minutes on a workstation, so the old 45s budget rejected perfectly
        // valid manifests on the first call of a session. 240s covers a cold
        // umbrella load with margin; the warm path stays fast, and problem_create
        // additionally skips this probe entirely when the identical manifest
        // already validated under the same environment (see the manifest-hash
        // check there).
        let (proc_success, lines, stderr, _output_receipt) = self.run_lean_json(
            &content,
            "import_probe",
            Duration::from_millis(self.resource_policy.import_validation_timeout_ms),
        ).map_err(|e| e.to_string())?;
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
        let pass1 = self.check_pass(
            names,
            import_manifest,
            Duration::from_millis(self.resource_policy.declaration_lookup_timeout_ms),
        )?;

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
        let umbrella_results = self.check_pass(
            &need_umbrella,
            &["Mathlib".to_string()],
            Duration::from_millis(self.resource_policy.deep_declaration_lookup_timeout_ms),
        )?;
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
        let (module_imports, open_directives) = crate::lean::module::partition_import_manifest(imports);
        let mut content = String::new();
        for module in &module_imports {
            content.push_str(&format!("import {}\n", module));
        }
        // The manifest's `open` context (issue #62) participates in name
        // resolution here too — a lookup should see exactly the scope a Solve
        // attempt against this manifest would see.
        for open_directive in &open_directives {
            content.push_str(open_directive);
            content.push('\n');
        }
        content.push('\n');
        let check_start_line = content.matches('\n').count() as i64 + 1; // 1-indexed line of the first #check
        for name in names {
            content.push_str(&format!("#check {}\n", name));
        }

        let check_end_line = check_start_line + names.len() as i64 - 1;
        let (proc_success, lines, stderr, _output_receipt) = self.run_lean_json(&content, "decl_lookup", timeout)
            .map_err(|e| e.to_string())?;
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
    fn verifier_resource_policy_defaults_are_finite() {
        let policy = VerifierResourcePolicy::from_lookup(|_| None).unwrap();
        assert_eq!(policy, VerifierResourcePolicy::default());
        assert!(policy.proof_timeout_ms > 0);
        assert!(policy.max_concurrent_processes > 0);
    }

    #[test]
    fn verifier_resource_policy_accepts_bounded_operator_override() {
        let policy = VerifierResourcePolicy::from_lookup(|name| {
            (name == "PROOFSEARCH_VERIFY_PROOF_TIMEOUT_MS").then(|| "12345".to_string())
        }).unwrap();
        assert_eq!(policy.proof_timeout_ms, 12_345);
        assert_eq!(policy.module_timeout_ms, VerifierResourcePolicy::default().module_timeout_ms);
    }

    #[test]
    fn verifier_resource_policy_denies_zero_and_unlimited_overrides() {
        for raw in ["0", "3600001", "unlimited"] {
            let error = VerifierResourcePolicy::from_lookup(|name| {
                (name == "PROOFSEARCH_VERIFY_PROOF_TIMEOUT_MS").then(|| raw.to_string())
            }).unwrap_err();
            assert!(error.contains("PROOFSEARCH_VERIFY_PROOF_TIMEOUT_MS"));
        }
    }

    #[test]
    fn verifier_output_streaming_preserves_raw_bytes_and_critical_diagnostics() {
        let root = tempfile::tempdir().unwrap();
        let first = br#"{"severity":"error","message":"first"}"#;
        let sorry = br#"{"kind":"hasSorry","severity":"warning","message":"declaration uses `sorry`"}"#;
        let last = br#"{"severity":"error","message":"last"}"#;
        let mut stdout_bytes = Vec::new();
        stdout_bytes.extend_from_slice(first);
        stdout_bytes.push(b'\n');
        stdout_bytes.extend_from_slice(&[0xff, 0xfe, b'\n']);
        stdout_bytes.extend_from_slice(sorry);
        stdout_bytes.push(b'\n');
        stdout_bytes.extend_from_slice(last);
        stdout_bytes.push(b'\n');
        let stdout = capture_stream(std::io::Cursor::new(stdout_bytes.clone()), 12).unwrap();
        let stderr_bytes = b"mixed stderr\n".to_vec();
        let stderr = capture_stream(std::io::Cursor::new(stderr_bytes.clone()), 5).unwrap();
        let (diagnostics, total) = parse_lean_json_file(stdout.raw.path(), 3).unwrap();
        assert_eq!(total, 3, "invalid UTF-8 is preserved raw but is not fabricated into JSON");
        assert_eq!(diagnostics.len(), 3);
        assert!(diagnostics.iter().any(|value| value["kind"] == "hasSorry"));
        assert!(diagnostics.iter().any(|value| value["message"] == "first"));
        assert!(diagnostics.iter().any(|value| value["message"] == "last"));

        let receipt = persist_verifier_output(root.path(), &stdout, &stderr, total, diagnostics.len() as u64).unwrap();
        assert_eq!(receipt.stdout_bytes, stdout_bytes.len() as u64);
        assert_eq!(receipt.stderr_bytes, stderr_bytes.len() as u64);
        assert!(receipt.truncated_bytes > 0);
        let hex = receipt.artifact_hash.strip_prefix("sha256:").unwrap();
        let artifact = std::fs::read(root.path().join(".proofsearch/artifacts/sha256").join(format!("{hex}.bin"))).unwrap();
        assert!(artifact.windows(sorry.len()).any(|window| window == sorry));
        assert!(artifact.windows(3).any(|window| window == [0xff, 0xfe, b'\n']));
    }

    #[test]
    fn verifier_resource_rejection_is_infrastructure_not_kernel_failure() {
        let mut policy = VerifierResourcePolicy::default();
        policy.max_source_bytes = 1;
        let gateway = RealLeanGateway::with_resource_policy(
            PathBuf::from("dummy"),
            PathBuf::from("dummy"),
            policy.clone(),
        );
        let obligation = Obligation {
            id: Uuid::new_v4(), problem_version_id: Uuid::new_v4(), kind: ObligationKind::Root,
            theorem_name: "t".into(), lean_statement: "True".into(), statement_hash: "hash".into(),
            natural_description: "test".into(), status: ObligationStatus::Open, depth_from_root: 0,
            created_by: ObligationCreator::InitialSketch, created_by_epoch_id: None,
            superseded_by_id: None, proved_lemma_id: None, refutation_lemma_id: None,
            failure_lesson: None, attempt_count: 0, created_at: Utc::now(), closed_at: None,
        };
        let result = gateway.verify_exact(
            &obligation, "trivial", &[], "env", &default_manifest(), ProofFormat::FlatTacticSequence,
        ).unwrap();
        assert_eq!(result.outcome, LeanVerificationOutcome::InfrastructureError);
        let receipt = result.resource_policy.expect("resource policy receipt");
        assert_eq!(receipt.requested, policy);
        assert_eq!(receipt.effective, policy);
        assert!(!receipt.policy_hash.is_empty());
    }

    #[test]
    fn verifier_process_timeout_is_enforced() {
        for _ in 0..3 {
            #[cfg(target_os = "windows")]
            let mut command = {
                let mut command = Command::new("cmd.exe");
                command.args(["/C", "ping -n 30 127.0.0.1 >NUL"]);
                command
            };
            #[cfg(not(target_os = "windows"))]
            let mut command = {
                let mut command = Command::new("sh");
                command.args(["-c", "sleep 30 & wait"]);
                command
            };
            command.stdout(Stdio::piped()).stderr(Stdio::piped());
            configure_process_containment(&mut command);
            let child = command.spawn().unwrap();
            let pid = child.id();
            let error = wait_for_status_with_timeout(child, Duration::from_millis(20)).unwrap_err();
            assert!(error.contains("timed out after 20 ms"), "{error}");
            assert!(error.contains("cleanup=reaped"), "{error}");
            assert!(!ACTIVE_VERIFIER_PIDS.lock().unwrap().contains(&pid));
        }
    }

    /// Regression test for issue #141: a `solve` submission with
    /// `proof_format: "raw_lean_block"` whose `proof_term` does NOT start
    /// with an explicit leading `\n`, assembled against a deliberately long
    /// statement (so `by` lands far to the right, at whatever column the
    /// statement text happens to end) — the exact scenario the issue
    /// reported failing with `unexpected identifier; expected command` on
    /// the second tactic line. Asserts the assembled source's `by` is
    /// followed by a real newline, at every statement length, regardless of
    /// whether `proof_term` supplies its own leading `\n` — i.e. the first
    /// tactic line can never share `by`'s physical source line.
    #[test]
    fn assemble_root_theorem_source_never_shares_by_line_regardless_of_statement_length_or_leading_newline() {
        let long_statement = "∀ (t : ℕ) (ht : 0 < t) (α : ℝ) (h : Filter.Tendsto (fun n => (t : ℝ) * α ^ n) Filter.atTop (nhds 0)), True";
        for proof_term in [
            // No leading '\n' -- the exact shape issue #141 reported.
            "intro t ht α h\n  rw [Filter.eventually_atTop] at h\n  trivial",
            // A leading '\n' -- should behave identically; this is not a
            // workaround the assembly should depend on.
            "\nintro t ht α h\n  rw [Filter.eventually_atTop] at h\n  trivial",
            // A single-line proof, and an empty one -- boundary cases.
            "trivial",
            "",
        ] {
            for statement in [long_statement, "True"] {
                let source = RealLeanGateway::assemble_root_theorem_source(
                    "import Mathlib\n", "ProofSearch.P_test", "", "O_test",
                    statement, proof_term, ProofFormat::RawLeanBlock,
                );
                let by_pos = source.find(" := by\n")
                    .expect(&format!("assembled source must contain ' := by\\n' literally: {source:?}"));
                // Confirm it's really a newline immediately after `by`, not
                // just that the literal substring above matched -- i.e. the
                // character right after "by" is '\n', full stop, and
                // whatever comes after that newline is not itself blank
                // trailing whitespace hiding a same-line token.
                let after_by = &source[by_pos + " := by".len()..];
                assert!(after_by.starts_with('\n'),
                    "no real newline immediately after 'by' for statement={statement:?} proof_term={proof_term:?}: {source:?}");
            }
        }
    }

    #[test]
    fn test_real_lean_gateway_failure_cases() {
        let home = std::env::var("USERPROFILE").or_else(|_| std::env::var("HOME")).unwrap_or_default();
        let elan_bin_path = PathBuf::from(home).join(".elan").join("bin");
        let lean_project_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("lean-checker");

        let gateway = RealLeanGateway::new(lean_project_path.clone(), elan_bin_path);

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
        let res = gateway.verify_exact(&obligation, "rfl", &[], "envhash", &default_manifest(), ProofFormat::FlatTacticSequence);
        if let Ok(res_val) = res {
            assert!(matches!(
                res_val.outcome,
                LeanVerificationOutcome::KernelFail | LeanVerificationOutcome::InfrastructureError
            ));
            if res_val.outcome == LeanVerificationOutcome::InfrastructureError {
                assert!(res_val.diagnostic.is_some(), "an unavailable machine-specific Lean path must be explained");
            } else {
                let receipt = res_val.output_receipt.expect("a completed Lean process must persist its raw output receipt");
                let hex = receipt.artifact_hash.strip_prefix("sha256:").unwrap();
                assert!(lean_project_path.join(".proofsearch/artifacts/sha256").join(format!("{hex}.bin")).exists());
            }
        }
    }

    #[test]
    fn verifier_output_limit_exhaustion_is_infrastructure() {
        let home = std::env::var("USERPROFILE").or_else(|_| std::env::var("HOME")).unwrap_or_default();
        let elan_bin_path = PathBuf::from(home).join(".elan").join("bin");
        let lean_project_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("lean-checker");
        if !elan_bin_path.join("lake.exe").exists() || !lean_project_path.join("lakefile.toml").exists() { return }
        let mut policy = VerifierResourcePolicy::default();
        policy.max_output_bytes = 1;
        let gateway = RealLeanGateway::with_resource_policy(lean_project_path, elan_bin_path, policy);
        let obligation = Obligation {
            id: Uuid::new_v4(), problem_version_id: Uuid::new_v4(), kind: ObligationKind::Root,
            theorem_name: "output_limit".into(), lean_statement: "1 = 2".into(), statement_hash: "hash".into(),
            natural_description: "test".into(), status: ObligationStatus::Open, depth_from_root: 0,
            created_by: ObligationCreator::InitialSketch, created_by_epoch_id: None,
            superseded_by_id: None, proved_lemma_id: None, refutation_lemma_id: None,
            failure_lesson: None, attempt_count: 0, created_at: Utc::now(), closed_at: None,
        };
        let result = gateway.verify_exact(&obligation, "rfl", &[], "env", &default_manifest(), ProofFormat::FlatTacticSequence).unwrap();
        assert_eq!(result.outcome, LeanVerificationOutcome::InfrastructureError);
        assert!(result.diagnostic.unwrap().primary_message.contains("verifier_output_limit_exceeded"));
        assert!(result.output_receipt.unwrap().truncated_bytes > 0);
    }

    #[test]
    fn durability_retry_is_background_observable_and_keeps_kernel_truth_separate() {
        let root = tempfile::tempdir().unwrap();
        let gateway = RealLeanGateway::new(root.path().to_path_buf(), PathBuf::from("Z:\\missing-elan"));
        let prior = Uuid::new_v4().to_string();
        gateway.write_durability_state(&prior, &serde_json::json!({
            "job_id": prior, "target": "LeanChecker.Verified.missing", "status": "failed",
            "kernel_verified": true, "artifact_persisted": true
        })).unwrap();
        let started = Instant::now();
        let retry = gateway.durability_job_retry(&prior).unwrap();
        assert!(started.elapsed() < Duration::from_secs(1), "retry must enqueue without waiting for Lake");
        assert_eq!(retry.status, "queued");
        // The background build acquires the process-wide LAKE_BUILD_LOCK before it
        // even spawns, so when kernel_pass_queues_and_completes_observable_durability_job
        // holds that lock for a real single-file compile (~15-30s now that the
        // build actually succeeds, #261), this retry's own build blocks on the
        // lock before failing fast on the missing elan. The deadline must absorb
        // that in-flight real build; the assertion — settles to `failed`, kernel
        // truth intact — is unchanged.
        let deadline = Instant::now() + Duration::from_secs(90);
        loop {
            let state = gateway.durability_job_status(&retry.job_id).unwrap();
            if state["status"] == "failed" {
                assert_eq!(state["kernel_verified"], true, "a durability failure cannot revoke kernel truth");
                assert_eq!(state["prior_job_id"], prior);
                assert!(state["error"].as_str().is_some_and(|error| error.contains("spawn")));
                break;
            }
            assert!(Instant::now() < deadline, "durability retry did not settle: {state}");
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    #[test]
    fn kernel_pass_queues_and_completes_observable_durability_job() {
        let home = std::env::var("USERPROFILE").or_else(|_| std::env::var("HOME")).unwrap_or_default();
        let elan_bin_path = PathBuf::from(home).join(".elan").join("bin");
        let lean_project_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("lean-checker");
        if !elan_bin_path.join("lake.exe").exists() || !lean_project_path.join("lakefile.toml").exists() { return }
        let gateway = RealLeanGateway::new(lean_project_path, elan_bin_path);
        let obligation = Obligation {
            id: Uuid::new_v4(), problem_version_id: Uuid::new_v4(), kind: ObligationKind::Root,
            theorem_name: "durability".into(), lean_statement: "True".into(), statement_hash: "hash".into(),
            natural_description: "test".into(), status: ObligationStatus::Open, depth_from_root: 0,
            created_by: ObligationCreator::InitialSketch, created_by_epoch_id: None,
            superseded_by_id: None, proved_lemma_id: None, refutation_lemma_id: None,
            failure_lesson: None, attempt_count: 0, created_at: Utc::now(), closed_at: None,
        };
        let result = gateway.verify_exact(&obligation, "trivial", &[], "env", &default_manifest(), ProofFormat::FlatTacticSequence).unwrap();
        assert_eq!(result.outcome, LeanVerificationOutcome::KernelPass);
        let job = result.durability_job.expect("kernel pass must expose its durability job");
        assert!(!job.job_id.is_empty());
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            let state = gateway.durability_job_status(&job.job_id).unwrap();
            match state["status"].as_str() {
                Some("complete") => {
                    assert_eq!(state["kernel_verified"], true);
                    assert!(state["output_receipt"]["artifact_hash"].is_string());
                    break;
                }
                Some("failed") => panic!("durability build unexpectedly failed without changing kernel truth: {state}"),
                _ => assert!(Instant::now() < deadline, "durability build did not settle: {state}"),
            }
            std::thread::sleep(Duration::from_millis(20));
        }
    }

    /// Issue #220's core invariant: an asynchronous verification job runs the
    /// EXACT SAME `verify_exact`, so its result must equal what the synchronous
    /// path produces for the SAME input — whatever that verdict is. This asserts
    /// that equality directly rather than assuming the environment proves the
    /// goal, so it validates the real claim ("async == sync") and stays honest in
    /// any real-Lean environment. Lean-guarded exactly like the other
    /// RealLeanGateway integration tests; the deadline is tied to the gateway's
    /// own proof timeout so a slow-but-working verifier never false-fails.
    #[test]
    fn async_verification_job_result_matches_synchronous_verify_exact() {
        let home = std::env::var("USERPROFILE").or_else(|_| std::env::var("HOME")).unwrap_or_default();
        let elan_bin_path = PathBuf::from(home).join(".elan").join("bin");
        let lean_project_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("lean-checker");
        if !elan_bin_path.join("lake.exe").exists() || !lean_project_path.join("lakefile.toml").exists() { return }
        let gateway = RealLeanGateway::new(lean_project_path, elan_bin_path);
        let obligation = Obligation {
            id: Uuid::new_v4(), problem_version_id: Uuid::new_v4(), kind: ObligationKind::Root,
            theorem_name: "async_match".into(), lean_statement: "True".into(), statement_hash: "hash".into(),
            natural_description: "test".into(), status: ObligationStatus::Open, depth_from_root: 0,
            created_by: ObligationCreator::InitialSketch, created_by_epoch_id: None,
            superseded_by_id: None, proved_lemma_id: None, refutation_lemma_id: None,
            failure_lesson: None, attempt_count: 0, created_at: Utc::now(), closed_at: None,
        };
        // A run-unique candidate source (trailing line comment, ignored by Lean)
        // so this test never deduplicates against a completed job a PRIOR run
        // persisted in the shared `.proofsearch/verification-jobs` dir — sync and
        // async are then computed fresh, together, on identical input.
        let candidate_source = format!("trivial -- {}", Uuid::new_v4());

        // Synchronous baseline — the source of truth this async run must match.
        let sync = gateway.verify_exact(&obligation, &candidate_source, &[], "env", &default_manifest(), ProofFormat::FlatTacticSequence).unwrap();

        // Same inputs, submitted asynchronously.
        let request = verification::VerificationJobRequest {
            obligation: obligation.clone(),
            candidate_source: candidate_source.clone(),
            approved_dependency_ids: vec![],
            environment: "env".into(),
            import_manifest: default_manifest(),
            proof_format: ProofFormat::FlatTacticSequence,
        };
        let receipt = gateway.verification_submit(request).unwrap();
        assert!(!receipt.job_id.is_empty());
        assert!(!receipt.reused);

        // Any terminal phase is acceptable (complete/failed/timed_out) — the
        // point is that whatever the sync path decided, the async path decides
        // identically. Deadline covers a full cold verify plus a generous margin.
        let deadline = Instant::now()
            + Duration::from_millis(gateway.resource_policy.proof_timeout_ms)
            + Duration::from_secs(120);
        let final_state = loop {
            let state = gateway.verification_status(&receipt.job_id).unwrap();
            match state["phase"].as_str() {
                Some("complete") | Some("failed") | Some("timed_out") => break state,
                Some("cancelled") | Some("interrupted") =>
                    panic!("async verify reached an unexpected terminal phase: {state}"),
                _ => assert!(Instant::now() < deadline, "async verify did not settle in time: {state}"),
            }
            std::thread::sleep(Duration::from_millis(50));
        };
        // Status is lightweight: no full payload, but carries the artifact hash.
        assert!(final_state.get("all_diagnostics").is_none());
        assert!(final_state["result_artifact_hash"].as_str().is_some());

        // The async result payload matches the synchronous verdict exactly on the
        // load-bearing fields (attempt_id/wall-time are expected to differ).
        let full = gateway.verification_result(&receipt.job_id).unwrap();
        assert_eq!(full["available"], true);
        let async_result: LeanVerificationResult = serde_json::from_value(full["result"].clone()).unwrap();
        assert_eq!(async_result.outcome, sync.outcome, "async outcome must equal the synchronous verify_exact outcome");
        assert_eq!(async_result.theorem_name, sync.theorem_name);
        assert_eq!(async_result.expected_statement_hash, sync.expected_statement_hash);
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
    /// elan path), so verify_module returns InfrastructureError — and the Verified/ tree must
    /// be untouched. No partial commit.
    #[test]
    fn verify_module_does_not_write_on_failure() {
        use crate::models::action::{ModuleTheorem, ProofFormat};
        let tmp = tempfile::tempdir().unwrap();
        let lean_project = tmp.path().to_path_buf();
        let gateway = RealLeanGateway::new(lean_project.clone(), PathBuf::from("Z:\\definitely\\nonexistent\\bin"));

        let stmt = "1 + 1 = 2";
        let root_hash = crate::hashing::canonical_hash(&stmt.to_string()).unwrap();
        let root = ModuleTheorem { name: "r".to_string(), statement: stmt.to_string(), proof_term: "norm_num".to_string(), proof_format: ProofFormat::FlatTacticSequence };
        let asm = module::assemble_module("ProofSearch.P_test", &root_hash, &[], &root, &default_manifest()).unwrap();

        let res = gateway.verify_module(&asm, "envhash").unwrap();
        assert!(matches!(res.outcome, LeanVerificationOutcome::InfrastructureError), "a gateway that can't run Lean is an infrastructure failure");

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
