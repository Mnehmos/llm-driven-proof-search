//! Issue #220: asynchronous verifier jobs — an ADDITIVE transport layer over the
//! EXACT SAME `verify_exact` the synchronous `episode_step` path uses.
//!
//! # Why this exists
//!
//! Synchronous verification runs inside the lifetime of a single MCP request, so
//! a large proof inherits every client/transport/proxy/request timeout even when
//! the verifier itself is healthy. This module lets a caller `submit` a
//! verification, get a durable `job_id` back immediately, and then `poll`
//! (`status`), fetch the `result`, `cancel`, or read the phase-transition
//! history (`events`) across as many separate requests as it takes — the
//! verifier runs on its own background thread, unbound from any one request.
//!
//! # Trust boundary (unchanged)
//!
//! This changes NOTHING about proof authority. A submitted job runs the same
//! `verify_exact`, reaches the same Lean kernel, and produces exactly the result
//! the synchronous path would have produced for the same inputs. The job's
//! persisted *state* (phase, timestamps, hashes) is transport bookkeeping and is
//! never itself a verdict; the verdict is the `LeanVerificationResult` the runner
//! returns, stored as the result artifact and only ever surfaced by `result`.
//!
//! # Persistence model
//!
//! File-based, exactly like the durability job system (`enqueue_durability_build`
//! in `super`): one JSON state file per job under
//! `<root>/.proofsearch/verification-jobs/{job_id}.json`, rewritten through the
//! phase machine and guarded by a process-wide state lock. The full result
//! payload lives beside it in `{job_id}.result.json`. State on disk is what gives
//! restart-survival for free: a job whose state file says it was mid-run but
//! whose owning process is gone (boot id mismatch) or whose heartbeat is stale is
//! reported as `interrupted` — never dishonestly as still-running or complete.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, LazyLock, Mutex};
use std::time::Duration;

use chrono::{DateTime, Utc};
use uuid::Uuid;

use crate::models::action::ProofFormat;
use crate::models::{LeanVerificationOutcome, LeanVerificationResult, Obligation, VerifierResourcePolicy};

/// Per-process identity, regenerated on every server start. Every job records the
/// boot id of the process that launched it. On read, a non-terminal job whose
/// boot id differs from this was left mid-run by a process that no longer exists
/// (a restart or crash), so it is reported `interrupted` rather than lying that
/// it is still running. This is the deterministic restart-survival signal.
pub static PROCESS_BOOT_ID: LazyLock<String> = LazyLock::new(|| Uuid::new_v4().to_string());

/// Serializes state-file writes, mirroring `DURABILITY_STATE_LOCK` in `super`.
/// Every read-modify-write of a job state file happens under this lock so
/// concurrent phase transitions, heartbeats, cancellation, and dedup scans never
/// interleave a torn write.
static VERIFICATION_STATE_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

/// `job_id -> subprocess pids` spawned while running that job. Populated by the
/// verifier process-tracking hook in `super::wait_for_status_with_timeout` when a
/// job context is active on the running thread, and read by `cancel` to kill the
/// COMPLETE process tree of the job's live Lean/Lake subprocess(es). Scoping the
/// kill to a single job's pids is why cancelling one job cannot disturb another's
/// concurrent verification.
static VERIFICATION_JOB_PIDS: LazyLock<Mutex<HashMap<String, HashSet<u32>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Job ids that received a cancel request. The running job thread consults this
/// (and the persisted phase) after its runner returns so a killed run is recorded
/// as `cancelled`, not `failed`.
static VERIFICATION_CANCELLED: LazyLock<Mutex<HashSet<String>>> =
    LazyLock::new(|| Mutex::new(HashSet::new()));

thread_local! {
    /// The verification job (if any) whose runner is executing on THIS thread.
    /// `super::wait_for_status_with_timeout` reads it to attribute the Lean
    /// subprocess pid it just spawned to the right job. `None` on the
    /// `episode_step` path, so that trust-critical path is entirely unaffected.
    static CURRENT_JOB: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Heartbeat cadence for a running job's liveness field.
const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(10);
/// Extra slack beyond a job's effective timeout before a same-process job with a
/// silent heartbeat is treated as interrupted (a panicked/wedged worker thread).
const HEARTBEAT_STALE_GRACE_MS: i64 = 120_000;

/// The complete set of inputs one asynchronous verification job runs — exactly
/// the arguments `LeanGateway::verify_exact` takes, so a job produces the same
/// result the synchronous path would for the same inputs.
#[derive(Debug, Clone)]
pub struct VerificationJobRequest {
    pub obligation: Obligation,
    pub candidate_source: String,
    pub approved_dependency_ids: Vec<Uuid>,
    pub environment: String,
    pub import_manifest: Vec<String>,
    pub proof_format: ProofFormat,
}

/// The work a job performs: run the real verification synchronously on the job's
/// background thread and return the full result. Boxed so `RealLeanGateway` can
/// hand in a closure that clones itself and calls `verify_exact`, while tests can
/// hand in a canned runner.
pub type VerificationRunner =
    Box<dyn FnOnce(&VerificationJobRequest) -> Result<LeanVerificationResult, String> + Send>;

fn terminal(phase: &str) -> bool {
    matches!(phase, "complete" | "failed" | "timed_out" | "cancelled")
}

// -- cancellation registry helpers (crate-internal) -----------------------

pub(crate) fn current_job() -> Option<String> {
    CURRENT_JOB.with(|c| c.borrow().clone())
}

fn set_current_job(job: Option<String>) {
    CURRENT_JOB.with(|c| *c.borrow_mut() = job);
}

/// Records a live verifier subprocess pid against the job running on this thread.
/// Called by `super::wait_for_status_with_timeout`; a no-op when no job context
/// is active (i.e. the synchronous path).
pub(crate) fn register_job_pid(job_id: &str, pid: u32) {
    VERIFICATION_JOB_PIDS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .entry(job_id.to_string())
        .or_default()
        .insert(pid);
}

pub(crate) fn deregister_job_pid(job_id: &str, pid: u32) {
    let mut map = VERIFICATION_JOB_PIDS.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(set) = map.get_mut(job_id) {
        set.remove(&pid);
        if set.is_empty() {
            map.remove(job_id);
        }
    }
}

fn job_pids(job_id: &str) -> Vec<u32> {
    VERIFICATION_JOB_PIDS
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .get(job_id)
        .map(|s| s.iter().copied().collect())
        .unwrap_or_default()
}

fn mark_cancelled(job_id: &str) {
    VERIFICATION_CANCELLED
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .insert(job_id.to_string());
}

fn is_cancelled(job_id: &str) -> bool {
    VERIFICATION_CANCELLED
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .contains(job_id)
}

fn clear_cancelled(job_id: &str) {
    VERIFICATION_CANCELLED
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .remove(job_id);
}

// -- state file helpers ---------------------------------------------------

fn job_path(dir: &Path, job_id: &str) -> PathBuf {
    dir.join(format!("{job_id}.json"))
}

fn result_path(dir: &Path, job_id: &str) -> PathBuf {
    dir.join(format!("{job_id}.result.json"))
}

/// Reads a job state file. Caller must hold `VERIFICATION_STATE_LOCK` for a
/// read-modify-write; a lone read may take it internally.
fn read_state_locked(dir: &Path, job_id: &str) -> Result<serde_json::Value, String> {
    let bytes = fs::read(job_path(dir, job_id))
        .map_err(|e| format!("unknown verification job {job_id}: {e}"))?;
    serde_json::from_slice(&bytes).map_err(|e| format!("corrupt verification job {job_id}: {e}"))
}

fn write_state_locked(dir: &Path, job_id: &str, state: &serde_json::Value) -> Result<(), String> {
    fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    fs::write(
        job_path(dir, job_id),
        serde_json::to_vec(state).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())
}

/// Appends a `{phase, at}` event and moves the job to `new_phase`, refreshing the
/// heartbeat and merging any extra fields. TERMINAL-AWARE: if the job is already
/// in a terminal phase it is left untouched (returns false) — this is what lets a
/// `cancel` that already wrote `cancelled` win against a slower in-flight
/// transition, and vice-versa, without a second writer clobbering the first.
fn transition_phase(
    dir: &Path,
    job_id: &str,
    new_phase: &str,
    extra: &[(&str, serde_json::Value)],
) -> Result<bool, String> {
    let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let mut state = read_state_locked(dir, job_id)?;
    let current = state.get("phase").and_then(|p| p.as_str()).unwrap_or("");
    if terminal(current) {
        return Ok(false);
    }
    apply_phase(&mut state, new_phase);
    for (k, v) in extra {
        state[*k] = v.clone();
    }
    write_state_locked(dir, job_id, &state)?;
    Ok(true)
}

fn apply_phase(state: &mut serde_json::Value, new_phase: &str) {
    let now = Utc::now().to_rfc3339();
    state["phase"] = serde_json::json!(new_phase);
    state["heartbeat_at"] = serde_json::json!(now);
    let event = serde_json::json!({ "phase": new_phase, "at": now });
    match state.get_mut("phases").and_then(|p| p.as_array_mut()) {
        Some(arr) => arr.push(event),
        None => state["phases"] = serde_json::json!([event]),
    }
}

// -- hashing --------------------------------------------------------------

/// Content hash of the verification INPUTS. Two submissions with identical
/// obligation statement, proof body, dependencies, imports, and transport format
/// share a source hash and (given the same environment) may be deduplicated.
pub fn compute_source_hash(req: &VerificationJobRequest) -> String {
    let dep_ids: Vec<String> = req.approved_dependency_ids.iter().map(|d| d.to_string()).collect();
    let proof_format = match req.proof_format {
        ProofFormat::FlatTacticSequence => "flat_tactic_sequence",
        ProofFormat::RawLeanBlock => "raw_lean_block",
    };
    crate::hashing::canonical_hash(&serde_json::json!({
        "lean_statement": req.obligation.lean_statement,
        "statement_hash": req.obligation.statement_hash,
        "candidate_source": req.candidate_source,
        "approved_dependency_ids": dep_ids,
        "import_manifest": req.import_manifest,
        "proof_format": proof_format,
    }))
    .unwrap_or_default()
}

// -- public engine API ----------------------------------------------------

/// Launches an asynchronous verification job, returning immediately with a
/// durable receipt. If an identical completed job (same source and environment
/// hash) already exists, that job is REUSED and its receipt returned instead of
/// launching a second run (acceptance: "identical completed jobs may be reused").
///
/// The `runner` executes on a background thread; `submit` never blocks on the
/// verifier (acceptance: "MCP submission returns without waiting for Lean").
pub fn submit(
    dir: &Path,
    policy: &VerifierResourcePolicy,
    request: VerificationJobRequest,
    runner: VerificationRunner,
) -> Result<crate::models::VerificationJobReceipt, String> {
    let source_hash = compute_source_hash(&request);
    let environment_hash = request.environment.clone();

    // Dedup + create the queued state under one lock section so two identical
    // concurrent submits can't both miss and both launch.
    let job_id = {
        let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(existing) = find_completed_locked(dir, &source_hash, &environment_hash) {
            return Ok(crate::models::VerificationJobReceipt {
                job_id: existing.0,
                source_hash,
                environment_hash,
                phase: existing.1,
                reused: true,
            });
        }
        let job_id = Uuid::new_v4().to_string();
        let now = Utc::now().to_rfc3339();
        let state = serde_json::json!({
            "job_id": job_id,
            "kind": "verify_exact",
            "phase": "queued",
            "source_hash": source_hash,
            "environment_hash": environment_hash,
            "boot_id": PROCESS_BOOT_ID.clone(),
            "server_pid": std::process::id(),
            "effective_timeout_ms": policy.proof_timeout_ms,
            "resource_policy_hash": crate::hashing::canonical_hash(policy).unwrap_or_default(),
            "cancellation_requested": false,
            "queued_at": now,
            "heartbeat_at": now,
            "phases": [{ "phase": "queued", "at": now }],
        });
        write_state_locked(dir, &job_id, &state)?;
        job_id
    };

    clear_cancelled(&job_id);
    spawn_worker(dir.to_path_buf(), job_id.clone(), request, runner);

    Ok(crate::models::VerificationJobReceipt {
        job_id,
        source_hash,
        environment_hash,
        phase: "queued".to_string(),
        reused: false,
    })
}

/// Scans for a completed job matching `(source_hash, environment_hash)`. Caller
/// holds the state lock. Returns `(job_id, phase)` on the first match.
fn find_completed_locked(
    dir: &Path,
    source_hash: &str,
    environment_hash: &str,
) -> Option<(String, String)> {
    let entries = fs::read_dir(dir).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
        // Only the job state files, never the `.result.json` sidecars.
        if !name.ends_with(".json") || name.ends_with(".result.json") {
            continue;
        }
        let Ok(bytes) = fs::read(&path) else { continue };
        let Ok(state) = serde_json::from_slice::<serde_json::Value>(&bytes) else { continue };
        let matches = state.get("phase").and_then(|p| p.as_str()) == Some("complete")
            && state.get("source_hash").and_then(|h| h.as_str()) == Some(source_hash)
            && state.get("environment_hash").and_then(|h| h.as_str()) == Some(environment_hash);
        if matches {
            let job_id = state.get("job_id").and_then(|j| j.as_str())?.to_string();
            return Some((job_id, "complete".to_string()));
        }
    }
    None
}

/// Guarantees the heartbeat ticker is stopped on every exit path from the worker.
struct StopGuard(Arc<AtomicBool>);
impl Drop for StopGuard {
    fn drop(&mut self) {
        self.0.store(true, Ordering::SeqCst);
    }
}

fn spawn_worker(
    dir: PathBuf,
    job_id: String,
    request: VerificationJobRequest,
    runner: VerificationRunner,
) {
    std::thread::spawn(move || {
        let stop = Arc::new(AtomicBool::new(false));
        let _stop_guard = StopGuard(stop.clone());
        spawn_heartbeat(dir.clone(), job_id.clone(), stop);

        set_current_job(Some(job_id.clone()));

        let started = Utc::now().to_rfc3339();
        let _ = transition_phase(&dir, &job_id, "staging", &[("started_at", serde_json::json!(started))]);
        if cancelled_before_run(&dir, &job_id) {
            return;
        }
        // A single opaque `verify_exact` call performs staging, import
        // resolution, elaboration, and kernel checking internally; the async
        // orchestrator marks the coarse `elaborating` phase it can honestly
        // observe from outside rather than fabricating finer transitions it
        // never actually witnesses.
        let _ = transition_phase(&dir, &job_id, "elaborating", &[]);
        if cancelled_before_run(&dir, &job_id) {
            return;
        }

        let outcome = runner(&request);

        // A cancel that already wrote `cancelled` (which happens under the lock
        // BEFORE the subprocess is killed) must win over the failure the killed
        // runner reports back. Both the persisted phase and the registry are
        // checked; `finalize_*` is terminal-aware so the loser never clobbers.
        set_current_job(None);
        if is_cancelled(&job_id) {
            finalize_cancelled(&dir, &job_id);
            clear_cancelled(&job_id);
            return;
        }

        match outcome {
            Ok(result) => finalize_result(&dir, &job_id, result),
            Err(err) => finalize_failure(&dir, &job_id, &err),
        }
    });
}

/// Returns true (and finalizes as cancelled) if a cancel landed before/while the
/// worker reached the verifier, so it never launches a run the caller already
/// asked to stop.
fn cancelled_before_run(dir: &Path, job_id: &str) -> bool {
    if is_cancelled(job_id) {
        finalize_cancelled(dir, job_id);
        clear_cancelled(job_id);
        set_current_job(None);
        return true;
    }
    false
}

fn spawn_heartbeat(dir: PathBuf, job_id: String, stop: Arc<AtomicBool>) {
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(HEARTBEAT_INTERVAL);
            if stop.load(Ordering::SeqCst) {
                break;
            }
            let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
            let Ok(mut state) = read_state_locked(&dir, &job_id) else { break };
            let phase = state.get("phase").and_then(|p| p.as_str()).unwrap_or("");
            if terminal(phase) {
                break;
            }
            state["heartbeat_at"] = serde_json::json!(Utc::now().to_rfc3339());
            let _ = write_state_locked(&dir, &job_id, &state);
        }
    });
}

/// Writes the full result payload as the job's result artifact and moves the job
/// to its terminal phase. The lightweight `outcome` label and
/// `result_artifact_hash` go into the state; the heavy payload (diagnostics,
/// receipts, hashes) stays in `{job_id}.result.json` and is only ever returned by
/// `result`, never by `status` (acceptance: "status polling does not return the
/// full result payload").
fn finalize_result(dir: &Path, job_id: &str, result: LeanVerificationResult) {
    let phase = match result.outcome {
        LeanVerificationOutcome::KernelPass | LeanVerificationOutcome::KernelFail => "complete",
        LeanVerificationOutcome::Timeout => "timed_out",
        LeanVerificationOutcome::InfrastructureError => "failed",
    };
    let outcome_label = result.outcome.to_string();
    let payload = serde_json::to_value(&result).unwrap_or(serde_json::Value::Null);
    let result_artifact_hash = crate::hashing::canonical_hash(&payload).unwrap_or_default();

    // Hold the lock across the check, the result-artifact write, and the state
    // write so a cancel that already finalized this job wins cleanly — and a
    // cancelled job never leaves a stray result artifact behind.
    let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let Ok(mut state) = read_state_locked(dir, job_id) else { return };
    if state.get("phase").and_then(|p| p.as_str()) == Some("cancelled") {
        return;
    }
    let _ = write_result_payload(dir, job_id, &payload);
    apply_phase(&mut state, phase);
    state["outcome"] = serde_json::json!(outcome_label);
    state["result_artifact_hash"] = serde_json::json!(result_artifact_hash);
    state["completed_at"] = serde_json::json!(Utc::now().to_rfc3339());
    let _ = write_state_locked(dir, job_id, &state);
}

fn finalize_failure(dir: &Path, job_id: &str, error: &str) {
    let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let Ok(mut state) = read_state_locked(dir, job_id) else { return };
    if state.get("phase").and_then(|p| p.as_str()) == Some("cancelled") {
        return;
    }
    apply_phase(&mut state, "failed");
    state["error"] = serde_json::json!(error);
    state["completed_at"] = serde_json::json!(Utc::now().to_rfc3339());
    let _ = write_state_locked(dir, job_id, &state);
}

fn finalize_cancelled(dir: &Path, job_id: &str) {
    let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let Ok(mut state) = read_state_locked(dir, job_id) else { return };
    if state.get("phase").and_then(|p| p.as_str()) == Some("cancelled") {
        return;
    }
    apply_phase(&mut state, "cancelled");
    state["cancellation_requested"] = serde_json::json!(true);
    state["cancelled_at"] = serde_json::json!(Utc::now().to_rfc3339());
    let _ = write_state_locked(dir, job_id, &state);
}

fn write_result_payload(dir: &Path, job_id: &str, payload: &serde_json::Value) -> Result<(), String> {
    fs::create_dir_all(dir).map_err(|e| e.to_string())?;
    fs::write(
        result_path(dir, job_id),
        serde_json::to_vec(payload).map_err(|e| e.to_string())?,
    )
    .map_err(|e| e.to_string())
}

/// Lightweight job metadata for polling: phase, timestamps, heartbeat, identity,
/// hashes, cancellation state, and (once complete) `result_artifact_hash` — but
/// NEVER the full result payload. A non-terminal job left behind by a dead
/// process (boot id mismatch) or a wedged worker (stale heartbeat) is reported as
/// `interrupted`, computed honestly at read time without mutating the file.
pub fn status(dir: &Path, job_id: &str) -> Result<serde_json::Value, String> {
    validate_job_id(job_id)?;
    let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let state = read_state_locked(dir, job_id)?;
    let mut view = state.clone();
    // `phases` is the events log; keep status lean and let `events` own it.
    if let Some(obj) = view.as_object_mut() {
        obj.remove("phases");
    }
    if let Some((interrupted_phase, reason)) = interrupted_view(&state) {
        view["phase"] = serde_json::json!(interrupted_phase);
        view["interrupted"] = serde_json::json!(true);
        view["interrupted_reason"] = serde_json::json!(reason);
    }
    Ok(view)
}

/// Returns `Some(("interrupted", reason))` when a non-terminal job's owning
/// process is gone or its heartbeat is stale; `None` otherwise.
fn interrupted_view(state: &serde_json::Value) -> Option<(&'static str, String)> {
    let phase = state.get("phase").and_then(|p| p.as_str()).unwrap_or("");
    if terminal(phase) {
        return None;
    }
    let boot = state.get("boot_id").and_then(|b| b.as_str()).unwrap_or("");
    if boot != PROCESS_BOOT_ID.as_str() {
        return Some((
            "interrupted",
            format!("job was started by a previous process (boot_id {boot}) that is no longer running"),
        ));
    }
    // Same process: a genuinely running job is heartbeated every ~10s, so a
    // heartbeat older than its effective timeout plus grace means a wedged or
    // panicked worker, not a live run.
    let timeout = state
        .get("effective_timeout_ms")
        .and_then(|t| t.as_i64())
        .unwrap_or(0);
    if let Some(hb) = state.get("heartbeat_at").and_then(|h| h.as_str()) {
        if let Ok(hb_time) = DateTime::parse_from_rfc3339(hb) {
            let age_ms = Utc::now()
                .signed_duration_since(hb_time.with_timezone(&Utc))
                .num_milliseconds();
            if age_ms > timeout.saturating_add(HEARTBEAT_STALE_GRACE_MS) {
                return Some((
                    "interrupted",
                    format!("heartbeat is stale ({age_ms} ms old); the worker is no longer live"),
                ));
            }
        }
    }
    None
}

/// Returns the full verification payload for a completed/failed job. This is the
/// ONLY action that returns the heavy result; `status` never does.
pub fn result(dir: &Path, job_id: &str) -> Result<serde_json::Value, String> {
    validate_job_id(job_id)?;
    let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let state = read_state_locked(dir, job_id)?;
    let phase = state.get("phase").and_then(|p| p.as_str()).unwrap_or("");
    match fs::read(result_path(dir, job_id)) {
        Ok(bytes) => {
            let payload: serde_json::Value =
                serde_json::from_slice(&bytes).map_err(|e| format!("corrupt result artifact for {job_id}: {e}"))?;
            Ok(serde_json::json!({
                "job_id": job_id,
                "phase": phase,
                "available": true,
                "result_artifact_hash": state.get("result_artifact_hash").cloned().unwrap_or(serde_json::Value::Null),
                "result": payload,
            }))
        }
        Err(_) => Ok(serde_json::json!({
            "job_id": job_id,
            "phase": phase,
            "available": false,
            "note": "no result payload for this job yet (still running, cancelled, or interrupted)",
        })),
    }
}

/// Cancels a job: records the cancellation, moves it to `cancelled`, and kills the
/// COMPLETE process tree of any live verifier subprocess for this job
/// (acceptance: "cancellation terminates the complete subprocess tree"). A job
/// already in a terminal phase is a no-op. Writing `cancelled` under the state
/// lock BEFORE killing is what makes the running worker record the killed run as
/// cancelled rather than failed.
pub fn cancel(dir: &Path, job_id: &str) -> Result<serde_json::Value, String> {
    validate_job_id(job_id)?;
    let (already_terminal, current_phase) = {
        let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let mut state = read_state_locked(dir, job_id)?;
        let phase = state.get("phase").and_then(|p| p.as_str()).unwrap_or("").to_string();
        if terminal(&phase) {
            (true, phase)
        } else {
            mark_cancelled(job_id);
            apply_phase(&mut state, "cancelled");
            state["cancellation_requested"] = serde_json::json!(true);
            state["cancelled_at"] = serde_json::json!(Utc::now().to_rfc3339());
            write_state_locked(dir, job_id, &state)?;
            (false, "cancelled".to_string())
        }
    };

    if already_terminal {
        return Ok(serde_json::json!({
            "job_id": job_id,
            "cancelled": false,
            "phase": current_phase,
            "note": "job already reached a terminal phase; cancellation is a no-op",
        }));
    }

    // Kill outside the lock. Force-kill the whole tree so no orphaned Lean/Lake
    // child survives the cancel.
    let pids = job_pids(job_id);
    let mut kills = Vec::new();
    for pid in &pids {
        kills.push(serde_json::json!({
            "pid": pid,
            "termination": super::kill_verifier_process_tree(*pid, true),
        }));
    }
    Ok(serde_json::json!({
        "job_id": job_id,
        "cancelled": true,
        "phase": "cancelled",
        "killed_process_trees": kills,
    }))
}

/// Returns the ordered phase-transition history for a job — the "progress" signal
/// without a streaming transport. An interrupted job gets a synthetic trailing
/// `interrupted` event (not persisted) so the timeline stays honest.
pub fn events(dir: &Path, job_id: &str) -> Result<serde_json::Value, String> {
    validate_job_id(job_id)?;
    let _lock = VERIFICATION_STATE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let state = read_state_locked(dir, job_id)?;
    let mut phases = state
        .get("phases")
        .and_then(|p| p.as_array())
        .cloned()
        .unwrap_or_default();
    if let Some((interrupted_phase, reason)) = interrupted_view(&state) {
        phases.push(serde_json::json!({
            "phase": interrupted_phase,
            "at": Utc::now().to_rfc3339(),
            "reason": reason,
            "synthetic": true,
        }));
    }
    Ok(serde_json::json!({ "job_id": job_id, "phases": phases }))
}

fn validate_job_id(job_id: &str) -> Result<(), String> {
    Uuid::parse_str(job_id).map_err(|e| format!("invalid verification job id: {e}"))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::{
        LeanVerificationOutcome, LeanVerificationResult, Obligation, ObligationCreator,
        ObligationKind, ObligationStatus, VerifierResourcePolicy,
    };

    fn test_obligation(statement: &str) -> Obligation {
        Obligation {
            id: Uuid::new_v4(),
            problem_version_id: Uuid::new_v4(),
            kind: ObligationKind::Root,
            theorem_name: "T".to_string(),
            lean_statement: statement.to_string(),
            statement_hash: crate::hashing::canonical_hash(&statement).unwrap(),
            natural_description: String::new(),
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
        }
    }

    fn test_request(statement: &str, proof: &str) -> VerificationJobRequest {
        VerificationJobRequest {
            obligation: test_obligation(statement),
            candidate_source: proof.to_string(),
            approved_dependency_ids: vec![],
            environment: "test-env-hash".to_string(),
            import_manifest: vec!["Mathlib".to_string()],
            proof_format: ProofFormat::FlatTacticSequence,
        }
    }

    fn canned_pass(req: &VerificationJobRequest) -> LeanVerificationResult {
        LeanVerificationResult {
            outcome: LeanVerificationOutcome::KernelPass,
            attempt_id: Uuid::new_v4(),
            obligation_id: req.obligation.id,
            theorem_name: req.obligation.theorem_name.clone(),
            expected_statement_hash: req.obligation.statement_hash.clone(),
            elaborated_statement_hash: None,
            environment_hash: req.environment.clone(),
            proof_source_hash: String::new(),
            compiled_artifact_hash: None,
            proof_term_hash: None,
            diagnostic: None,
            all_diagnostics: vec![],
            dependency_use_report: None,
            resource_policy: None,
            output_receipt: None,
            durability_job: None,
            wall_time_ms: 1,
            lean_cpu_time_ms: 1,
        }
    }

    fn wait_for_phase(dir: &Path, job_id: &str, target: &str) -> serde_json::Value {
        for _ in 0..200 {
            let s = status(dir, job_id).unwrap();
            if s["phase"] == target {
                return s;
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        panic!("job {job_id} never reached phase {target}; last = {:?}", status(dir, job_id));
    }

    #[test]
    fn submit_returns_immediately_and_runs_to_complete() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path().join("verification-jobs");
        let policy = VerifierResourcePolicy::default();
        let req = test_request("1 = 1", "rfl");

        let receipt = submit(&dir, &policy, req, Box::new(|r| Ok(canned_pass(r)))).unwrap();
        // Submission returns a durable id + hashes + queued state, not a verdict.
        assert!(!receipt.job_id.is_empty());
        assert!(!receipt.source_hash.is_empty());
        assert_eq!(receipt.environment_hash, "test-env-hash");
        assert!(!receipt.reused);
        assert!(matches!(receipt.phase.as_str(), "queued" | "staging" | "elaborating" | "complete"));

        let final_status = wait_for_phase(&dir, &receipt.job_id, "complete");
        // Lightweight status must NOT carry the heavy result payload.
        assert!(final_status.get("all_diagnostics").is_none());
        assert!(final_status.get("output_receipt").is_none());
        assert!(final_status.get("resource_policy").is_none());
        assert!(final_status["result_artifact_hash"].as_str().is_some());
        assert_eq!(final_status["outcome"], "kernel_pass");

        // The full payload is only reachable through `result`.
        let full = result(&dir, &receipt.job_id).unwrap();
        assert_eq!(full["available"], true);
        assert_eq!(full["result"]["outcome"], "kernel_pass");
        assert!(full["result"]["all_diagnostics"].is_array());
    }

    #[test]
    fn identical_completed_job_is_reused_by_source_and_environment_hash() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path().join("verification-jobs");
        let policy = VerifierResourcePolicy::default();

        let r1 = submit(&dir, &policy, test_request("2 = 2", "rfl"), Box::new(|r| Ok(canned_pass(r)))).unwrap();
        wait_for_phase(&dir, &r1.job_id, "complete");

        // A second identical submission reuses the completed job rather than
        // launching a new run.
        let r2 = submit(&dir, &policy, test_request("2 = 2", "rfl"), Box::new(|r| Ok(canned_pass(r)))).unwrap();
        assert!(r2.reused);
        assert_eq!(r2.job_id, r1.job_id);
        assert_eq!(r2.phase, "complete");

        // A different proof body → different source hash → NOT reused.
        let r3 = submit(&dir, &policy, test_request("2 = 2", "by norm_num"), Box::new(|r| Ok(canned_pass(r)))).unwrap();
        assert!(!r3.reused);
        assert_ne!(r3.job_id, r1.job_id);
    }

    #[test]
    fn cancel_marks_job_cancelled_and_wins_over_late_completion() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path().join("verification-jobs");
        let policy = VerifierResourcePolicy::default();

        // Runner blocks until released so the job is reliably mid-run at cancel.
        let gate = Arc::new(AtomicBool::new(false));
        let gate_runner = gate.clone();
        let receipt = submit(
            &dir,
            &policy,
            test_request("3 = 3", "rfl"),
            Box::new(move |r| {
                for _ in 0..500 {
                    if gate_runner.load(Ordering::SeqCst) {
                        break;
                    }
                    std::thread::sleep(Duration::from_millis(5));
                }
                Ok(canned_pass(r))
            }),
        )
        .unwrap();

        // Cancel is synchronous and independent of the runner finishing.
        let cancel_res = cancel(&dir, &receipt.job_id).unwrap();
        assert_eq!(cancel_res["cancelled"], true);
        assert_eq!(cancel_res["phase"], "cancelled");

        // Release the runner; the worker's late completion must NOT overwrite the
        // cancelled state.
        gate.store(true, Ordering::SeqCst);
        std::thread::sleep(Duration::from_millis(100));
        let s = status(&dir, &receipt.job_id).unwrap();
        assert_eq!(s["phase"], "cancelled");
        assert_eq!(s["cancellation_requested"], true);

        // Cancelling an already-terminal job is a no-op.
        let again = cancel(&dir, &receipt.job_id).unwrap();
        assert_eq!(again["cancelled"], false);
    }

    #[test]
    fn stale_boot_id_is_reported_interrupted_not_running() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path().join("verification-jobs");
        fs::create_dir_all(&dir).unwrap();
        let job_id = Uuid::new_v4().to_string();
        // A job left mid-run (`elaborating`) by a previous process: its boot id is
        // not this process's boot id.
        let state = serde_json::json!({
            "job_id": job_id,
            "phase": "elaborating",
            "source_hash": "s",
            "environment_hash": "e",
            "boot_id": "some-previous-process-boot-id",
            "effective_timeout_ms": 300000,
            "queued_at": Utc::now().to_rfc3339(),
            "heartbeat_at": Utc::now().to_rfc3339(),
            "phases": [{"phase": "queued", "at": Utc::now().to_rfc3339()}],
        });
        fs::write(job_path(&dir, &job_id), serde_json::to_vec(&state).unwrap()).unwrap();

        let s = status(&dir, &job_id).unwrap();
        assert_eq!(s["phase"], "interrupted", "a job from a dead process must never be reported as still running");
        assert_eq!(s["interrupted"], true);

        // A terminal job from a previous process is NOT interrupted — it really
        // finished.
        let done_id = Uuid::new_v4().to_string();
        let mut done = state.clone();
        done["job_id"] = serde_json::json!(done_id);
        done["phase"] = serde_json::json!("complete");
        fs::write(job_path(&dir, &done_id), serde_json::to_vec(&done).unwrap()).unwrap();
        let ds = status(&dir, &done_id).unwrap();
        assert_eq!(ds["phase"], "complete");
        assert!(ds.get("interrupted").is_none());
    }

    #[test]
    fn events_returns_ordered_phase_history() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path().join("verification-jobs");
        let policy = VerifierResourcePolicy::default();
        let receipt = submit(&dir, &policy, test_request("4 = 4", "rfl"), Box::new(|r| Ok(canned_pass(r)))).unwrap();
        wait_for_phase(&dir, &receipt.job_id, "complete");
        let ev = events(&dir, &receipt.job_id).unwrap();
        let phases: Vec<String> = ev["phases"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| p["phase"].as_str().unwrap().to_string())
            .collect();
        assert_eq!(phases.first().unwrap(), "queued");
        assert_eq!(phases.last().unwrap(), "complete");
        assert!(phases.contains(&"elaborating".to_string()));
    }

    #[test]
    fn failed_infra_run_is_recorded_failed_with_error() {
        let tmp = tempfile::tempdir().unwrap();
        let dir = tmp.path().join("verification-jobs");
        let policy = VerifierResourcePolicy::default();
        let receipt = submit(
            &dir,
            &policy,
            test_request("5 = 5", "rfl"),
            Box::new(|_| Err("spawn failed".to_string())),
        )
        .unwrap();
        let s = wait_for_phase(&dir, &receipt.job_id, "failed");
        assert_eq!(s["error"], "spawn failed");
    }
}
