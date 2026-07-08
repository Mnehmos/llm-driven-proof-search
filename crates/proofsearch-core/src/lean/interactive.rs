//! Interactive (tactic-by-tactic) proof-state sessions — issue #159, part of
//! the Pantograph-style interaction epic (#158).
//!
//! ## What this is
//! [`InteractiveProofGateway`] is a backend abstraction for LIVE proof-state
//! interaction: start a session against a theorem statement, observe the
//! current goal state, apply one tactic at a time, and (once a path through
//! the resulting state tree looks complete) reconstruct a tactic script from
//! it. This is additive: it sits next to [`crate::lean::LeanGateway`], not on
//! top of it, and does not change `verify_exact`, `verify_module`, or any
//! `Solve` / `SubmitModule` / `GiveUp` / `Decompose` behavior.
//!
//! ## Pantograph is an optional backend, not the API
//! Nothing in this module spawns Pantograph, imports a Pantograph client, or
//! otherwise hardwires Pantograph into the core engine. `InteractiveProofGateway`
//! is deliberately backend-agnostic: a Pantograph-backed implementation is one
//! POSSIBLE future backend (not implemented here), alongside the deterministic
//! [`MockInteractiveGateway`] (for regression tests) and
//! [`FallbackInteractiveGateway`] (a backend that compiles and can stand in
//! for a real one but cleanly refuses every live-stepping operation). The MCP
//! API surface is this trait, not any particular backend's wire protocol —
//! callers program against `InteractiveProofGateway`, never against
//! Pantograph directly.
//!
//! ## Trust boundary — read this before wiring a real backend in
//! Every result produced by an `InteractiveProofGateway` implementation —
//! session state, tactic-application results, reconstructed scripts, replay
//! results — is SEARCH EVIDENCE ONLY. None of it marks an obligation proved,
//! and no caller may treat it as if it did. The only proof authority in this
//! system is [`crate::lean::LeanGateway`] (`verify_exact` / `verify_module`):
//! a script produced by [`InteractiveProofGateway::reconstruct_script`] must
//! still be submitted through that existing kernel-verification path — a
//! fresh, from-scratch Lean kernel check — before the corresponding
//! obligation's status can change. If a future backend's internal elaborator
//! ever disagrees with the real kernel, the kernel wins, always.
//!
//! No provider SDKs, API keys, or inference calls are introduced by this
//! module — every backend here is either a deterministic in-memory double or
//! a hard "not supported" stub.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use crate::models::action::ProofFormat;
use crate::models::{LeanDiagnostic, LeanDiagnosticCategory};

/// Opaque handle to a live interactive session. Only meaningful to the
/// backend that issued it via `start_session` — handing one gateway's handle
/// to a different gateway implementation is a caller bug this type does not
/// prevent structurally, the same way `LeanGateway` callers already carry
/// `environment` / `import_manifest` by convention rather than by type.
///
/// `JsonSchema` (added in #162, additive) so this type can appear inside the
/// `lean::observation` models without breaking their MCP-schema derivation —
/// it does not change this type's fields, `Serialize`/`Deserialize` shape, or
/// any #159 trait signature.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub struct InteractiveSessionHandle(pub Uuid);

/// Identifies one node in a session's proof-state tree — the state produced
/// either by `start_session` (the root, before any tactic) or by one
/// `apply_tactic` call. Tactics branch rather than overwrite: a session can
/// hold several sibling nodes reached from the same parent by different
/// tactics, which is why `apply_tactic` takes an explicit `parent_node`
/// instead of always extending an implicit "current" pointer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, JsonSchema)]
pub struct ProofStateNodeId(pub Uuid);

/// One open goal within a proof-state node, in Pantograph-shaped terms: a
/// target proposition plus the hypotheses in scope to prove it. Field names
/// deliberately mirror `LeanDiagnostic`'s `goal` / `local_context` /
/// `canonical_goal_hash` hooks (currently empty/`None` on the whole-theorem
/// path; issue #162 is specifically about filling those in) rather than
/// inventing a second vocabulary — a future real backend can populate both
/// from the same parsed Lean goal state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InteractiveGoal {
    pub goal: String,
    pub local_context: Vec<String>,
    pub canonical_goal_hash: Option<String>,
}

/// A snapshot of one node in a session's proof-state tree.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStateSnapshot {
    pub node: ProofStateNodeId,
    pub parent: Option<ProofStateNodeId>,
    /// The tactic text that produced this node from `parent` (`None` for the
    /// session's root node, returned by `start_session`).
    pub tactic_applied: Option<String>,
    /// Remaining open goals at this node. Empty means every goal at this node
    /// has been closed — see `is_solved`.
    pub goals: Vec<InteractiveGoal>,
    /// `true` iff `goals` is empty, i.e. this node has no remaining
    /// obligations. This is a claim about the SESSION's internal state only —
    /// see the module-level trust-boundary note; it is never a proof of the
    /// original theorem by itself.
    pub is_solved: bool,
}

/// Outcome of one `apply_tactic` call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TacticOutcome {
    /// The tactic elaborated and produced a new node.
    Applied,
    /// The tactic failed to apply (elaboration/tactic error) — see `diagnostic`.
    Failed,
}

/// Structured result of one `apply_tactic` call. Exactly one of `state` /
/// `diagnostic` is populated, matching `outcome`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticApplicationResult {
    pub outcome: TacticOutcome,
    /// Present iff `outcome == Applied`.
    pub state: Option<ProofStateSnapshot>,
    /// Present iff `outcome == Failed`. Reuses [`LeanDiagnostic`] rather than
    /// a parallel type — see the module doc.
    pub diagnostic: Option<LeanDiagnostic>,
}

/// Everything needed to start a session, held together so `start_session`'s
/// signature doesn't grow a sixth positional string/slice argument.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InteractiveSessionRequest {
    pub problem_namespace: String,
    pub theorem_name: String,
    pub statement: String,
    pub imports: Vec<String>,
    /// Approved dependency obligation ids this session's environment may
    /// assume — the interactive analogue of `verify_exact`'s
    /// `approved_dependency_ids`.
    pub dependencies: Vec<Uuid>,
}

/// Result of `start_session`: a handle plus the initial (pre-tactic) state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InteractiveSessionStart {
    pub session: InteractiveSessionHandle,
    pub initial_state: ProofStateSnapshot,
}

/// A tactic script reconstructed from the root-to-`selected node` path in a
/// session's proof-state tree. This is SEARCH EVIDENCE, not a verified proof
/// — see the module-level trust-boundary note. `tactic_block` /
/// `proof_format` are shaped to be handed directly to a whole-theorem
/// `Solve { proof_term, proof_format }` submission for kernel verification,
/// nothing more.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReconstructedScript {
    pub tactic_block: String,
    pub proof_format: ProofFormat,
    /// Root-to-`selected` node path this was reconstructed from.
    pub node_path: Vec<ProofStateNodeId>,
    /// `true` iff the selected node's `is_solved` was `true` at
    /// reconstruction time. Still not proof authority — only the kernel is.
    pub reports_complete: bool,
    /// The same per-step tactic strings `tactic_block` was built from
    /// (`tactic_block == tactics.join("\n")`), kept as their own field
    /// rather than making a caller re-split `tactic_block` to recover them.
    /// Issue #163: `tactic_block.split('\n')` is NOT a safe inverse of the
    /// join — a single step's tactic text can itself legitimately contain
    /// embedded newlines (the same multi-line tactic-block shape
    /// `EpisodeStepArgs`/`Solve` already has to support elsewhere in this
    /// codebase), which `split('\n')` would fragment into spurious extra
    /// pseudo-steps. `tactics.len() == node_path.len().saturating_sub(1)`
    /// (one tactic per edge on the root-to-selected path; zero for a
    /// root-only reconstruction).
    pub tactics: Vec<String>,
}

/// One step of a recorded session, replayable against a fresh session for
/// deterministic regression testing / audit. `parent_step` indexes into the
/// trace's own `steps` (not a live session's node ids, which are only valid
/// within the session that produced them) so a trace can be replayed against
/// any fresh session a backend starts, independent of how that backend
/// assigns node identity.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InteractiveTraceStep {
    /// Index into the trace's `steps` (0-based) of the parent step's
    /// resulting node, or `None` to apply this tactic to the session's root
    /// (the state `start_session` returned, before any tactic). Must be
    /// strictly less than this step's own index.
    pub parent_step: Option<usize>,
    pub tactic: String,
}

/// A full recorded session trace: enough to start an equivalent session and
/// replay every tactic application against it in order.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InteractiveSessionTrace {
    pub request: InteractiveSessionRequest,
    pub steps: Vec<InteractiveTraceStep>,
}

/// Result of replaying a trace against a fresh session: the fresh session's
/// handle plus one `TacticApplicationResult` per replayed step, in order.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SessionReplayResult {
    pub session: InteractiveSessionHandle,
    pub steps: Vec<TacticApplicationResult>,
}

/// Backend abstraction for live, tactic-by-tactic proof-state interaction.
///
/// See the module doc for the trust-boundary rule: results from this trait
/// are search evidence, never proof authority. [`crate::lean::LeanGateway`]
/// remains the only path that can mark an obligation proved.
///
/// Backend policy (issue #159): this trait does not require Pantograph for
/// its first schema pass. It permits (a) a future Pantograph-backed gateway
/// (not implemented here), (b) the deterministic [`MockInteractiveGateway`]
/// below for regression tests, and (c) [`FallbackInteractiveGateway`], which
/// compiles and can stand in for a real backend but cleanly refuses every
/// live-stepping operation.
pub trait InteractiveProofGateway {
    /// Starts a new session for `request.statement` under `request.imports`
    /// and `request.dependencies`, returning a handle plus the initial
    /// (pre-tactic, single-goal) state.
    fn start_session(&self, request: &InteractiveSessionRequest) -> Result<InteractiveSessionStart, String>;

    /// Returns the session's current proof-state node (the most recently
    /// reached node — the root if no tactic has been applied yet).
    fn observe_state(&self, session: InteractiveSessionHandle) -> Result<ProofStateSnapshot, String>;

    /// Applies `tactic` at `parent_node`, producing a new node on success (or
    /// a structured diagnostic on failure). `parent_node` need not be the
    /// session's current node — branching from an earlier node is allowed.
    fn apply_tactic(
        &self,
        session: InteractiveSessionHandle,
        parent_node: ProofStateNodeId,
        tactic: &str,
    ) -> Result<TacticApplicationResult, String>;

    /// Releases any resources held for `session`. After this call, every
    /// other operation on `session` must return an `Err`, not panic.
    fn close_session(&self, session: InteractiveSessionHandle) -> Result<(), String>;

    /// Reconstructs the tactic script along the root-to-`selected_node` path.
    /// SEARCH EVIDENCE ONLY — see the module-level trust-boundary note.
    fn reconstruct_script(
        &self,
        session: InteractiveSessionHandle,
        selected_node: ProofStateNodeId,
    ) -> Result<ReconstructedScript, String>;

    /// Starts a fresh session from `trace.request` and replays `trace.steps`
    /// against it in order, for deterministic regression testing / audit.
    fn replay_session(&self, trace: &InteractiveSessionTrace) -> Result<SessionReplayResult, String>;
}

/// One in-memory session tracked by [`MockInteractiveGateway`].
struct MockSession {
    nodes: HashMap<ProofStateNodeId, ProofStateSnapshot>,
    current: ProofStateNodeId,
    closed: bool,
}

/// A deterministic, in-memory test/dummy backend (issue #159's `(b)`): no
/// Lean process, no Pantograph, no I/O. Every session starts with exactly one
/// goal (the requested statement, verbatim, with no hypotheses — the
/// `local_context` / `canonical_goal_hash` hooks stay empty/`None` here just
/// like `RealLeanGateway`'s current diagnostics, pending issue #162). Every
/// syntactically nonempty tactic deterministically closes the first open goal
/// at its parent node — this backend never asks a real elaborator whether the
/// tactic actually discharges the goal, so it is a schema-shape double for
/// tests, never evidence that any Lean statement holds.
#[derive(Default)]
pub struct MockInteractiveGateway {
    sessions: Mutex<HashMap<InteractiveSessionHandle, MockSession>>,
}

impl MockInteractiveGateway {
    pub fn new() -> Self {
        Self::default()
    }
}

impl InteractiveProofGateway for MockInteractiveGateway {
    fn start_session(&self, request: &InteractiveSessionRequest) -> Result<InteractiveSessionStart, String> {
        let root_id = ProofStateNodeId(Uuid::new_v4());
        let root = ProofStateSnapshot {
            node: root_id,
            parent: None,
            tactic_applied: None,
            goals: vec![InteractiveGoal {
                goal: request.statement.clone(),
                local_context: vec![],
                canonical_goal_hash: None,
            }],
            is_solved: false,
        };
        let mut nodes = HashMap::new();
        nodes.insert(root_id, root.clone());

        let session_id = InteractiveSessionHandle(Uuid::new_v4());
        let mut sessions = self.sessions.lock().map_err(|_| "mock gateway session lock poisoned".to_string())?;
        sessions.insert(session_id, MockSession { nodes, current: root_id, closed: false });

        Ok(InteractiveSessionStart { session: session_id, initial_state: root })
    }

    fn observe_state(&self, session: InteractiveSessionHandle) -> Result<ProofStateSnapshot, String> {
        let sessions = self.sessions.lock().map_err(|_| "mock gateway session lock poisoned".to_string())?;
        let s = sessions.get(&session).ok_or("unknown interactive session")?;
        if s.closed {
            return Err("session is closed".to_string());
        }
        s.nodes.get(&s.current).cloned().ok_or_else(|| "internal error: current node missing from session".to_string())
    }

    fn apply_tactic(
        &self,
        session: InteractiveSessionHandle,
        parent_node: ProofStateNodeId,
        tactic: &str,
    ) -> Result<TacticApplicationResult, String> {
        if tactic.trim().is_empty() {
            return Err("tactic text must not be empty".to_string());
        }
        let mut sessions = self.sessions.lock().map_err(|_| "mock gateway session lock poisoned".to_string())?;
        let s = sessions.get_mut(&session).ok_or("unknown interactive session")?;
        if s.closed {
            return Err("session is closed".to_string());
        }
        let parent = s.nodes.get(&parent_node).cloned().ok_or("unknown proof-state node")?;

        if parent.goals.is_empty() {
            // Deterministic failure: nothing left to apply a tactic to at this node.
            return Ok(TacticApplicationResult {
                outcome: TacticOutcome::Failed,
                state: None,
                diagnostic: Some(LeanDiagnostic {
                    category: LeanDiagnosticCategory::TacticFailure,
                    primary_message: "no goals remaining at this node".to_string(),
                    source_span: None,
                    goal: None,
                    local_context: vec![],
                    unsolved_goals: vec![],
                    used_dependencies: vec![],
                    error_code: None,
                    canonical_goal_hash: None,
                }),
            });
        }

        // Deterministic rule: close exactly the first open goal on every
        // syntactically nonempty tactic. See the struct doc — this is a
        // schema-shape double, not a soundness check.
        let mut remaining = parent.goals.clone();
        remaining.remove(0);
        let new_id = ProofStateNodeId(Uuid::new_v4());
        let new_state = ProofStateSnapshot {
            node: new_id,
            parent: Some(parent_node),
            tactic_applied: Some(tactic.to_string()),
            is_solved: remaining.is_empty(),
            goals: remaining,
        };
        s.nodes.insert(new_id, new_state.clone());
        s.current = new_id;

        Ok(TacticApplicationResult { outcome: TacticOutcome::Applied, state: Some(new_state), diagnostic: None })
    }

    fn close_session(&self, session: InteractiveSessionHandle) -> Result<(), String> {
        let mut sessions = self.sessions.lock().map_err(|_| "mock gateway session lock poisoned".to_string())?;
        let s = sessions.get_mut(&session).ok_or("unknown or already-closed interactive session")?;
        s.closed = true;
        Ok(())
    }

    fn reconstruct_script(
        &self,
        session: InteractiveSessionHandle,
        selected_node: ProofStateNodeId,
    ) -> Result<ReconstructedScript, String> {
        let sessions = self.sessions.lock().map_err(|_| "mock gateway session lock poisoned".to_string())?;
        let s = sessions.get(&session).ok_or("unknown interactive session")?;
        if s.closed {
            return Err("session is closed".to_string());
        }

        let mut cur = s.nodes.get(&selected_node).cloned().ok_or("unknown proof-state node")?;
        let reports_complete = cur.is_solved;
        let mut node_path = vec![selected_node];
        let mut tactics = vec![];
        loop {
            if let Some(t) = &cur.tactic_applied {
                tactics.push(t.clone());
            }
            match cur.parent {
                Some(p) => {
                    node_path.push(p);
                    cur = s.nodes.get(&p).cloned().ok_or("broken proof-state chain: parent node missing")?;
                }
                None => break,
            }
        }
        node_path.reverse();
        tactics.reverse();

        Ok(ReconstructedScript {
            tactic_block: tactics.join("\n"),
            proof_format: ProofFormat::FlatTacticSequence,
            node_path,
            reports_complete,
            tactics,
        })
    }

    fn replay_session(&self, trace: &InteractiveSessionTrace) -> Result<SessionReplayResult, String> {
        let start = self.start_session(&trace.request)?;
        let mut node_of_step: Vec<Option<ProofStateNodeId>> = Vec::with_capacity(trace.steps.len());
        let mut steps = Vec::with_capacity(trace.steps.len());

        for (i, step) in trace.steps.iter().enumerate() {
            let parent_node = match step.parent_step {
                Some(idx) if idx < i => node_of_step[idx].ok_or_else(|| {
                    format!("replay step {i}: parent_step {idx} did not produce a state (it failed during replay)")
                })?,
                Some(idx) => return Err(format!("replay step {i}: parent_step {idx} must reference an earlier step")),
                None => start.initial_state.node,
            };
            let result = self.apply_tactic(start.session, parent_node, &step.tactic)?;
            node_of_step.push(result.state.as_ref().map(|s| s.node));
            steps.push(result);
        }

        Ok(SessionReplayResult { session: start.session, steps })
    }
}

/// A backend that implements `InteractiveProofGateway` but never actually
/// steps a proof (issue #159's `(c)`): every live-stepping operation returns
/// a clear "not supported" error instead of silently no-opting or panicking.
/// Exists so callers can always construct SOME `InteractiveProofGateway` —
/// even when no real interactive backend (Pantograph or otherwise) is
/// configured — without plumbing an `Option<dyn InteractiveProofGateway>`
/// through every call site. Compiles and is fully safe to hold; it simply has
/// nothing to offer.
#[derive(Debug, Default, Clone, Copy)]
pub struct FallbackInteractiveGateway;

const FALLBACK_NOT_SUPPORTED: &str = "this gateway does not support live tactic-by-tactic proof stepping \
    (no interactive backend, e.g. Pantograph, is configured) — submit a complete proof through \
    the existing Solve or SubmitModule action instead";

impl InteractiveProofGateway for FallbackInteractiveGateway {
    fn start_session(&self, _request: &InteractiveSessionRequest) -> Result<InteractiveSessionStart, String> {
        Err(FALLBACK_NOT_SUPPORTED.to_string())
    }

    fn observe_state(&self, _session: InteractiveSessionHandle) -> Result<ProofStateSnapshot, String> {
        Err(FALLBACK_NOT_SUPPORTED.to_string())
    }

    fn apply_tactic(
        &self,
        _session: InteractiveSessionHandle,
        _parent_node: ProofStateNodeId,
        _tactic: &str,
    ) -> Result<TacticApplicationResult, String> {
        Err(FALLBACK_NOT_SUPPORTED.to_string())
    }

    fn close_session(&self, _session: InteractiveSessionHandle) -> Result<(), String> {
        Err(FALLBACK_NOT_SUPPORTED.to_string())
    }

    fn reconstruct_script(
        &self,
        _session: InteractiveSessionHandle,
        _selected_node: ProofStateNodeId,
    ) -> Result<ReconstructedScript, String> {
        Err(FALLBACK_NOT_SUPPORTED.to_string())
    }

    fn replay_session(&self, _trace: &InteractiveSessionTrace) -> Result<SessionReplayResult, String> {
        Err(FALLBACK_NOT_SUPPORTED.to_string())
    }
}

// ---------------------------------------------------------------------------
// Pantograph adapter (issue #166) — a real detection path, permanently
// fail-closed on live operations in this prototype
// ---------------------------------------------------------------------------

/// Result of genuinely probing this environment for a usable Pantograph
/// installation. Every variant is reachable from real filesystem/PATH state
/// (see [`detect_pantograph_status`]) — none of it is a hardcoded stub.
/// Deliberately has NO variant meaning "ready to step tactics": even the two
/// most favorable outcomes below (`ReferencedButNotFetched`'s opposite case,
/// `CompatibleButNoIpcImplemented`) only establish STATIC compatibility
/// (matching `lean-toolchain` files); this prototype adapter never spawns a
/// Pantograph process or speaks its wire protocol, so no state here ever
/// authorizes [`PantographInteractiveGateway`] to actually perform a live
/// operation — see the struct doc for why, and the module-level trust
/// boundary note for why that would still only be search evidence even if
/// it did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PantographStatus {
    /// No `pantograph`/`pantograph.exe` executable was found in any of the
    /// searched `PATH` directories, and this project's `lake-manifest.json`
    /// has no package entry named `pantograph`.
    NotInstalled { path_dirs_checked: usize },
    /// A `pantograph` executable exists somewhere on `PATH`, but this
    /// adapter has no IPC implementation to ask it anything (e.g. its
    /// declared Lean toolchain) — presence on `PATH` alone is not evidence
    /// of compatibility with this project's pinned toolchain.
    BinaryFoundNoIpc { binary_path: PathBuf },
    /// `lake-manifest.json` declares a `pantograph` package dependency, but
    /// no fetched checkout is present under `.lake/packages/pantograph` (or
    /// the legacy `lake-packages/pantograph`) to compare its own
    /// `lean-toolchain` against this project's — `lake build`/`lake update`
    /// has not actually pulled it down in this environment.
    ReferencedButNotFetched { manifest_rev: Option<String> },
    /// This project's own `lean-toolchain` could not be read (the same
    /// condition [`crate::lean::detect_environment`] reports as `None`,
    /// i.e. `lean_available == false`) — compatibility cannot be assessed
    /// without it, independent of whatever was found for Pantograph itself.
    ProjectToolchainUndetected,
    /// A fetched Pantograph checkout's `lean-toolchain` was compared
    /// byte-for-byte (after trimming) against this project's own — and they
    /// DIFFER. The strongest evidence of incompatibility this adapter can
    /// gather without invoking either toolchain.
    IncompatibleToolchain { pantograph_toolchain: String, project_toolchain: String },
    /// A fetched checkout's `lean-toolchain` matches this project's exactly.
    /// The strongest STATIC evidence of compatibility available — but this
    /// prototype adapter still has no real process/IPC implementation
    /// behind it, so it still cannot perform a single live operation. See
    /// the struct doc for what a real integration would still need to add.
    CompatibleButNoIpcImplemented { toolchain: String },
}

impl PantographStatus {
    /// Always `false` in this prototype — see the enum doc: no variant here
    /// represents a backend actually capable of live tactic stepping, only
    /// gradations of "why not, specifically."
    pub fn is_available(&self) -> bool {
        false
    }

    /// Human-readable explanation, safe to surface directly in an MCP error
    /// message or `environment_describe` capability flag.
    pub fn reason(&self) -> String {
        match self {
            PantographStatus::NotInstalled { path_dirs_checked } => format!(
                "no `pantograph` executable found on PATH ({path_dirs_checked} directories searched) \
                 and no `pantograph` package entry in this project's lake-manifest.json — Pantograph is not installed in this environment"
            ),
            PantographStatus::BinaryFoundNoIpc { binary_path } => format!(
                "a `pantograph` executable was found at {} on PATH, but this adapter has no process/IPC \
                 implementation to query or drive it — presence on PATH is not itself confirmation of \
                 toolchain compatibility or a working integration",
                binary_path.display()
            ),
            PantographStatus::ReferencedButNotFetched { manifest_rev } => format!(
                "lake-manifest.json declares a `pantograph` dependency{} but no fetched checkout is present \
                 under .lake/packages/pantograph — run the project's normal `lake update`/`lake build` to \
                 fetch it before compatibility can be assessed",
                manifest_rev.as_deref().map(|r| format!(" (rev {r})")).unwrap_or_default()
            ),
            PantographStatus::ProjectToolchainUndetected => {
                "this project's own lean-toolchain/lake-manifest.json could not be read (same condition \
                 RealLeanGateway reports as lean_available=false) — compatibility cannot be assessed \
                 without a pinned toolchain to compare against".to_string()
            }
            PantographStatus::IncompatibleToolchain { pantograph_toolchain, project_toolchain } => format!(
                "fetched Pantograph checkout declares lean-toolchain '{pantograph_toolchain}', which does not \
                 match this project's pinned '{project_toolchain}' — incompatible toolchains, refusing to proceed"
            ),
            PantographStatus::CompatibleButNoIpcImplemented { toolchain } => format!(
                "fetched Pantograph checkout's lean-toolchain matches this project's pinned '{toolchain}' \
                 exactly, but this prototype adapter has no real process spawning/IPC implementation — static \
                 toolchain compatibility alone does not make live tactic stepping available"
            ),
        }
    }
}

/// Searches `PATH` (or, in tests, an explicit override string standing in
/// for it, so tests never mutate the real process-wide `PATH` env var) for
/// an executable named `name`. Windows resolves bare names via `PATHEXT`
/// (`.exe`/`.cmd`/`.bat`, most commonly); this checks the same handful of
/// suffixes plus the bare name, which covers how `pantograph` would
/// realistically be installed (a prebuilt `.exe`, or a `lake exe`-style
/// wrapper script) without adding a `which`-style crate dependency this
/// workspace doesn't already have. Returns the number of directories
/// searched (for the "not found" message) alongside the first hit, if any.
fn find_binary_on_path(name: &str, path_override: Option<&str>) -> (usize, Option<PathBuf>) {
    let path_var = match path_override {
        Some(p) => std::ffi::OsString::from(p),
        None => std::env::var_os("PATH").unwrap_or_default(),
    };
    let dirs: Vec<PathBuf> = std::env::split_paths(&path_var).collect();
    let candidates: Vec<String> = if cfg!(windows) {
        vec![format!("{name}.exe"), format!("{name}.cmd"), format!("{name}.bat"), name.to_string()]
    } else {
        vec![name.to_string()]
    };
    for dir in &dirs {
        for candidate in &candidates {
            let path = dir.join(candidate);
            if path.is_file() {
                return (dirs.len(), Some(path));
            }
        }
    }
    (dirs.len(), None)
}

/// Looks up one named package's `rev` field in `lean_project_path`'s
/// `lake-manifest.json` — the same file/shape
/// [`crate::lean::detect_environment`] already reads to find Mathlib's
/// pinned revision, reused here (not reinvented) for `package_name` instead.
fn lake_manifest_package_rev(lean_project_path: &Path, package_name: &str) -> Option<String> {
    let manifest_str = std::fs::read_to_string(lean_project_path.join("lake-manifest.json")).ok()?;
    let manifest: serde_json::Value = serde_json::from_str(&manifest_str).ok()?;
    manifest
        .get("packages")?
        .as_array()?
        .iter()
        .find(|p| p.get("name").and_then(|n| n.as_str()) == Some(package_name))?
        .get("rev")
        .and_then(|r| r.as_str())
        .map(|s| s.to_string())
}

/// Reads a fetched Pantograph checkout's own `lean-toolchain` file, checking
/// both the current (`.lake/packages/...`) and legacy (`lake-packages/...`)
/// Lake layouts — the same two layouts this codebase's Mathlib source-scan
/// path (`mathlib_source_dir`) already has to account for.
fn fetched_pantograph_toolchain(lean_project_path: &Path) -> Option<String> {
    for rel in [".lake/packages/pantograph/lean-toolchain", "lake-packages/pantograph/lean-toolchain"] {
        if let Ok(content) = std::fs::read_to_string(lean_project_path.join(rel)) {
            return Some(content.trim().to_string());
        }
    }
    None
}

/// Genuinely probes this environment for a usable Pantograph installation
/// compatible with `lean_project_path`'s pinned Lean toolchain — real
/// filesystem/PATH checks, not a stub. See [`PantographStatus`] for what
/// each outcome means.
pub fn detect_pantograph_status(lean_project_path: &Path) -> PantographStatus {
    detect_pantograph_status_impl(lean_project_path, None)
}

/// `path_override` lets tests substitute a synthetic `PATH` string instead
/// of mutating the real, process-global `PATH` env var (which would race
/// against Rust's parallel test execution) — `None` (the only value
/// production code ever passes, via [`detect_pantograph_status`]) means
/// "use the real PATH".
fn detect_pantograph_status_impl(lean_project_path: &Path, path_override: Option<&str>) -> PantographStatus {
    let (path_dirs_checked, binary_path) = find_binary_on_path("pantograph", path_override);
    let manifest_rev = lake_manifest_package_rev(lean_project_path, "pantograph");

    if manifest_rev.is_none() {
        return match binary_path {
            Some(binary_path) => PantographStatus::BinaryFoundNoIpc { binary_path },
            None => PantographStatus::NotInstalled { path_dirs_checked },
        };
    }

    // A lake dependency on `pantograph` IS declared — assess it against
    // this project's own pinned toolchain using the SAME detection
    // mechanism RealLeanGateway/detect_environment already uses (issue
    // #166's compatibility requirement), not a second, parallel notion of
    // "the pinned toolchain".
    let Some(project_env) = crate::lean::detect_environment(lean_project_path) else {
        return PantographStatus::ProjectToolchainUndetected;
    };
    match fetched_pantograph_toolchain(lean_project_path) {
        Some(pantograph_toolchain) if pantograph_toolchain == project_env.toolchain => {
            PantographStatus::CompatibleButNoIpcImplemented { toolchain: project_env.toolchain }
        }
        Some(pantograph_toolchain) => PantographStatus::IncompatibleToolchain {
            pantograph_toolchain,
            project_toolchain: project_env.toolchain,
        },
        None => PantographStatus::ReferencedButNotFetched { manifest_rev },
    }
}

/// Prototype [`InteractiveProofGateway`] adapter for Pantograph — issue
/// #166, evaluating Pantograph as an optional backend for the interactive
/// session epic (#158). Follows the same shape as [`FallbackInteractiveGateway`]
/// (compiles, implements the trait, cleanly refuses every live-stepping
/// operation) but backs its refusal with a REAL, filesystem/PATH-based
/// probe of this environment (see [`detect_pantograph_status`]) instead of
/// an unconditional stub — the returned error explains WHICH of several
/// concrete reasons applies (missing binary vs. undetected/incompatible
/// toolchain vs. detected-but-unintegrated), not just "not supported".
///
/// ## Why this can never reach "available" in this codebase (yet)
/// Per issue #166's explicit scope, this adapter does not shell out to,
/// link against, or vendor a real Pantograph process — no new crate
/// dependency was added for this, and none is needed, since detection here
/// is PATH/filesystem probing only. That means even the most favorable
/// [`PantographStatus`] this adapter can compute
/// (`CompatibleButNoIpcImplemented`, a fetched checkout's `lean-toolchain`
/// matching this project's own byte-for-byte) still cannot authorize a live
/// session: there is no code anywhere in this adapter that spawns a
/// `pantograph` process, speaks its stdio/RPC protocol, or parses its
/// responses. Every [`InteractiveProofGateway`] method below is
/// unconditionally `Err` — the specific message just improves with the
/// detected status.
///
/// ## Known compatibility risks a REAL integration would still need to handle
/// (this is deliberately concrete, not a generic disclaimer — these are the
/// specific hazards this prototype's static-file checks do NOT cover):
/// - **Toolchain version drift**: this project's `lean-toolchain` can be
///   bumped (as it already has been across this epic's issues) independent
///   of any Pantograph release cadence. A byte-equal `lean-toolchain` match
///   at detection time says nothing about whether it STAYS equal after the
///   next `lean-toolchain` bump lands in this repo — a real integration
///   needs this check to run on every session start, not once, and needs a
///   CI signal (not just a runtime probe) when the two drift apart.
/// - **Mathlib revision mismatches**: Pantograph's own Lake manifest pins
///   its OWN Mathlib revision (transitively, as one of its dependencies).
///   Even with an exactly matching Lean toolchain, a real integration must
///   confirm Pantograph's resolved Mathlib commit does not diverge from
///   this project's own `lake-manifest.json` Mathlib `rev` (the same field
///   [`crate::lean::detect_environment`] already reads) — two different
///   Mathlib commits under the same Lean version can still disagree on
///   declaration names/signatures a proof session would reference, in
///   exactly the way `lookup_declarations`'s "environmental scope collapse"
///   documentation already warns about for import manifests generally.
/// - **Process lifecycle/IPC concerns**: Pantograph is a long-lived
///   subprocess exposing a stateful proof-search REPL (spawn once, issue
///   many tactic-application requests against live in-process Lean
///   elaborator state, eventually tear down) — nothing like the
///   short-lived, one-shot `lake env lean --json` invocations
///   `RealLeanGateway` already uses per verification call. A real adapter
///   needs: (a) a supervised child process per session (or a pool), tied to
///   `InteractiveSessionHandle`'s lifetime, not `LeanGateway`'s stateless
///   spawn-per-call model; (b) a wire protocol codec for whatever framing
///   Pantograph's REPL actually uses; (c) explicit handling for a crashed
///   or hung Pantograph process mid-session (this adapter's `close_session`
///   contract — "every other operation on `session` must return an `Err`,
///   not panic" — would need to hold even when the underlying OS process is
///   already dead); (d) concurrency behavior when multiple sessions are
///   open at once (one process per session is the safe default, but has
///   real memory/startup-latency cost per session that a pooled design
///   would need to justify against).
/// - **Trust boundary is unaffected either way**: none of the above changes
///   this module's core rule — a real Pantograph-backed session's results
///   remain search evidence only; `reconstruct_script`'s output still has
///   to go through `LeanGateway::verify_exact`/`verify_module` (the real
///   kernel) before any obligation status can change. A future real
///   integration must not add any shortcut around that.
#[derive(Debug, Clone)]
pub struct PantographInteractiveGateway {
    status: PantographStatus,
}

impl PantographInteractiveGateway {
    /// Runs real detection (see [`detect_pantograph_status`]) against
    /// `lean_project_path` — the same project path `RealLeanGateway` and
    /// `detect_environment` are constructed against — and captures the
    /// result. Cheap (a handful of filesystem stats plus a small JSON
    /// parse), so callers may construct a fresh instance per call rather
    /// than needing to cache one.
    pub fn new(lean_project_path: &Path) -> Self {
        Self { status: detect_pantograph_status(lean_project_path) }
    }

    pub fn status(&self) -> &PantographStatus {
        &self.status
    }

    fn unavailable_message(&self) -> String {
        format!("pantograph interactive backend is unavailable: {}", self.status.reason())
    }
}

impl InteractiveProofGateway for PantographInteractiveGateway {
    fn start_session(&self, _request: &InteractiveSessionRequest) -> Result<InteractiveSessionStart, String> {
        Err(self.unavailable_message())
    }

    fn observe_state(&self, _session: InteractiveSessionHandle) -> Result<ProofStateSnapshot, String> {
        Err(self.unavailable_message())
    }

    fn apply_tactic(
        &self,
        _session: InteractiveSessionHandle,
        _parent_node: ProofStateNodeId,
        _tactic: &str,
    ) -> Result<TacticApplicationResult, String> {
        Err(self.unavailable_message())
    }

    fn close_session(&self, _session: InteractiveSessionHandle) -> Result<(), String> {
        Err(self.unavailable_message())
    }

    fn reconstruct_script(
        &self,
        _session: InteractiveSessionHandle,
        _selected_node: ProofStateNodeId,
    ) -> Result<ReconstructedScript, String> {
        Err(self.unavailable_message())
    }

    fn replay_session(&self, _trace: &InteractiveSessionTrace) -> Result<SessionReplayResult, String> {
        Err(self.unavailable_message())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_request() -> InteractiveSessionRequest {
        InteractiveSessionRequest {
            problem_namespace: "ProofSearch.P_test".to_string(),
            theorem_name: "O_test".to_string(),
            statement: "1 + 1 = 2".to_string(),
            imports: vec!["Mathlib.Tactic.NormNum".to_string()],
            dependencies: vec![],
        }
    }

    #[test]
    fn mock_backend_start_apply_observe_close_flow() {
        let gw = MockInteractiveGateway::new();

        let start = gw.start_session(&sample_request()).expect("start_session should succeed");
        assert_eq!(start.initial_state.goals.len(), 1);
        assert_eq!(start.initial_state.goals[0].goal, "1 + 1 = 2");
        assert!(!start.initial_state.is_solved);
        assert!(start.initial_state.parent.is_none());

        let applied = gw
            .apply_tactic(start.session, start.initial_state.node, "norm_num")
            .expect("apply_tactic should succeed");
        assert_eq!(applied.outcome, TacticOutcome::Applied);
        assert!(applied.diagnostic.is_none());
        let new_state = applied.state.expect("Applied outcome must carry a state");
        assert!(new_state.goals.is_empty());
        assert!(new_state.is_solved);
        assert_eq!(new_state.parent, Some(start.initial_state.node));
        assert_eq!(new_state.tactic_applied.as_deref(), Some("norm_num"));

        // observe_state reflects the most recently reached node.
        let observed = gw.observe_state(start.session).expect("observe_state should succeed");
        assert_eq!(observed.node, new_state.node);
        assert!(observed.is_solved);

        // Reconstructing from the solved node yields exactly the one tactic applied.
        let script = gw
            .reconstruct_script(start.session, new_state.node)
            .expect("reconstruct_script should succeed");
        assert_eq!(script.tactic_block, "norm_num");
        assert!(script.reports_complete);
        assert_eq!(script.node_path, vec![start.initial_state.node, new_state.node]);
        assert_eq!(script.tactics, vec!["norm_num".to_string()]);

        gw.close_session(start.session).expect("close_session should succeed");

        // Session is closed: further interaction must fail cleanly, not panic.
        assert!(gw.observe_state(start.session).is_err());
        assert!(gw.apply_tactic(start.session, new_state.node, "rfl").is_err());
    }

    #[test]
    fn mock_backend_apply_tactic_on_solved_node_fails_cleanly() {
        let gw = MockInteractiveGateway::new();
        let start = gw.start_session(&sample_request()).unwrap();
        let applied = gw.apply_tactic(start.session, start.initial_state.node, "norm_num").unwrap();
        let solved_node = applied.state.unwrap().node;

        let second = gw.apply_tactic(start.session, solved_node, "rfl").unwrap();
        assert_eq!(second.outcome, TacticOutcome::Failed);
        assert!(second.state.is_none());
        assert!(second.diagnostic.is_some());
    }

    #[test]
    fn mock_backend_apply_tactic_rejects_empty_tactic_and_unknown_node() {
        let gw = MockInteractiveGateway::new();
        let start = gw.start_session(&sample_request()).unwrap();
        assert!(gw.apply_tactic(start.session, start.initial_state.node, "   ").is_err());
        assert!(gw
            .apply_tactic(start.session, ProofStateNodeId(Uuid::new_v4()), "norm_num")
            .is_err());
    }

    #[test]
    fn mock_backend_replay_session_is_deterministic() {
        let gw = MockInteractiveGateway::new();
        let trace = InteractiveSessionTrace {
            request: sample_request(),
            steps: vec![InteractiveTraceStep { parent_step: None, tactic: "norm_num".to_string() }],
        };

        let first = gw.replay_session(&trace).expect("first replay should succeed");
        let second = gw.replay_session(&trace).expect("second replay should succeed");

        assert_eq!(first.steps.len(), 1);
        assert_eq!(second.steps.len(), 1);
        assert_eq!(first.steps[0].outcome, second.steps[0].outcome);
        assert_eq!(
            first.steps[0].state.as_ref().unwrap().is_solved,
            second.steps[0].state.as_ref().unwrap().is_solved,
        );
        assert_eq!(
            first.steps[0].state.as_ref().unwrap().goals.len(),
            second.steps[0].state.as_ref().unwrap().goals.len(),
        );
    }

    /// Issue #163: `tactic_block` is `tactics.join("\n")`, so
    /// `tactic_block.split('\n')` is NOT a safe way to recover the original
    /// per-step tactics when a single step's own text legitimately contains
    /// an embedded newline (a multi-line tactic block, the same shape
    /// `EpisodeStepArgs`/`Solve` already supports elsewhere). `tactics`
    /// exists precisely so a caller (e.g. `proof_session_replay`'s backend
    /// mode) never has to re-split `tactic_block` and risk fragmenting one
    /// step into several spurious pseudo-steps.
    #[test]
    fn mock_backend_reconstruct_script_tactics_field_preserves_embedded_newlines_as_one_step() {
        let gw = MockInteractiveGateway::new();
        let start = gw.start_session(&sample_request()).unwrap();

        let multiline_tactic = "have h : 1 + 1 = 2 := by\n  norm_num\nexact h";
        let applied = gw.apply_tactic(start.session, start.initial_state.node, multiline_tactic).unwrap();
        assert_eq!(applied.outcome, TacticOutcome::Applied);
        let solved_node = applied.state.unwrap().node;

        let script = gw.reconstruct_script(start.session, solved_node).unwrap();
        // The naive (WRONG) recovery would split this into 3 pseudo-steps.
        assert_eq!(script.tactic_block.split('\n').count(), 3, "sanity: the flattened block does span 3 lines");
        // The CORRECT recovery: exactly one step, with its embedded newlines intact.
        assert_eq!(script.tactics.len(), 1, "a single multi-line tactic call must round-trip as ONE step: {:?}", script.tactics);
        assert_eq!(script.tactics[0], multiline_tactic);
        assert_eq!(script.tactic_block, multiline_tactic, "tactic_block == tactics.join(\"\\n\") for a single step");
    }

    #[test]
    fn mock_backend_reconstruct_script_rejects_closed_session() {
        let gw = MockInteractiveGateway::new();
        let start = gw.start_session(&sample_request()).unwrap();
        let applied = gw.apply_tactic(start.session, start.initial_state.node, "norm_num").unwrap();
        let solved_node = applied.state.unwrap().node;

        // reconstruct_script succeeds while the session is open ...
        assert!(gw.reconstruct_script(start.session, solved_node).is_ok());

        gw.close_session(start.session).expect("close_session should succeed");

        // ... but must fail cleanly once the session is closed, matching the
        // contract close_session's own doc comment makes for every other
        // operation (observe_state, apply_tactic).
        assert!(gw.reconstruct_script(start.session, solved_node).is_err());
    }

    #[test]
    fn fallback_backend_rejects_live_stepping_without_panicking() {
        let gw = FallbackInteractiveGateway;
        let dummy_session = InteractiveSessionHandle(Uuid::new_v4());
        let dummy_node = ProofStateNodeId(Uuid::new_v4());

        assert!(gw.start_session(&sample_request()).is_err());
        assert!(gw.observe_state(dummy_session).is_err());
        assert!(gw.apply_tactic(dummy_session, dummy_node, "rfl").is_err());
        assert!(gw.close_session(dummy_session).is_err());
        assert!(gw.reconstruct_script(dummy_session, dummy_node).is_err());
        let trace = InteractiveSessionTrace { request: sample_request(), steps: vec![] };
        assert!(gw.replay_session(&trace).is_err());
    }

    // -----------------------------------------------------------------
    // PantographInteractiveGateway (issue #166) — real-environment tests.
    // Pantograph is genuinely NOT installed anywhere in this environment
    // (no executable on PATH, no `pantograph` lake-manifest entry in the
    // repo's lean-checker/) — these tests exercise the actual detection
    // logic against the actual repo layout, not a mock or a skip.
    // -----------------------------------------------------------------

    /// This crate lives at `<repo>/crates/proofsearch-core`; the real Lean
    /// project this repo verifies against is `<repo>/lean-checker`, the
    /// SAME directory `RealLeanGateway`/`detect_environment` are pointed at
    /// via `PROOFSEARCH_LEAN_PROJECT_PATH` in this repo's own `.mcp.json`.
    fn real_lean_project_path() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean-checker")
    }

    /// Sanity check the fixture itself: the real lean-checker project this
    /// repo pins actually exists and has no pantograph dependency — i.e.
    /// the "Pantograph is genuinely absent" premise the rest of these tests
    /// rely on is real, not assumed.
    #[test]
    fn real_lean_project_has_no_pantograph_lake_dependency() {
        let project = real_lean_project_path();
        assert!(project.join("lean-toolchain").exists(), "fixture check: real lean-checker project should exist at {:?}", project);
        assert!(
            lake_manifest_package_rev(&project, "pantograph").is_none(),
            "fixture assumption broken: this repo's lake-manifest.json now declares a pantograph dependency \
             — PantographStatus::NotInstalled-focused tests below need updating"
        );
    }

    /// Real detection, in this actual environment: no `pantograph` binary
    /// on the real PATH (confirmed independently before writing this test —
    /// see the task notes) and no lake-manifest entry (confirmed by the
    /// fixture check above) must together classify as `NotInstalled`, using
    /// the REAL PATH (path_override = None), not a synthetic one.
    #[test]
    fn detect_pantograph_status_reports_not_installed_in_this_real_environment() {
        let status = detect_pantograph_status(&real_lean_project_path());
        match status {
            PantographStatus::NotInstalled { path_dirs_checked } => {
                assert!(path_dirs_checked > 0, "PATH should have at least one directory in any real shell environment");
            }
            other => panic!(
                "expected PantographStatus::NotInstalled in this real environment (no pantograph binary, no lake dependency), got {:?}",
                other
            ),
        }
        assert!(!status.is_available());
        assert!(status.reason().to_lowercase().contains("pantograph"));
    }

    /// Every `InteractiveProofGateway` method on a gateway constructed
    /// against the REAL (Pantograph-absent) environment must return a
    /// structured `Err`, never panic — this is the fail-closed acceptance
    /// criterion, exercised for real, not skipped/ignored.
    #[test]
    fn pantograph_gateway_fails_closed_on_every_trait_method_in_this_real_environment() {
        let gw = PantographInteractiveGateway::new(&real_lean_project_path());
        assert!(!gw.status().is_available());

        let dummy_session = InteractiveSessionHandle(Uuid::new_v4());
        let dummy_node = ProofStateNodeId(Uuid::new_v4());

        let start_err = gw.start_session(&sample_request()).expect_err("start_session must fail closed");
        assert!(start_err.contains("pantograph"), "error should name the backend: {start_err}");

        let observe_err = gw.observe_state(dummy_session).expect_err("observe_state must fail closed");
        assert!(observe_err.contains("pantograph"));

        let apply_err = gw.apply_tactic(dummy_session, dummy_node, "rfl").expect_err("apply_tactic must fail closed");
        assert!(apply_err.contains("pantograph"));

        let close_err = gw.close_session(dummy_session).expect_err("close_session must fail closed");
        assert!(close_err.contains("pantograph"));

        let reconstruct_err = gw.reconstruct_script(dummy_session, dummy_node).expect_err("reconstruct_script must fail closed");
        assert!(reconstruct_err.contains("pantograph"));

        let trace = InteractiveSessionTrace { request: sample_request(), steps: vec![] };
        let replay_err = gw.replay_session(&trace).expect_err("replay_session must fail closed");
        assert!(replay_err.contains("pantograph"));
    }

    /// `NotInstalled` branch, isolated: an empty synthetic PATH and a
    /// project directory with no lake-manifest.json at all.
    #[test]
    fn detect_pantograph_status_impl_not_installed_branch() {
        let tmp = tempfile::tempdir().unwrap();
        let status = detect_pantograph_status_impl(tmp.path(), Some(""));
        assert!(matches!(status, PantographStatus::NotInstalled { .. }));
    }

    /// `BinaryFoundNoIpc` branch, isolated: a synthetic PATH pointing at a
    /// tempdir containing a fake `pantograph` file, no lake dependency.
    #[test]
    fn detect_pantograph_status_impl_binary_found_no_ipc_branch() {
        let bin_dir = tempfile::tempdir().unwrap();
        let bin_name = if cfg!(windows) { "pantograph.exe" } else { "pantograph" };
        std::fs::write(bin_dir.path().join(bin_name), b"not a real binary").unwrap();

        let project = tempfile::tempdir().unwrap();

        let status = detect_pantograph_status_impl(project.path(), Some(bin_dir.path().to_str().unwrap()));
        match &status {
            PantographStatus::BinaryFoundNoIpc { binary_path } => {
                assert_eq!(binary_path, &bin_dir.path().join(bin_name));
            }
            other => panic!("expected BinaryFoundNoIpc, got {:?}", other),
        }
        assert!(!status.is_available());
    }

    /// `ReferencedButNotFetched` branch, isolated: lake-manifest.json
    /// declares a `pantograph` package, but no `.lake/packages/pantograph`
    /// checkout exists on disk.
    #[test]
    fn detect_pantograph_status_impl_referenced_but_not_fetched_branch() {
        let project = tempfile::tempdir().unwrap();
        // detect_environment (reused for the project's own toolchain read)
        // also requires a resolvable mathlib manifest entry, not just any
        // lake-manifest.json — include one alongside pantograph's so this
        // test reaches ReferencedButNotFetched rather than short-circuiting
        // into ProjectToolchainUndetected (that branch has its own test).
        std::fs::write(
            project.path().join("lake-manifest.json"),
            r#"{"packages":[{"name":"mathlib","rev":"abc123"},{"name":"pantograph","rev":"deadbeef"}]}"#,
        ).unwrap();
        std::fs::write(project.path().join("lean-toolchain"), "leanprover/lean4:v4.32.0-rc1\n").unwrap();

        let status = detect_pantograph_status_impl(project.path(), Some(""));
        match status {
            PantographStatus::ReferencedButNotFetched { manifest_rev } => {
                assert_eq!(manifest_rev.as_deref(), Some("deadbeef"));
            }
            other => panic!("expected ReferencedButNotFetched, got {:?}", other),
        }
    }

    /// `ProjectToolchainUndetected` branch, isolated: a `pantograph` lake
    /// dependency is declared, but this project itself has no
    /// `lean-toolchain` file (mirroring `detect_environment`'s own
    /// `lean_available == false` condition).
    #[test]
    fn detect_pantograph_status_impl_project_toolchain_undetected_branch() {
        let project = tempfile::tempdir().unwrap();
        std::fs::write(
            project.path().join("lake-manifest.json"),
            r#"{"packages":[{"name":"pantograph","rev":"deadbeef"}]}"#,
        ).unwrap();
        // No lean-toolchain file written for this project.

        let status = detect_pantograph_status_impl(project.path(), Some(""));
        assert_eq!(status, PantographStatus::ProjectToolchainUndetected);
    }

    /// `IncompatibleToolchain` branch, isolated: a fetched Pantograph
    /// checkout's `lean-toolchain` differs from this project's own.
    #[test]
    fn detect_pantograph_status_impl_incompatible_toolchain_branch() {
        let project = tempfile::tempdir().unwrap();
        std::fs::write(project.path().join("lean-toolchain"), "leanprover/lean4:v4.32.0-rc1\n").unwrap();
        std::fs::write(
            project.path().join("lake-manifest.json"),
            r#"{"packages":[{"name":"mathlib","rev":"abc123"},{"name":"pantograph","rev":"deadbeef"}]}"#,
        ).unwrap();
        let checkout_dir = project.path().join(".lake/packages/pantograph");
        std::fs::create_dir_all(&checkout_dir).unwrap();
        std::fs::write(checkout_dir.join("lean-toolchain"), "leanprover/lean4:v4.10.0\n").unwrap();

        let status = detect_pantograph_status_impl(project.path(), Some(""));
        match &status {
            PantographStatus::IncompatibleToolchain { pantograph_toolchain, project_toolchain } => {
                assert_eq!(pantograph_toolchain, "leanprover/lean4:v4.10.0");
                assert_eq!(project_toolchain, "leanprover/lean4:v4.32.0-rc1");
            }
            other => panic!("expected IncompatibleToolchain, got {:?}", other),
        }
        assert!(!status.is_available());
    }

    /// `CompatibleButNoIpcImplemented` branch, isolated: a fetched
    /// Pantograph checkout's `lean-toolchain` matches this project's own
    /// exactly — the most favorable outcome this adapter can compute — and
    /// it STILL must not report itself available, and a gateway built from
    /// this exact project must still fail closed on every operation.
    #[test]
    fn detect_pantograph_status_impl_compatible_but_no_ipc_branch_still_fails_closed() {
        let project = tempfile::tempdir().unwrap();
        let toolchain = "leanprover/lean4:v4.32.0-rc1\n";
        std::fs::write(project.path().join("lean-toolchain"), toolchain).unwrap();
        std::fs::write(
            project.path().join("lake-manifest.json"),
            r#"{"packages":[{"name":"mathlib","rev":"abc123"},{"name":"pantograph","rev":"deadbeef"}]}"#,
        ).unwrap();
        let checkout_dir = project.path().join(".lake/packages/pantograph");
        std::fs::create_dir_all(&checkout_dir).unwrap();
        std::fs::write(checkout_dir.join("lean-toolchain"), toolchain).unwrap();

        let status = detect_pantograph_status_impl(project.path(), Some(""));
        match &status {
            PantographStatus::CompatibleButNoIpcImplemented { toolchain: t } => {
                assert_eq!(t, "leanprover/lean4:v4.32.0-rc1");
            }
            other => panic!("expected CompatibleButNoIpcImplemented, got {:?}", other),
        }
        // Even the most favorable static status still reports unavailable...
        assert!(!status.is_available());

        // ...and a gateway built with this status still fails closed on
        // every single trait method — no path to a live session exists in
        // this prototype regardless of what static detection concludes.
        let gw = PantographInteractiveGateway { status };
        let dummy_session = InteractiveSessionHandle(Uuid::new_v4());
        assert!(gw.start_session(&sample_request()).is_err());
        assert!(gw.observe_state(dummy_session).is_err());
    }
}
