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
}
