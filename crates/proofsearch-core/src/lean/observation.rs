//! Canonical proof-state observation model — issue #162, part of the
//! Pantograph-style interaction epic (#158).
//!
//! ## What this is
//! Issue #159 (`crate::lean::interactive`) defined the LIVE session trait —
//! `start_session` / `observe_state` / `apply_tactic` / ... — and its
//! in-session types (`ProofStateSnapshot`, `InteractiveGoal`,
//! `TacticApplicationResult`, ...). Those types are shaped for talking to a
//! backend right now: they hold whatever a backend happened to report, with
//! no notion of "this hash is stable," "this field is missing because the
//! backend didn't say," or "this is what goes in the database."
//!
//! This module is the next layer up: the CANONICAL, hashed, `serde`/
//! `schemars`-compatible shape those live results get formalized into before
//! they're persisted, exported, or handed back over MCP as the response of a
//! (future, not-implemented-here) `proof_session_observe` /
//! `proof_session_tactic_step` tool. It does not start sessions, apply
//! tactics, or talk to any backend — it only defines the model and the
//! canonical hashing rules, plus lossless conversions from #159's live types
//! and from `LeanDiagnostic`.
//!
//! `LeanDiagnostic` already carries `goal` / `local_context` /
//! `unsolved_goals` / `used_dependencies` / `canonical_goal_hash` fields, but
//! every whole-theorem-verification call site fills them `None` / empty
//! today (see the module doc and grep hits in `lean::mod` — every
//! `canonical_goal_hash: None` is a real, current gap, not a hypothetical
//! one). Interactive proof search needs those fields to become first-class,
//! stably-hashed, structured observations — that is the whole scope of
//! #162: no new proving capability, only a canonical shape for evidence that
//! already exists in less structured form.
//!
//! ## Trust boundary — same rule as #159
//! Everything in this module is SEARCH EVIDENCE, never proof authority. A
//! `ProofStateObservation` reporting `is_solved: true`, or a
//! `ProofStateHash` matching a previous run, proves nothing about the
//! original theorem by itself — only `crate::lean::LeanGateway::verify_exact`
//! / `verify_module` (a real Lean kernel check) can do that. See
//! `crate::lean::interactive`'s module doc for the full statement of this
//! rule; it applies here unchanged.
//!
//! ## Canonical hashing — the rule, once, here
//! Every hash in this module is produced by [`crate::hashing::canonical_hash`],
//! the SAME function `lean::module`, `lean::mod::detect_environment`, and
//! `orchestrator::{trajectories,step,lifecycle}` already use for
//! `environment_hash` / root-statement hashes / kernel-result hashes: the
//! input is serialized via JSON Canoniconicalization Scheme (RFC 8785 — via
//! `serde_jcs`: sorted object keys, canonical number formatting, no
//! insignificant whitespace) and then SHA-256'd, hex-encoded. #162 reuses
//! this rather than inventing a second hashing scheme; see the per-function
//! docs below for exactly what each hash's input tuple contains and why.
//!
//! A structural rule that applies to every hash function here: we hash
//! backend-independent, canonically-RENDERED content, never a backend-native
//! opaque id. A future backend's internal node/goal id is not guaranteed
//! stable across a fresh replay (a different process run, a different
//! elaboration order) the way a hash of the actual rendered text is, so no
//! hash function in this module takes one as input. This directly matches
//! the issue's instruction: "prefer canonical normalized renderings where
//! possible."
//!
//! `selected_goal` (which goal a client/UI currently has focused) is
//! deliberately EXCLUDED from every hash below: it is a view-side concern,
//! not proof-state content — two observations of the same underlying goals
//! with a different focused index are the same proof state.

use chrono::{DateTime, Utc};
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use super::interactive::{InteractiveSessionHandle, ProofStateNodeId, ProofStateSnapshot};
use crate::models::LeanDiagnostic;

/// One hypothesis in a goal's local context.
///
/// `raw_rendering` is the one piece of information every backend that
/// reports a local context at all can supply (a pre-rendered text line, e.g.
/// Lean's `name : type` pretty-printer output, or `name : type := value` for
/// a let-bound hypothesis) and is always present. `name` / `type_rendering`
/// are populated ONLY when the observation's source supplies them already
/// split apart (e.g. a future structured-backend response) — this type never
/// heuristically parses `raw_rendering` on `:` to fabricate them, because
/// that split is not reliable across every real Lean hypothesis shape
/// (anonymous instances like `inst✝`, multi-name binders `a b : Nat`,
/// let-bound hypotheses, hypotheses whose *type* itself contains a `:`).
/// `None` means "not supplied structured," not "anonymous."
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct LocalHypothesis {
    pub raw_rendering: String,
    pub name: Option<String>,
    pub type_rendering: Option<String>,
}

/// The proposition a goal is trying to prove, in one or two renderings.
///
/// `raw_rendering` is required — a goal with no target text at all isn't
/// representable by this type. `pretty_rendering` is a backend-specific
/// "nicer" rendering distinct from `raw_rendering` (e.g. a display form with
/// implicit-argument elision or unicode notation); `None` means the backend
/// only supplied one rendering, not that pretty-printing failed.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ProofTarget {
    pub raw_rendering: String,
    pub pretty_rendering: Option<String>,
}

/// One open goal within a [`ProofStateObservation`].
///
/// `local_context: None` means "this observation's source did not report a
/// local context for this goal" — distinct from `Some(vec![])`, which means
/// the source explicitly reported zero hypotheses in scope. Every #159
/// backend today (`MockInteractiveGateway`, `FallbackInteractiveGateway`,
/// and the whole-theorem `RealLeanGateway`/`MockGateway` diagnostic paths)
/// leaves this unpopulated regardless of how many real hypotheses would be
/// in scope at that point, so the conversions in this module
/// (`ProofGoal::from_interactive_goal`) always produce `None` for today's
/// backends rather than guessing "so it must be zero."
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ProofGoal {
    /// Position of this goal within its observation's `goals` list at
    /// observation time. Structural bookkeeping only — excluded from
    /// `hash_goal` (see that function's doc).
    pub goal_index: usize,
    pub target: ProofTarget,
    pub local_context: Option<Vec<LocalHypothesis>>,
}

impl ProofGoal {
    /// Lossless-as-possible conversion from #159's [`super::interactive::InteractiveGoal`].
    /// `InteractiveGoal.local_context: Vec<String>` has no way to distinguish
    /// "zero hypotheses" from "not reported," so this conversion treats an
    /// empty vector as "not reported" (`None`) — the honest reading given
    /// every current backend leaves it empty unconditionally rather than
    /// having ever actually inspected hypothesis scope. A non-empty
    /// `local_context` converts to one [`LocalHypothesis`] per line, with
    /// `name` / `type_rendering` left `None` per this module's no-heuristic-
    /// parsing rule.
    pub fn from_interactive_goal(goal_index: usize, goal: &super::interactive::InteractiveGoal) -> Self {
        let local_context = if goal.local_context.is_empty() {
            None
        } else {
            Some(
                goal.local_context
                    .iter()
                    .map(|line| LocalHypothesis { raw_rendering: line.clone(), name: None, type_rendering: None })
                    .collect(),
            )
        };
        ProofGoal {
            goal_index,
            target: ProofTarget { raw_rendering: goal.goal.clone(), pretty_rendering: None },
            local_context,
        }
    }
}

/// Stable hashes over one [`ProofStateObservation`]'s content — the
/// "canonical hashing" half of issue #162's acceptance criteria. See the
/// module doc for the shared hashing convention (`canonical_hash` / JCS /
/// SHA-256) and the `selected_goal`-exclusion rule.
///
/// Every field here is independently documented with exactly what goes into
/// it; see the free functions below (`hash_goal`, `hash_local_context`, ...)
/// for the precise input tuples, which are the load-bearing part of "hashing
/// rules are documented" — this struct just carries their outputs.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ProofStateHash {
    /// Hash of the full proof state at this node: the ordered list of
    /// `goal_hashes` plus `tactic_text_hash`. Order of `goal_hashes` is
    /// significant — see `compute_proof_state_hash`'s doc for why goal order
    /// is treated as real content, not incidental. Always computable (a node
    /// with zero goals still hashes deterministically), so this is a plain
    /// `String`, never `None`.
    pub full_state_hash: String,
    /// One hash per goal in `ProofStateObservation.goals`, same order,
    /// same length. See `hash_goal`.
    pub goal_hashes: Vec<String>,
    /// One entry per goal, same order/length as `goal_hashes`. `None` at
    /// index `i` means goal `i`'s `local_context` was itself `None`
    /// ("not reported" — see [`ProofGoal`]'s doc); `Some(hash)` means a
    /// local context (possibly empty) was reported and hashed. This is
    /// deliberately `Vec<Option<String>>`, not `Vec<String>` with a
    /// placeholder, so "backend didn't report this" round-trips through the
    /// hash summary explicitly rather than becoming indistinguishable from
    /// an empty-but-known context.
    pub local_context_hashes: Vec<Option<String>>,
    /// Hash of the tactic text that produced this node from its parent.
    /// `None` iff there is no such tactic — i.e. this is a session's root
    /// node (`ProofStateSnapshot.tactic_applied == None`), not "the backend
    /// didn't report the tactic text" (a node reached BY a tactic always has
    /// that tactic's text available, since the caller supplied it to
    /// `apply_tactic`).
    pub tactic_text_hash: Option<String>,
}

/// Hashes one hypothesis's full content (`raw_rendering`, `name`,
/// `type_rendering` — all three; `name`/`type_rendering` being `None` is
/// itself part of the hashed content, since "not reported structured" is
/// observably different from a future observation that DOES report them).
pub fn hash_local_hypothesis(hypothesis: &LocalHypothesis) -> Result<String, String> {
    crate::hashing::canonical_hash(hypothesis)
}

/// Hashes an ordered list of hypotheses. Order is significant: local-context
/// order reflects real hypothesis-introduction order in the Lean proof
/// state (shadowing and dependent hypotheses are order-sensitive), so two
/// goals with the same hypotheses in a different order are NOT treated as
/// equivalent here.
pub fn hash_local_context(context: &[LocalHypothesis]) -> Result<String, String> {
    crate::hashing::canonical_hash(&context.to_vec())
}

/// Hashes one goal from `(target, local_context_hash)` — the goal's own
/// target rendering plus its ALREADY-COMPUTED local-context hash (not the
/// raw hypothesis list again), so a goal's hash composes cleanly on top of
/// `hash_local_context` rather than duplicating that serialization.
/// `local_context_hash: None` (goal's local context was itself unreported)
/// is part of the hashed tuple, not skipped — a goal whose context is
/// unreported must hash differently from one whose context is known-empty.
/// `goal_index` is NOT part of this hash (see [`ProofGoal`]'s doc): it is
/// positional bookkeeping already captured by the goal's position in
/// `ProofStateHash.goal_hashes`.
pub fn hash_goal(target: &ProofTarget, local_context_hash: Option<&str>) -> Result<String, String> {
    crate::hashing::canonical_hash(&(target.clone(), local_context_hash.map(|s| s.to_string())))
}

/// Hashes tactic text after trimming leading/trailing whitespace only
/// (matching `MockInteractiveGateway::apply_tactic`'s own "must not be empty
/// after trim" rule). Internal whitespace/comments are NOT further
/// normalized: two tactic strings differing only in internal formatting can
/// be different Lean syntax (e.g. inside a string literal token), and this
/// hash exists to answer "was literally this tactic text replayed," not "was
/// a semantically equivalent tactic replayed."
pub fn hash_tactic_text(tactic: &str) -> Result<String, String> {
    crate::hashing::canonical_hash(&tactic.trim().to_string())
}

/// Hashes a full `LeanDiagnostic` (every field — `category`,
/// `primary_message`, `source_span`, `goal`, `local_context`,
/// `unsolved_goals`, `used_dependencies`, `error_code`,
/// `canonical_goal_hash`). Two diagnostics are considered the same
/// "resulting diagnostic" here only if every one of those fields matches
/// exactly; this module does not attempt to normalize away incidental
/// pretty-printer differences (e.g. a Lean/Mathlib version bump changing
/// whitespace in `primary_message`) — that is a future enrichment, not part
/// of #162's scope, and treating two textually different messages as "the
/// same diagnostic" without that normalization actually existing would be
/// guessing, which issue #162 explicitly asks this module not to do.
pub fn hash_diagnostic(diagnostic: &LeanDiagnostic) -> Result<String, String> {
    crate::hashing::canonical_hash(diagnostic)
}

/// Computes the full [`ProofStateHash`] for a node from its `goals` (in
/// order) and the tactic that produced it (`None` at a session root). This
/// is the composition point: it calls `hash_local_context` and `hash_goal`
/// per goal, then folds the resulting `goal_hashes` together with
/// `tactic_text_hash` into `full_state_hash`. `selected_goal` is
/// intentionally not a parameter — see the module doc.
pub fn compute_proof_state_hash(goals: &[ProofGoal], tactic_applied: Option<&str>) -> Result<ProofStateHash, String> {
    let mut goal_hashes = Vec::with_capacity(goals.len());
    let mut local_context_hashes: Vec<Option<String>> = Vec::with_capacity(goals.len());
    for goal in goals {
        let local_context_hash = match &goal.local_context {
            Some(ctx) => Some(hash_local_context(ctx)?),
            None => None,
        };
        goal_hashes.push(hash_goal(&goal.target, local_context_hash.as_deref())?);
        local_context_hashes.push(local_context_hash);
    }
    let tactic_text_hash = match tactic_applied {
        Some(t) => Some(hash_tactic_text(t)?),
        None => None,
    };
    let full_state_hash = crate::hashing::canonical_hash(&(goal_hashes.clone(), tactic_text_hash.clone()))?;
    Ok(ProofStateHash { full_state_hash, goal_hashes, local_context_hashes, tactic_text_hash })
}

/// Caller-supplied context a [`ProofStateObservation`] needs but cannot
/// derive from a live [`ProofStateSnapshot`] alone: which episode/obligation/
/// problem-version this session's evidence is for, and which backend/
/// environment produced it. Bundled into one struct so
/// `ProofStateObservation::from_snapshot` doesn't grow an unreadable
/// positional-argument list.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ObservationContext {
    pub episode_id: Uuid,
    pub obligation_id: Uuid,
    pub problem_version_id: Uuid,
    /// Free-text identifier of the backend that produced this observation
    /// (e.g. `"mock"`, `"fallback"`, a future `"pantograph"`). Required: an
    /// observation with no known origin is not useful evidence.
    pub backend_kind: String,
    /// Backend version string, if the backend reports one. `None` means the
    /// backend didn't report a version — not "unversioned."
    pub backend_version: Option<String>,
    /// Already-computed import-manifest hash (same convention as
    /// `problem_versions.import_manifest_hash` / `orchestrator::context`),
    /// carried through rather than recomputed here. `None` means this
    /// session's caller did not supply one (e.g. no problem-version context
    /// available for this session yet).
    pub import_manifest_hash: Option<String>,
    /// Already-computed environment hash (same convention as
    /// `lean::detect_environment`'s `LeanEnvironmentInfo.hash`), carried
    /// through rather than recomputed here. `None` means unavailable — e.g.
    /// `MockInteractiveGateway` has no real Lean environment to hash.
    pub environment_hash: Option<String>,
}

/// The canonical, hashed, `serde`/`schemars`-compatible observation of one
/// LIVE (non-failed) proof-state node — issue #162's primary deliverable.
/// This is what a (future) `proof_session_observe` / successful
/// `proof_session_tactic_step` MCP response is built from. See the module
/// doc for the trust-boundary rule: this is search evidence, never proof
/// authority, regardless of `is_solved`.
///
/// A FAILED `apply_tactic` call does not produce one of these — see
/// [`ProofStateDiagnostic`], which stands alone the same way
/// `TacticApplicationResult::diagnostic` stands in place of (not nested
/// inside) `TacticApplicationResult::state` in #159.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ProofStateObservation {
    pub session_id: InteractiveSessionHandle,
    pub node_id: ProofStateNodeId,
    /// `None` iff `node_id` is the session's root node.
    pub parent_node_id: Option<ProofStateNodeId>,
    pub episode_id: Uuid,
    pub obligation_id: Uuid,
    pub problem_version_id: Uuid,
    pub backend_kind: String,
    pub backend_version: Option<String>,
    pub import_manifest_hash: Option<String>,
    pub environment_hash: Option<String>,
    /// Canonical hashes of this node's content — see [`ProofStateHash`] and
    /// `compute_proof_state_hash`.
    pub proof_state_hash: ProofStateHash,
    /// Typed, structured goals (not a parallel `goals_json` string): this
    /// type already derives `Serialize`/`JsonSchema`, so a raw-JSON view is
    /// always exactly `serde_json::to_value(&observation.goals)` away
    /// without maintaining a second representation that could drift out of
    /// sync with this one.
    pub goals: Vec<ProofGoal>,
    /// Index into `goals` of the goal a client/UI currently has focused.
    /// `None` iff `goals` is empty (nothing to select). View-side state —
    /// deliberately excluded from `proof_state_hash` (see the module doc).
    pub selected_goal: Option<usize>,
    /// The tactic text that produced this node from its parent. `None` for
    /// a session's root node.
    pub tactic_applied: Option<String>,
    /// `true` iff `goals` is empty at this node. A claim about this
    /// session's internal state only — see the trust-boundary note.
    pub is_solved: bool,
    /// A backend-supplied whole-node pretty rendering (e.g. what a
    /// Pantograph-style widget would show for the ENTIRE node, all goals
    /// combined), distinct from each goal's own `ProofTarget.pretty_rendering`.
    /// `None` means the backend didn't supply one — no #159 backend does
    /// today.
    pub pretty_rendering: Option<String>,
    /// Hash of the backend's raw wire payload for this node, if the backend
    /// exposes one and it was captured. `None` means either not applicable
    /// (an in-memory backend like `MockInteractiveGateway` has no wire
    /// payload) or not captured — this module does not distinguish those two
    /// `None` reasons because neither is knowable from the observation alone.
    pub raw_backend_payload_hash: Option<String>,
    /// Mirrors the machine-checkable `proof_body_redacted` marker issue #70
    /// established for `proof_export` / `trajectory_export` in
    /// `proofsearch-mcp`: `false` means `goals` / `tactic_applied` on this
    /// observation carry real proof-body content (goal text, tactic text)
    /// verbatim; `true` means that content has been scrubbed before this
    /// observation was serialized (e.g. a future benchmark-linked public
    /// export path) and must not be treated as proof-body-bearing evidence.
    /// The constructors in this module always produce `false` — they never
    /// redact; a future export wrapper sets this when it does.
    pub proof_body_redacted: bool,
    pub observed_at: DateTime<Utc>,
}

impl ProofStateObservation {
    /// Builds a canonical observation from a live [`ProofStateSnapshot`]
    /// (#159) plus the context #159's trait doesn't carry (episode/
    /// obligation/problem-version/backend identity). Computes
    /// `proof_state_hash` from the converted `goals` and `tactic_applied`.
    /// Defaults `selected_goal` to the first open goal (index `0`) when
    /// `goals` is non-empty, matching `observe_state`'s existing convention
    /// of exposing "the" current node without a separate live selection
    /// concept in #159.
    pub fn from_snapshot(
        session_id: InteractiveSessionHandle,
        snapshot: &ProofStateSnapshot,
        context: ObservationContext,
        observed_at: DateTime<Utc>,
    ) -> Result<Self, String> {
        let goals: Vec<ProofGoal> = snapshot
            .goals
            .iter()
            .enumerate()
            .map(|(i, g)| ProofGoal::from_interactive_goal(i, g))
            .collect();
        let proof_state_hash = compute_proof_state_hash(&goals, snapshot.tactic_applied.as_deref())?;
        let selected_goal = if goals.is_empty() { None } else { Some(0) };
        Ok(ProofStateObservation {
            session_id,
            node_id: snapshot.node,
            parent_node_id: snapshot.parent,
            episode_id: context.episode_id,
            obligation_id: context.obligation_id,
            problem_version_id: context.problem_version_id,
            backend_kind: context.backend_kind,
            backend_version: context.backend_version,
            import_manifest_hash: context.import_manifest_hash,
            environment_hash: context.environment_hash,
            proof_state_hash,
            goals,
            selected_goal,
            tactic_applied: snapshot.tactic_applied.clone(),
            is_solved: snapshot.is_solved,
            pretty_rendering: None,
            raw_backend_payload_hash: None,
            proof_body_redacted: false,
            observed_at,
        })
    }
}

/// Canonical record of one FAILED `apply_tactic` call. Stands alone — it is
/// not nested inside a [`ProofStateObservation`] — the same way
/// `TacticApplicationResult::diagnostic` in #159 stands in place of, not
/// inside, `TacticApplicationResult::state`: a failed tactic application
/// produces no new node to observe.
///
/// Wraps [`LeanDiagnostic`] WHOLESALE (`diagnostic` field) rather than
/// re-declaring its fields, so nothing #159/#162's `TacticApplicationResult`
/// already puts in a `LeanDiagnostic` (`category`, `primary_message`,
/// `source_span`, `goal`, `local_context`, `unsolved_goals`,
/// `used_dependencies`, `error_code`, `canonical_goal_hash`) is lost or
/// duplicated by this type — this satisfies the acceptance criterion that
/// `LeanDiagnostic`'s existing fields are "reused or mapped without losing
/// information" by construction (reuse), not by a lossy field-by-field copy.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ProofStateDiagnostic {
    pub session_id: InteractiveSessionHandle,
    /// The node the failing tactic was applied to. `None` only if the
    /// failure occurred before any node context was available (not possible
    /// via `InteractiveProofGateway::apply_tactic`, which always requires a
    /// `parent_node`; reserved for a future diagnostic source that doesn't).
    pub parent_node_id: Option<ProofStateNodeId>,
    /// `full_state_hash` of `parent_node_id`'s [`ProofStateHash`], if the
    /// caller had already computed one for that node. `None` means the
    /// caller did not supply it, not that the parent state is unhashable.
    pub parent_proof_state_hash: Option<String>,
    /// `Some(id)` iff a child node marked failed was created for replay
    /// purposes (see the issue's "no child node (or a child node marked
    /// failed if that's easier for replay)" allowance); `None` means no
    /// child node was created. `MockInteractiveGateway` today creates none —
    /// a failed `apply_tactic` call there leaves `s.current` unchanged and
    /// returns no new node — so conversions from it always produce `None`.
    pub child_node_id: Option<ProofStateNodeId>,
    /// The raw tactic text that failed, if available. `None` only if the
    /// diagnostic genuinely has no associated tactic text (e.g. a future
    /// session-start-time diagnostic, not possible via `apply_tactic`
    /// today).
    pub tactic_text: Option<String>,
    /// `hash_tactic_text(tactic_text)`, or `None` iff `tactic_text` is
    /// `None`.
    pub tactic_text_hash: Option<String>,
    /// The full diagnostic, reused wholesale — see the struct doc.
    pub diagnostic: LeanDiagnostic,
    /// `hash_diagnostic(&diagnostic)` — always computable.
    pub diagnostic_hash: String,
    pub observed_at: DateTime<Utc>,
}

impl ProofStateDiagnostic {
    /// Builds a canonical diagnostic record from a failed `apply_tactic`
    /// call's `LeanDiagnostic` plus the parent/child node context #159's
    /// `TacticApplicationResult` doesn't itself carry (it only carries the
    /// bare `LeanDiagnostic`). Computes `diagnostic_hash` always, and
    /// `tactic_text_hash` iff `tactic_text` is `Some`.
    pub fn from_tactic_failure(
        session_id: InteractiveSessionHandle,
        parent_node_id: Option<ProofStateNodeId>,
        parent_proof_state_hash: Option<String>,
        tactic_text: Option<String>,
        child_node_id: Option<ProofStateNodeId>,
        diagnostic: LeanDiagnostic,
        observed_at: DateTime<Utc>,
    ) -> Result<Self, String> {
        let tactic_text_hash = match &tactic_text {
            Some(t) => Some(hash_tactic_text(t)?),
            None => None,
        };
        let diagnostic_hash = hash_diagnostic(&diagnostic)?;
        Ok(ProofStateDiagnostic {
            session_id,
            parent_node_id,
            parent_proof_state_hash,
            child_node_id,
            tactic_text,
            tactic_text_hash,
            diagnostic,
            diagnostic_hash,
            observed_at,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean::interactive::InteractiveGoal;
    use crate::models::LeanDiagnosticCategory;

    fn hyp(raw: &str) -> LocalHypothesis {
        LocalHypothesis { raw_rendering: raw.to_string(), name: None, type_rendering: None }
    }

    fn goal(raw_target: &str, ctx: Option<Vec<LocalHypothesis>>) -> ProofGoal {
        ProofGoal { goal_index: 0, target: ProofTarget { raw_rendering: raw_target.to_string(), pretty_rendering: None }, local_context: ctx }
    }

    // --- (a) stable-hash tests -------------------------------------------

    #[test]
    fn compute_proof_state_hash_is_stable_for_structurally_equivalent_goals() {
        let goals_a = vec![goal("1 + 1 = 2", Some(vec![hyp("n : Nat")]))];
        let goals_b = vec![goal("1 + 1 = 2", Some(vec![hyp("n : Nat")]))];

        let hash_a = compute_proof_state_hash(&goals_a, Some("norm_num")).unwrap();
        let hash_b = compute_proof_state_hash(&goals_b, Some("norm_num")).unwrap();

        assert_eq!(hash_a.full_state_hash, hash_b.full_state_hash);
        assert_eq!(hash_a.goal_hashes, hash_b.goal_hashes);
        assert_eq!(hash_a.local_context_hashes, hash_b.local_context_hashes);
        assert_eq!(hash_a.tactic_text_hash, hash_b.tactic_text_hash);
    }

    #[test]
    fn compute_proof_state_hash_changes_when_goal_target_changes() {
        let goals_a = vec![goal("1 + 1 = 2", None)];
        let goals_b = vec![goal("1 + 1 = 3", None)];

        let hash_a = compute_proof_state_hash(&goals_a, None).unwrap();
        let hash_b = compute_proof_state_hash(&goals_b, None).unwrap();

        assert_ne!(hash_a.full_state_hash, hash_b.full_state_hash);
        assert_ne!(hash_a.goal_hashes[0], hash_b.goal_hashes[0]);
    }

    #[test]
    fn compute_proof_state_hash_changes_when_tactic_text_changes() {
        let goals = vec![goal("1 + 1 = 2", None)];

        let hash_a = compute_proof_state_hash(&goals, Some("norm_num")).unwrap();
        let hash_b = compute_proof_state_hash(&goals, Some("rfl")).unwrap();
        let hash_root = compute_proof_state_hash(&goals, None).unwrap();

        assert_ne!(hash_a.full_state_hash, hash_b.full_state_hash);
        assert_ne!(hash_a.tactic_text_hash, hash_b.tactic_text_hash);
        assert_ne!(hash_a.full_state_hash, hash_root.full_state_hash);
        assert!(hash_root.tactic_text_hash.is_none());
    }

    #[test]
    fn compute_proof_state_hash_distinguishes_unreported_from_empty_local_context() {
        // Same goal target, but one reports "no context supplied" (None) and
        // the other reports "supplied, zero hypotheses" (Some(vec![])).
        // These must hash differently — collapsing them would silently
        // discard exactly the "unavailable vs known" distinction #162 asks
        // this module to preserve.
        let goals_unreported = vec![goal("1 + 1 = 2", None)];
        let goals_known_empty = vec![goal("1 + 1 = 2", Some(vec![]))];

        let hash_unreported = compute_proof_state_hash(&goals_unreported, None).unwrap();
        let hash_known_empty = compute_proof_state_hash(&goals_known_empty, None).unwrap();

        assert_ne!(hash_unreported.goal_hashes[0], hash_known_empty.goal_hashes[0]);
        assert!(hash_unreported.local_context_hashes[0].is_none());
        assert!(hash_known_empty.local_context_hashes[0].is_some());
    }

    #[test]
    fn compute_proof_state_hash_is_sensitive_to_local_context_order() {
        let goals_ab = vec![goal("P", Some(vec![hyp("a : Nat"), hyp("b : Nat")]))];
        let goals_ba = vec![goal("P", Some(vec![hyp("b : Nat"), hyp("a : Nat")]))];

        let hash_ab = compute_proof_state_hash(&goals_ab, None).unwrap();
        let hash_ba = compute_proof_state_hash(&goals_ba, None).unwrap();

        assert_ne!(hash_ab.goal_hashes[0], hash_ba.goal_hashes[0]);
    }

    #[test]
    fn hash_tactic_text_trims_whitespace_but_not_internal_content() {
        let a = hash_tactic_text("  norm_num  ").unwrap();
        let b = hash_tactic_text("norm_num").unwrap();
        let c = hash_tactic_text("norm_num  ;  rfl").unwrap();
        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn hash_diagnostic_is_stable_and_field_sensitive() {
        let base = LeanDiagnostic {
            category: LeanDiagnosticCategory::TacticFailure,
            primary_message: "tactic failed".to_string(),
            source_span: Some("1:2".to_string()),
            goal: Some("1 + 1 = 2".to_string()),
            local_context: vec!["n : Nat".to_string()],
            unsolved_goals: vec!["1 + 1 = 2".to_string()],
            used_dependencies: vec!["Nat.add".to_string()],
            error_code: Some("E001".to_string()),
            canonical_goal_hash: Some("deadbeef".to_string()),
        };
        let same = base.clone();
        let mut changed = base.clone();
        changed.primary_message = "a different failure".to_string();

        assert_eq!(hash_diagnostic(&base).unwrap(), hash_diagnostic(&same).unwrap());
        assert_ne!(hash_diagnostic(&base).unwrap(), hash_diagnostic(&changed).unwrap());
    }

    // --- (b) LeanDiagnostic -> ProofStateDiagnostic mapping is lossless --

    #[test]
    fn from_tactic_failure_preserves_every_populated_lean_diagnostic_field() {
        let diagnostic = LeanDiagnostic {
            category: LeanDiagnosticCategory::UnsolvedGoals,
            primary_message: "unsolved goals".to_string(),
            source_span: Some("3:7".to_string()),
            goal: Some("P n".to_string()),
            local_context: vec!["n : Nat".to_string(), "h : P 0".to_string()],
            unsolved_goals: vec!["P n".to_string()],
            used_dependencies: vec!["Nat.rec".to_string(), "P.intro".to_string()],
            error_code: Some("E042".to_string()),
            canonical_goal_hash: Some("abc123".to_string()),
        };
        let session = InteractiveSessionHandle(Uuid::new_v4());
        let parent = ProofStateNodeId(Uuid::new_v4());

        let record = ProofStateDiagnostic::from_tactic_failure(
            session,
            Some(parent),
            Some("parent-hash-xyz".to_string()),
            Some("induction n".to_string()),
            None,
            diagnostic.clone(),
            Utc::now(),
        )
        .expect("from_tactic_failure should succeed");

        // Every LeanDiagnostic field survives unchanged — field-by-field,
        // since LeanDiagnostic does not derive PartialEq.
        assert_eq!(record.diagnostic.category, diagnostic.category);
        assert_eq!(record.diagnostic.primary_message, diagnostic.primary_message);
        assert_eq!(record.diagnostic.source_span, diagnostic.source_span);
        assert_eq!(record.diagnostic.goal, diagnostic.goal);
        assert_eq!(record.diagnostic.local_context, diagnostic.local_context);
        assert_eq!(record.diagnostic.unsolved_goals, diagnostic.unsolved_goals);
        assert_eq!(record.diagnostic.used_dependencies, diagnostic.used_dependencies);
        assert_eq!(record.diagnostic.error_code, diagnostic.error_code);
        assert_eq!(record.diagnostic.canonical_goal_hash, diagnostic.canonical_goal_hash);

        // New #162 fields are populated from the supplied context.
        assert_eq!(record.session_id, session);
        assert_eq!(record.parent_node_id, Some(parent));
        assert_eq!(record.parent_proof_state_hash.as_deref(), Some("parent-hash-xyz"));
        assert_eq!(record.tactic_text.as_deref(), Some("induction n"));
        assert!(record.tactic_text_hash.is_some());
        assert!(record.child_node_id.is_none());
        assert_eq!(record.diagnostic_hash, hash_diagnostic(&diagnostic).unwrap());
    }

    #[test]
    fn from_snapshot_preserves_interactive_goal_content() {
        let session = InteractiveSessionHandle(Uuid::new_v4());
        let node = ProofStateNodeId(Uuid::new_v4());
        let snapshot = ProofStateSnapshot {
            node,
            parent: None,
            tactic_applied: None,
            goals: vec![InteractiveGoal { goal: "1 + 1 = 2".to_string(), local_context: vec![], canonical_goal_hash: None }],
            is_solved: false,
        };
        let context = ObservationContext {
            episode_id: Uuid::new_v4(),
            obligation_id: Uuid::new_v4(),
            problem_version_id: Uuid::new_v4(),
            backend_kind: "mock".to_string(),
            backend_version: None,
            import_manifest_hash: None,
            environment_hash: None,
        };

        let observation = ProofStateObservation::from_snapshot(session, &snapshot, context, Utc::now())
            .expect("from_snapshot should succeed");

        assert_eq!(observation.node_id, node);
        assert!(observation.parent_node_id.is_none());
        assert_eq!(observation.goals.len(), 1);
        assert_eq!(observation.goals[0].target.raw_rendering, "1 + 1 = 2");
        assert_eq!(observation.selected_goal, Some(0));
        assert!(!observation.is_solved);
        assert!(!observation.proof_body_redacted);
    }

    // --- (c) missing/unavailable fields serialize as explicit null -------

    #[test]
    fn unreported_local_context_serializes_as_null_not_empty_array() {
        let g = goal("1 + 1 = 2", None);
        let value = serde_json::to_value(&g).unwrap();
        assert!(value["local_context"].is_null(), "expected null, got {value}");
    }

    #[test]
    fn unreported_hypothesis_name_and_type_serialize_as_null() {
        let h = hyp("n : Nat");
        let value = serde_json::to_value(&h).unwrap();
        assert!(value["name"].is_null(), "expected null, got {value}");
        assert!(value["type_rendering"].is_null(), "expected null, got {value}");
    }

    #[test]
    fn unavailable_environment_and_backend_details_serialize_as_null() {
        let context = ObservationContext {
            episode_id: Uuid::new_v4(),
            obligation_id: Uuid::new_v4(),
            problem_version_id: Uuid::new_v4(),
            backend_kind: "mock".to_string(),
            backend_version: None,
            import_manifest_hash: None,
            environment_hash: None,
        };
        let value = serde_json::to_value(&context).unwrap();
        assert!(value["backend_version"].is_null());
        assert!(value["import_manifest_hash"].is_null());
        assert!(value["environment_hash"].is_null());
        // backend_kind is required, non-optional, and must NOT be null.
        assert_eq!(value["backend_kind"], "mock");
    }
}
