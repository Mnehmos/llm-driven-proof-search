use serde::{Deserialize, Serialize};
use schemars::JsonSchema;
use super::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use super::reward::RewardComponent;

use chrono::{DateTime, Utc};
use uuid::Uuid;

/// Issue #51: how the server should treat leading whitespace in a submitted
/// proof body before splicing it under `... := by`. This is a pure TRANSPORT
/// format — it only affects leading whitespace, never the tactic text, the
/// statement, imports, or the namespace, and it never bypasses verification:
/// the Lean kernel remains the sole authority on KernelPass/KernelFail.
///
/// - `flat_tactic_sequence` (default): the #41 flattener — re-bases uniform
///   indentation and collapses accidental nesting to one level, protecting
///   simple sequential tactic lists from an inadvertent focus-block trap.
/// - `raw_lean_block`: strips only the common left margin and re-bases it,
///   preserving RELATIVE indentation so a proof that intentionally relies on
///   Lean's indentation structure (focus bullets `·`, nested `case`/`by`
///   blocks) keeps its shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema, Default)]
#[serde(rename_all = "snake_case")]
pub enum ProofFormat {
    #[default]
    FlatTacticSequence,
    RawLeanBlock,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum TypedAction {
    Decompose { sub_lemmas: Vec<String> },
    Solve {
        proof_term: String,
        /// Transport format for `proof_term`'s leading whitespace (see
        /// [`ProofFormat`]). Defaults to `flat_tactic_sequence`; set
        /// `raw_lean_block` only when the proof intentionally uses Lean
        /// relative-indentation structure.
        #[serde(default)]
        proof_format: ProofFormat,
    },
    /// Submit a small structured Lean development — helper definitions and
    /// helper theorems plus a root theorem — that the server assembles into one
    /// namespaced module and verifies as a unit. This is NOT a raw-Lean escape
    /// hatch: clients send structured items only (no import / namespace / end /
    /// set_option lines, and no axiom / opaque / unsafe / instance declarations),
    /// the server sanitizes every name and places all declarations under the
    /// generated `ChatDB.P_<problem>` namespace, and the root theorem's statement
    /// must hash-match the problem's registered root formal statement. Either the
    /// whole module passes the kernel and is recorded, or nothing enters the
    /// trusted namespace. See [`LeanModuleItem`], [`ModuleTheorem`], and
    /// `crate::lean::module`.
    SubmitModule {
        module_items: Vec<LeanModuleItem>,
        root_theorem: ModuleTheorem,
    },
    ExternalResponseRejected { reason: String, raw_response: String },
    GiveUp,
}

/// One structured item in a [`TypedAction::SubmitModule`] development. Never a
/// raw Lean source line — the server renders the surrounding `def`/`theorem`
/// keyword, the sanitized name, and the namespace. The client supplies only the
/// mathematical content (type signature / statement / body / proof term).
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "item_kind", rename_all = "snake_case")]
pub enum LeanModuleItem {
    /// A helper definition: `def <name> : <type_signature> := <body>` (or, when
    /// `type_signature` is empty, `def <name> := <body>` — Lean infers the type).
    Def {
        /// A single namespace-local identifier (no dots). Sanitized and placed
        /// under `ChatDB.P_<problem>`.
        name: String,
        /// The type after the colon, e.g. `List ℕ → ℕ`. May be empty to let Lean
        /// infer it. Must not contain top-level Lean commands.
        type_signature: String,
        /// The definition body (what goes after `:=`). Must not contain top-level
        /// Lean commands.
        body: String,
    },
    /// A helper theorem: `theorem <name> : <statement> := by <proof_term>`.
    Theorem {
        /// A single namespace-local identifier (no dots).
        name: String,
        /// The proposition after the colon. Must not contain top-level Lean commands.
        statement: String,
        /// The tactic block proving `statement` (what goes after `:= by`).
        proof_term: String,
    },
    /// Two or more declarations that must forward-reference each other (e.g. a
    /// pair of mutually recursive functions) — rendered together inside one
    /// server-owned `mutual ... end` block, the only way Lean lets a member see
    /// a sibling declared later in the group. The client still never writes
    /// `mutual`/`end` itself (both stay banned anywhere in client content); it
    /// only supplies the same per-member content a bare `Def`/`Theorem` would,
    /// structured so the server knows which declarations belong in one block.
    /// A group of fewer than two members is rejected — that's just a bare
    /// `Def`/`Theorem`, which has no forward-reference problem to begin with.
    MutualGroup {
        members: Vec<MutualMember>,
    },
}

/// One declaration inside a [`LeanModuleItem::MutualGroup`]. Deliberately not
/// `LeanModuleItem` itself: a group cannot legally contain another group, and
/// this shape makes that unrepresentable rather than a runtime check.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[serde(tag = "item_kind", rename_all = "snake_case")]
pub enum MutualMember {
    Def {
        name: String,
        type_signature: String,
        body: String,
    },
    Theorem {
        name: String,
        statement: String,
        proof_term: String,
    },
}

/// The root theorem of a [`TypedAction::SubmitModule`] development — the one
/// whose `statement` must hash-match the problem's registered root formal
/// statement, and whose success proves the root obligation.
#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ModuleTheorem {
    /// A single namespace-local identifier (no dots).
    pub name: String,
    /// The root proposition. Its canonical hash must equal the problem's
    /// `root_statement_hash` — a module cannot silently prove a different goal.
    pub statement: String,
    /// The tactic block proving `statement` (what goes after `:= by`).
    pub proof_term: String,
    /// Transport format for `proof_term`'s leading whitespace (see
    /// [`ProofFormat`]). Defaults to `flat_tactic_sequence`; set
    /// `raw_lean_block` only when the root proof intentionally uses Lean
    /// relative-indentation structure. Helper defs/theorems and mutual members
    /// are always flattened.
    #[serde(default)]
    pub proof_format: ProofFormat,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ActionRequest {
    pub id: Uuid,
    pub episode_id: Uuid,
    pub problem_version_id: Uuid,
    pub episode_revision: i64,
    pub request_sequence_number: i64,
    pub role: ActionRole,
    pub state_hash_before: Option<String>,
    pub status: String,
    pub expiration_at: Option<DateTime<Utc>>,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct ActionAttempt {
    pub id: Uuid,
    pub action_request_id: Uuid,
    pub model_config_hash: Option<String>,
    pub status: AttemptStatus,
    pub action_json: Option<TypedAction>,
    pub created_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum ActionRole {
    Prover,
    Reviewer,
    Human,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum AttemptStatus {
    Claimed,
    PreflightRejected,
    Executing,
    Verified,
    Rejected,
    Committed,
    Abandoned,
    Expired,
    InfrastructureFailed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, JsonSchema)]
#[serde(rename_all = "snake_case")]
pub enum StepDisposition {
    Accepted,
    StaleRevision,
    InvalidResponse,
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
pub struct StepResult {
    pub disposition: StepDisposition,
    pub counts_as_environment_step: bool,
    pub reward: Option<Vec<RewardComponent>>,
    pub outcome: Option<EpisodeOutcome>,
    pub termination_reason: Option<TerminationReason>,
    pub truncation_reason: Option<TruncationReason>,
    pub diagnostics: Option<String>,
}

impl StepResult {
    /// Validates the constraints of the StepResult.
    pub fn validate(&self) -> Result<(), &'static str> {
        match (self.outcome, self.termination_reason, self.truncation_reason) {
            (Some(_), Some(_), Some(_)) => return Err("Cannot have both termination and truncation reasons"),
            (Some(_), None, None) => return Err("Terminal outcome must have a termination or truncation reason"),
            (None, Some(_), _) => return Err("Cannot have termination reason without outcome"),
            (None, _, Some(_)) => return Err("Cannot have truncation reason without outcome"),
            _ => {}
        }
        Ok(())
    }
}
