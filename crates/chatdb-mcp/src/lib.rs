use std::path::PathBuf;
use std::sync::Arc;
use tokio::sync::Mutex;
use rusqlite::{Connection, OptionalExtension, Transaction};
use uuid::Uuid;
use chrono::Utc;
use serde::Deserialize;
use schemars::JsonSchema;

use rmcp::ServerHandler;
use rmcp::model::*;
use rmcp::service::RequestContext;
use rmcp::service::RoleServer;
pub use rmcp::ErrorData as McpError;

use chatdb_proof_core::db::schema_v1;
use chatdb_proof_core::orchestrator::{lifecycle, attempts, step, trajectories};
use chatdb_proof_core::lean::{LeanGateway, RealLeanGateway};
use chatdb_proof_core::models::action::{TypedAction, ActionRequest, ActionRole, StepDisposition, LeanModuleItem, ModuleTheorem};
use chatdb_proof_core::lean::module::assemble_module;
use chatdb_proof_core::models::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use chatdb_proof_core::models::reward::{RewardComponent, RewardComponentId, RewardPolicy};
use chatdb_proof_core::hashing::canonical_hash;

/// Every problem's import manifest starts with these two; problem_imports adds to
/// them. Kept in one place so the "what does a bare problem_create get by
/// default" answer stays consistent with what RealLeanGateway historically
/// hardcoded.
const BASE_IMPORT_MANIFEST: &[&str] = &["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum"];

/// A Lean import target is written verbatim into `import {module}\n` source.
/// This is the entire security boundary for that interpolation: reject
/// anything but a dotted sequence of identifier segments so a string can never
/// contain a newline, comment, or command separator that would let it inject
/// arbitrary Lean source (e.g. `axiom cheat : False`) into every proof file
/// checked against this manifest.
fn valid_lean_module_path(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 256
        && s.split('.').all(|segment| {
            !segment.is_empty()
                && segment.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                && segment.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        })
}

/// A Lean declaration name is written verbatim into `#check {name}\n` source.
/// Same boundary as `valid_lean_module_path`, slightly more permissive to
/// admit Lean identifier characters (primes, unicode letters used in
/// mathlib names) while still excluding anything that could break out of a
/// single `#check` line: whitespace, newlines, comment/command syntax.
fn valid_lean_declaration_name(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 256
        && !s.chars().any(|c| c.is_whitespace())
        && s.chars().all(|c| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.' | '!' | '?'))
}

// -- Mathlib librarian (issue #25) -----------------------------------------
//
// A hint system, deliberately outside the trusted proof transaction: it can
// suggest imports/names/declarations, but nothing here can mark anything
// proved, certify a claim, or mutate an existing problem's import manifest.
// Reads the REAL pinned Mathlib source tree directly (no precomputed offline
// index — a live scan of ~111MB of .lean files takes a fraction of a second,
// so a separately-maintained index would only add staleness risk between
// itself and the actual pinned commit, for no real speed benefit).

const MATHLIB_DECLARATION_KEYWORDS: &[&str] = &[
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "inductive", "class",
];

/// Modifiers Lean allows immediately before a declaration keyword on the same
/// line (e.g. `protected theorem foo`, `private noncomputable def bar`).
/// Mirrors the modifier list `crates/chatdb-core/src/lean/module.rs` bans a
/// CLIENT from writing (there, closing an injection escape); here the
/// direction is reversed — this is real Mathlib source the server only
/// reads, and skipping past a modifier is required to find the keyword at
/// all, not a security boundary.
const MATHLIB_DECLARATION_MODIFIERS: &[&str] = &[
    "protected", "private", "scoped", "local", "noncomputable", "partial", "unsafe",
];

/// Self-review finding: a first pass only recognized a keyword as the VERY
/// FIRST token on a line, missing every modifier-prefixed
/// (`protected theorem ...`) or attribute-prefixed (`@[simp] theorem ...`)
/// declaration — confirmed empirically against the real Mathlib checkout to
/// affect roughly 80% of files, and worse than a mere gap: a query that
/// should hit a modifier-prefixed declaration could instead confidently
/// return an unrelated `exact_match` elsewhere, a false-confidence result.
/// Strips at most one leading attribute list and any number of leading
/// modifiers so the real keyword underneath is what gets matched.
fn strip_mathlib_declaration_prefix(mut line: &str) -> &str {
    if let Some(after_at) = line.strip_prefix('@') {
        if let Some(after_bracket) = after_at.strip_prefix('[') {
            if let Some(close) = after_bracket.find(']') {
                line = after_bracket[close + 1..].trim_start();
            }
        }
    }
    loop {
        let mut advanced = false;
        for modifier in MATHLIB_DECLARATION_MODIFIERS {
            if let Some(rest) = line.strip_prefix(modifier) {
                if rest.starts_with(|c: char| c.is_whitespace()) {
                    line = rest.trim_start();
                    advanced = true;
                    break;
                }
            }
        }
        if !advanced {
            break;
        }
    }
    line
}

/// A single declaration hit from scanning the real Mathlib source tree.
#[derive(Debug, Clone, serde::Serialize)]
struct MathlibDeclarationHit {
    declaration_name: String,
    keyword: String,
    import_module: String,
    file_relative_path: String,
    signature_snippet: String,
    confidence: &'static str,
}

/// Locates the real Mathlib source tree under a Lake project, supporting
/// both the current (`.lake/packages/`) and legacy (`lake-packages/`) Lake
/// dependency layouts. `None` if lean-checker isn't set up at all — the
/// librarian degrades to "unavailable", never to a hard error.
fn mathlib_source_dir(lean_project_path: &std::path::Path) -> Option<std::path::PathBuf> {
    for layout in [".lake/packages", "lake-packages"] {
        let candidate = lean_project_path.join(layout).join("mathlib").join("Mathlib");
        if candidate.is_dir() {
            return Some(candidate);
        }
    }
    None
}

/// Extracts the identifier immediately following a declaration keyword at the
/// start of a trimmed line, e.g. `"theorem foo_bar (n : Nat) : ..."` with
/// `keyword = "theorem"` yields `Some("foo_bar")`. Returns the FILE-LOCAL name
/// only — a known MVP limitation: a declaration nested in `namespace Foo ...
/// end Foo` is written here as `bar`, not `Foo.bar`; the caller can infer the
/// qualified name from nearby `namespace`/`end` lines in the same file if
/// needed, but this tool does not resolve that automatically.
fn extract_declaration_name<'a>(trimmed_line: &'a str, keyword: &str) -> Option<&'a str> {
    let rest = trimmed_line.strip_prefix(keyword)?;
    if !rest.starts_with(|c: char| c.is_whitespace()) {
        return None; // e.g. "theorem_like_helper" must not match keyword "theorem"
    }
    let name_start = rest.trim_start();
    // Bug found via playtest.rs against the real Mathlib source (not caught by
    // the synthetic-tree unit test, which used ASCII-only names): real
    // declaration names can contain multi-byte Unicode characters (e.g. `₂`
    // subscripts). `.chars().take_while(...).count()` counts CHARACTERS, but
    // `name_start[..n]` slices BYTES — using the char count as a byte index
    // panics ("byte index N is not a char boundary") the instant a matched
    // name contains any non-ASCII character. `char_indices()` yields the byte
    // offset of each character, which is always a valid boundary to slice at.
    let end_byte = name_start.char_indices()
        .find(|(_, c)| !(c.is_alphanumeric() || matches!(c, '_' | '\'')))
        .map(|(i, _)| i)
        .unwrap_or(name_start.len());
    if end_byte == 0 {
        return None;
    }
    Some(&name_start[..end_byte])
}

/// Recursively scans every `.lean` file under `mathlib_dir` for declarations
/// whose name contains `query` (case-insensitive substring). Read-only,
/// synchronous filesystem I/O — matches this codebase's existing convention
/// of calling `std::fs` directly rather than via a blocking-pool wrapper
/// (`crates/chatdb-core/src/lean/mod.rs` does the same for its own checks).
/// Collects every match (no early cutoff at `limit`) so exact matches
/// encountered later in the scan aren't silently dropped in favor of
/// nearby-name matches found earlier, then sorts and truncates.
fn scan_mathlib_declarations(mathlib_dir: &std::path::Path, query: &str, limit: usize) -> Vec<MathlibDeclarationHit> {
    let query_lower = query.to_lowercase();
    let mathlib_parent = mathlib_dir.parent().unwrap_or(mathlib_dir);
    let mut hits = Vec::new();
    let mut stack = vec![mathlib_dir.to_path_buf()];
    // Hard collection cap: protects against a degenerate 1-character query
    // matching a huge fraction of the library. Independent of the caller's
    // requested `limit`, which is applied only after sorting below.
    const MAX_RAW_HITS: usize = 2000;
    // Self-review finding: no protection against a symlink cycle under a
    // misconfigured project path (Lake's dependency cache doesn't create one
    // in practice, confirmed against the real checkout, but this is cheap
    // defense-in-depth against a hang on some other layout). Real Mathlib is
    // ~8200 files; this cap is an order of magnitude above that.
    const MAX_DIRS_VISITED: usize = 100_000;
    let mut dirs_visited = 0usize;

    while let Some(dir) = stack.pop() {
        dirs_visited += 1;
        if dirs_visited > MAX_DIRS_VISITED {
            break;
        }
        let Ok(entries) = std::fs::read_dir(&dir) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }
            if path.extension().and_then(|e| e.to_str()) != Some("lean") {
                continue;
            }
            let Ok(content) = std::fs::read_to_string(&path) else { continue };
            for line in content.lines() {
                let trimmed = strip_mathlib_declaration_prefix(line.trim_start());
                for keyword in MATHLIB_DECLARATION_KEYWORDS {
                    let Some(name) = extract_declaration_name(trimmed, keyword) else { continue };
                    if !name.to_lowercase().contains(&query_lower) {
                        continue;
                    }
                    let rel_path = path.strip_prefix(mathlib_parent).unwrap_or(&path);
                    let import_module = rel_path.with_extension("")
                        .components()
                        .map(|c| c.as_os_str().to_string_lossy().into_owned())
                        .collect::<Vec<_>>()
                        .join(".");
                    let confidence = if name == query { "exact_match" } else { "nearby_name" };
                    hits.push(MathlibDeclarationHit {
                        declaration_name: name.to_string(),
                        keyword: keyword.to_string(),
                        import_module,
                        file_relative_path: rel_path.to_string_lossy().replace('\\', "/"),
                        signature_snippet: line.trim().to_string(),
                        confidence,
                    });
                    break; // one keyword match per line is enough
                }
                if hits.len() >= MAX_RAW_HITS {
                    break;
                }
            }
            if hits.len() >= MAX_RAW_HITS {
                break;
            }
        }
        if hits.len() >= MAX_RAW_HITS {
            break;
        }
    }

    hits.sort_by(|a, b| {
        let rank = |c: &str| if c == "exact_match" { 0 } else { 1 };
        rank(a.confidence).cmp(&rank(b.confidence))
            .then_with(|| a.declaration_name.len().cmp(&b.declaration_name.len()))
            .then_with(|| a.declaration_name.cmp(&b.declaration_name))
    });
    hits.truncate(limit);
    hits
}

/// Shared by formalization_plan_create's seeding path and
/// formalization_plan_add_item — the only two sites that construct a
/// formalization_plan_items row.
fn plan_item_kind_str(kind: &PlanItemKind) -> &'static str {
    match kind {
        PlanItemKind::Concept => "concept",
        PlanItemKind::MissingDefinition => "missing_definition",
        PlanItemKind::MissingLemma => "missing_lemma",
        PlanItemKind::PlannedModule => "planned_module",
        PlanItemKind::ExternalCitation => "external_citation",
    }
}

// ---------------------------------------------------------------------------
// Tool argument schemas
// ---------------------------------------------------------------------------

#[derive(JsonSchema, Deserialize)]
pub struct EnvironmentDescribeArgs {}

#[derive(JsonSchema, Deserialize)]
pub struct ProblemCreateArgs {
    pub source_problem_text: String,
    pub root_formal_statement: String,
    #[serde(default)]
    pub normalized_root_rendering: Option<String>,
    #[serde(default)]
    pub environment_hash: Option<String>,
    #[serde(default)]
    pub metadata_json: Option<String>,
    /// Additional Mathlib modules (beyond the base Ring + NormNum set) this
    /// problem's proofs may import — e.g. "Mathlib.NumberTheory.Padics.PadicVal.Basic".
    /// Each is validated (a real compile check, not a name-shape check) before the
    /// problem is created; an unresolvable module is rejected outright. The
    /// resulting manifest is immutable for this problem_version — see
    /// docs/fix_plan_playtest_03.md. Broadening imports for an existing problem
    /// means creating a new problem_version with an extended list.
    #[serde(default)]
    pub problem_imports: Option<Vec<String>>,
    /// Named honestly on purpose: this is NOT a review. It sets fidelity_status
    /// to 'attested' (proving is allowed) — never 'verified'. Episodes created
    /// under 'attested' can reach outcome=kernel_verified but never 'certified',
    /// and their data is excluded from dataset exports by default. Use
    /// problem_submit_fidelity_review for a real, evidence-backed determination.
    #[serde(default)]
    pub unsafe_dev_attestation: bool,
}

#[derive(JsonSchema, Deserialize)]
pub enum FidelityDecision {
    #[serde(rename = "verified")]
    Verified,
    #[serde(rename = "rejected")]
    Rejected,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProblemSubmitFidelityReviewArgs {
    pub problem_version_id: String,
    pub decision: FidelityDecision,
    /// e.g. "human_review", "dual_model_review", "gold_benchmark_alignment" —
    /// free text naming how the decision was reached; not policy-enforced here.
    pub method: String,
    pub approver_id: String,
    pub rubric_version: String,
    /// The server independently recomputes source_problem_hash,
    /// root_statement_hash, and normalized_rendering_hash from the CURRENT
    /// problem_versions row and rejects the submission if these don't match —
    /// a review can only authorize the exact text it actually reviewed.
    pub source_problem_hash: String,
    pub root_statement_hash: String,
    pub rendering_hash: String,
    pub evidence_json: String,
    #[serde(default)]
    pub notes: Option<String>,
    #[serde(default)]
    pub signature: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProblemListArgs {
    #[serde(default)]
    pub limit: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeCreateArgs {
    pub problem_version_id: String,
    #[serde(default)]
    pub max_steps: Option<i32>,
    #[serde(default)]
    pub cost_budget_micros: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeResetArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeObserveArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct AttemptClaimArgs {
    pub episode_id: String,
    pub action_request_id: String,
    pub idempotency_key: String,
    pub expected_revision: i64,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeStepArgs {
    pub episode_id: String,
    pub action_attempt_id: String,
    pub expected_revision: i64,
    pub claim_token: String,
    pub action: TypedAction,
    pub cost_micros: i64,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeStatusArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeCloseArgs {
    pub episode_id: String,
    pub reason: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct ModelCallReserveArgs {
    pub episode_id: String,
    pub action_attempt_id: String,
    pub runner_id: String,
    pub declared_model: String,
    pub max_input_tokens: i64,
    pub max_output_tokens: i64,
    pub reserved_cost_micros: i64,
}

#[derive(JsonSchema, Deserialize)]
pub struct ModelCallSettleArgs {
    pub lease_id: String,
    pub actual_cost_micros: i64,
    pub status: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct TrajectoryExportArgs {
    pub episode_id: String,
    #[serde(default)]
    pub cursor: Option<i64>,
    #[serde(default)]
    pub page_size: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeReplayArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProofExportArgs {
    pub episode_id: String,
    /// "markdown" (default): full human-readable dossier — proof tree, assembled
    /// Lean source, attempt history, integrity line. "lean": bare assembled Lean
    /// source only, ready to paste into a Mathlib project.
    #[serde(default)]
    pub format: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub enum PatternConfidence {
    /// Hand-authored from a documented lesson (e.g. a playtest report), not
    /// mined from local attempt data.
    #[serde(rename = "seed")]
    Seed,
    /// Extracted from real local attempts.
    #[serde(rename = "mined")]
    Mined,
    /// Validated across multiple distinct problems.
    #[serde(rename = "confirmed")]
    Confirmed,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProofPatternCreateArgs {
    /// A unique, stable slug, e.g. "def_wrapped_decide_needs_unfold". Creating
    /// with a pattern_key that already exists is rejected — patterns are not
    /// silently overwritten by a second create call.
    pub pattern_key: String,
    pub title: String,
    /// Free-text symptom this pattern recognizes, e.g. "decide fails on a
    /// goal wrapped behind a def".
    pub failure_signature: String,
    /// Free-text recommended fix, e.g. "unfold <def_name> before decide".
    pub recommended_repair: String,
    #[serde(default)]
    pub applicable_when: Vec<String>,
    #[serde(default)]
    pub avoid_when: Vec<String>,
    #[serde(default)]
    pub source_episode_id: Option<String>,
    #[serde(default)]
    pub source_attempt_ids: Vec<String>,
    pub confidence: PatternConfidence,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProofPatternSearchArgs {
    /// Free-text search against pattern_key/title/failure_signature/
    /// recommended_repair. Omit to list the whole active library. `%` and `_`
    /// act as SQL LIKE wildcards rather than literal characters.
    #[serde(default)]
    pub query: Option<String>,
    #[serde(default)]
    pub limit: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub enum PatternApplicationRole {
    /// This attempt is a real example of the pattern's failure_signature.
    #[serde(rename = "failed_example")]
    FailedExample,
    /// This attempt applied the pattern's recommended_repair and succeeded.
    #[serde(rename = "repair_example")]
    RepairExample,
    /// The pattern was surfaced to a client as a hint before it acted (no
    /// outcome recorded yet).
    #[serde(rename = "suggested_hint")]
    SuggestedHint,
}

#[derive(JsonSchema, Deserialize)]
pub struct ProofPatternRecordApplicationArgs {
    pub pattern_id: String,
    pub episode_id: String,
    #[serde(default)]
    pub action_attempt_id: Option<String>,
    pub role: PatternApplicationRole,
    #[serde(default)]
    pub notes: Option<String>,
}

// -- Draft artifacts + formalization planning (issues #23, #10) -----------
//
// Both explicitly advisory layers over the real trusted machinery: a draft or
// a formalization plan item can never mark anything proved. Real obligations
// are still created only through Decompose (via the normal, budget-accounted
// episode_step flow); formalization_plan_promote_item_to_obligation only
// records a metadata LINK to an obligation that already exists that way.

#[derive(JsonSchema, Deserialize)]
pub struct DraftCreateArgs {
    pub problem_version_id: String,
    /// A draft may exist before any episode is created for the problem.
    #[serde(default)]
    pub episode_id: Option<String>,
    pub content: String,
    /// Free text naming who/what produced this draft (a model identity, a
    /// human reviewer, ...). Not policy-enforced.
    pub author: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct DraftObserveArgs {
    pub draft_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub enum DraftMoveKind {
    #[serde(rename = "construction")] Construction,
    #[serde(rename = "auxiliary_lemma")] AuxiliaryLemma,
    #[serde(rename = "case_split")] CaseSplit,
    #[serde(rename = "induction")] Induction,
    #[serde(rename = "reduction")] Reduction,
    #[serde(rename = "bijection")] Bijection,
    #[serde(rename = "counterexample_search")] CounterexampleSearch,
    #[serde(rename = "asymptotic_step")] AsymptoticStep,
    #[serde(rename = "external_citation")] ExternalCitation,
    #[serde(rename = "unknown")] Unknown,
}

#[derive(JsonSchema, Deserialize)]
pub struct DraftMoveInput {
    pub move_kind: DraftMoveKind,
    pub description: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct DraftExtractMovesArgs {
    pub draft_id: String,
    /// The moves an external agent identified in this draft's content — the
    /// server never infers these itself (no inference code lives in ChatDB).
    /// Appended after any moves already recorded for this draft, not
    /// replaced.
    pub moves: Vec<DraftMoveInput>,
}

#[derive(JsonSchema, Deserialize)]
pub enum PlanItemKind {
    #[serde(rename = "concept")] Concept,
    #[serde(rename = "missing_definition")] MissingDefinition,
    #[serde(rename = "missing_lemma")] MissingLemma,
    #[serde(rename = "planned_module")] PlannedModule,
    #[serde(rename = "external_citation")] ExternalCitation,
}

#[derive(JsonSchema, Deserialize)]
pub struct SeedPlanItemFromMove {
    pub draft_move_id: String,
    /// What kind of plan item this move becomes — the client decides this,
    /// since a draft move's proof-strategy kind (e.g. "bijection") and a plan
    /// item's planning-target kind (e.g. "missing_lemma") are different
    /// vocabularies with no automatic mapping between them.
    pub kind: PlanItemKind,
}

#[derive(JsonSchema, Deserialize)]
pub struct FormalizationPlanCreateArgs {
    pub problem_version_id: String,
    pub title: String,
    #[serde(default)]
    pub source_draft_id: Option<String>,
    /// Draft moves (each must belong to source_draft_id) to seed as the
    /// plan's initial items. Each selected move is marked promoted.
    #[serde(default)]
    pub seed_items_from_draft_moves: Vec<SeedPlanItemFromMove>,
    #[serde(default)]
    pub risk_flags: Vec<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct FormalizationPlanObserveArgs {
    pub plan_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub enum PlanStatus {
    #[serde(rename = "draft")] Draft,
    #[serde(rename = "active")] Active,
    #[serde(rename = "completed")] Completed,
    #[serde(rename = "abandoned")] Abandoned,
}

#[derive(JsonSchema, Deserialize)]
pub struct FormalizationPlanUpdateArgs {
    pub plan_id: String,
    #[serde(default)]
    pub title: Option<String>,
    #[serde(default)]
    pub status: Option<PlanStatus>,
    #[serde(default)]
    pub risk_flags: Option<Vec<String>>,
}

#[derive(JsonSchema, Deserialize)]
pub struct FormalizationPlanAddItemArgs {
    pub plan_id: String,
    pub kind: PlanItemKind,
    pub description: String,
    #[serde(default)]
    pub mathlib_candidate_names: Vec<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct FormalizationPlanAttachLookupArgs {
    pub plan_item_id: String,
    /// Mirrored verbatim from a lean_declaration_lookup result's `status`
    /// field (e.g. "available", "not_available_under_current_manifest",
    /// "not_in_current_import_scope", "unknown_declaration",
    /// "environment_error"). This attaches that result as a hint; it is not
    /// re-validated or re-run here.
    pub lookup_status: String,
    #[serde(default)]
    pub matched_name: Option<String>,
    #[serde(default)]
    pub diagnostics: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct FormalizationPlanPromoteItemToObligationArgs {
    pub plan_item_id: String,
    pub episode_id: String,
    /// Must already exist (created through a normal Decompose action via
    /// episode_step) and belong to episode_id. This tool only records the
    /// link — it never creates the obligation itself.
    pub obligation_id: String,
}

// -- Mathlib librarian (issue #25) -----------------------------------------

#[derive(JsonSchema, Deserialize)]
pub struct MathlibSearchDeclarationsArgs {
    /// Case-insensitive substring to search for in Mathlib declaration names
    /// (theorem/lemma/def/abbrev/instance/structure/inductive/class).
    pub query: String,
    #[serde(default)]
    pub limit: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub struct MathlibSearchLocalArtifactsArgs {
    /// Case-insensitive substring to search for among this ChatDB instance's
    /// OWN previously-verified theorem/def names — a local precedent, not a
    /// Mathlib-library result.
    pub query: String,
    #[serde(default)]
    pub limit: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub enum LibrarianConfidence {
    /// The suggested name matches exactly.
    #[serde(rename = "exact_match")] ExactMatch,
    /// A similarly-named declaration was found; not confirmed as the right one.
    #[serde(rename = "nearby_name")] NearbyName,
    /// Matched by type signature rather than name (not produced by the
    /// current search tools — reserved for a future type-aware search).
    #[serde(rename = "type_match")] TypeMatch,
    /// Found via a prior local ChatDB artifact using this or a similar name.
    #[serde(rename = "usage_example")] UsageExample,
    /// No useful signal either way.
    #[serde(rename = "unknown")] Unknown,
}

#[derive(JsonSchema, Deserialize)]
pub struct FormalizationPlanAttachLibrarianResultArgs {
    pub plan_item_id: String,
    pub declaration_name: String,
    pub confidence: LibrarianConfidence,
    #[serde(default)]
    pub import_module: Option<String>,
    #[serde(default)]
    pub snippet: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct LeanDeclarationLookupArgs {
    pub problem_version_id: String,
    /// Fully-qualified names to check, e.g. "Nat.factorization", "padicValNat".
    pub names: Vec<String>,
    /// false (default, fast — sub-second beyond process spawn): only checks
    /// under the problem's own manifest. A failure reports
    /// "not_available_under_current_manifest" WITHOUT determining whether that's
    /// because the name needs an import or is genuinely absent.
    /// true (slow — reliably 15-40+ seconds, since there is no persistent Lean
    /// server and the full Mathlib umbrella must be loaded from a cold process):
    /// also checks names that failed under "import Mathlib", splitting the
    /// result into "not_in_current_import_scope" vs "unknown_declaration". Only
    /// set this when that distinction is worth the wait.
    #[serde(default)]
    pub deep_check: bool,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_tool<T: JsonSchema>(name: &'static str, desc: &'static str) -> Tool {
    let settings = schemars::r#gen::SchemaSettings::draft07().with(|s| {
        s.option_nullable = true;
        s.option_add_null_type = false;
        // Inline nested types (e.g. TypedAction) at the parameter site instead of
        // emitting `$ref: #/definitions/...`. Many client harnesses decide whether
        // a parameter is an object by the *declared* type at the param node and do
        // not chase refs — a `$ref` there makes them ship the value as a string.
        // Inlining also sidesteps the draft-2020-12 `definitions` vs `$defs` split.
        s.inline_subschemas = true;
    });
    let generator = settings.into_generator();
    let mut schema = generator.into_root_schema_for::<T>();
    schema.schema.metadata().id = Some("https://json-schema.org/draft/2020-12/schema".to_string());
    let mut val = serde_json::to_value(&schema.schema).unwrap();
    annotate_oneof_objecthood(&mut val);
    let obj = val.as_object().unwrap().clone();
    Tool::new(name, desc, obj)
}

/// schemars emits tagged-enum schemas as a bare `oneOf` with no top-level `type`.
/// Coercion-by-declared-type clients need to see `"type": "object"` at the node
/// itself, so stamp it on wherever every branch of the oneOf is an object.
fn annotate_oneof_objecthood(val: &mut serde_json::Value) {
    match val {
        serde_json::Value::Object(obj) => {
            let all_branches_are_objects = obj.get("oneOf").and_then(|v| v.as_array()).map(|arr| {
                !arr.is_empty() && arr.iter().all(|b| b.get("type").and_then(|t| t.as_str()) == Some("object"))
            }).unwrap_or(false);
            if all_branches_are_objects && !obj.contains_key("type") {
                obj.insert("type".to_string(), serde_json::Value::String("object".to_string()));
            }
            for (_, v) in obj.iter_mut() {
                annotate_oneof_objecthood(v);
            }
        }
        serde_json::Value::Array(arr) => {
            for v in arr.iter_mut() {
                annotate_oneof_objecthood(v);
            }
        }
        _ => {}
    }
}

fn query_action_request(conn: &Connection, id: Uuid) -> Result<ActionRequest, rusqlite::Error> {
    conn.query_row(
        "SELECT id, episode_id, problem_version_id, episode_revision, request_sequence_number, role, state_hash_before, status, expiration_at, created_at FROM action_requests WHERE id = ?1",
        [id.to_string()],
        |row| {
            let id_str: String = row.get(0)?;
            let ep_id_str: String = row.get(1)?;
            let pv_id_str: String = row.get(2)?;
            let role_str: String = row.get(5)?;
            let role = match role_str.as_str() {
                "prover" => ActionRole::Prover,
                "reviewer" => ActionRole::Reviewer,
                _ => ActionRole::Human,
            };
            let created_at_str: String = row.get(9)?;
            let created_at = chrono::DateTime::parse_from_rfc3339(&created_at_str).unwrap().with_timezone(&Utc);
            let exp_str: Option<String> = row.get(8)?;
            let expiration_at = exp_str.map(|s| chrono::DateTime::parse_from_rfc3339(&s).unwrap().with_timezone(&Utc));

            Ok(ActionRequest {
                id: Uuid::parse_str(&id_str).unwrap(),
                episode_id: Uuid::parse_str(&ep_id_str).unwrap(),
                problem_version_id: Uuid::parse_str(&pv_id_str).unwrap(),
                episode_revision: row.get(3)?,
                request_sequence_number: row.get(4)?,
                role,
                state_hash_before: row.get(6)?,
                status: row.get(7)?,
                expiration_at,
                created_at,
            })
        }
    )
}

fn mcp_invalid_params(msg: impl Into<std::borrow::Cow<'static, str>>) -> McpError {
    McpError::new(ErrorCode::INVALID_PARAMS, msg, None)
}

fn mcp_internal_error(msg: impl Into<std::borrow::Cow<'static, str>>) -> McpError {
    McpError::new(ErrorCode::INTERNAL_ERROR, msg, None)
}

fn rs(e: impl std::fmt::Display) -> McpError {
    mcp_internal_error(e.to_string())
}

/// The problem version's environment hash, joined through an episode.
fn episode_env_hash(conn: &Connection, episode_id: &str) -> rusqlite::Result<String> {
    conn.query_row(
        "SELECT pv.environment_hash FROM episodes e JOIN problem_versions pv ON e.problem_version_id = pv.id WHERE e.id = ?1",
        [episode_id],
        |row| row.get(0),
    )
}

/// Small, cheap fingerprint of the episode's externally-visible progress. Not a
/// full content-addressed state hash of every obligation — good enough to chain
/// trajectory events and to give `state_hash_before` on action_requests real
/// content instead of a placeholder.
fn episode_progress_hash(tx: &Transaction, episode_id: &str) -> Result<String, McpError> {
    let (rev, steps, state): (i64, i64, String) = tx.query_row(
        "SELECT current_revision, step_count, state FROM episodes WHERE id = ?1",
        [episode_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).map_err(rs)?;
    canonical_hash(&serde_json::json!({"revision": rev, "step_count": steps, "state": state})).map_err(mcp_internal_error)
}

/// Everything `episode_step` does with the (by then fully resolved)
/// `Result<LeanVerificationOutcome, StepError>` — disposition mapping, freeing a
/// wedged attempt, terminal/truncation checks, `lifecycle::advance`, and
/// trajectory recording — factored out so it runs identically whether the
/// result came back immediately (`step::attempt_prepare`'s `Done` branches, no
/// Lean call needed) or after a deferred Lean gateway call
/// (`step::attempt_finalize`, run with the DB lock released — see
/// `run_in_background`/two-phase note on `episode_step`). Takes `tx` generically
/// so either transaction can drive it; does NOT commit `tx` — the caller does,
/// once it knows no further writes are coming on that transaction.
struct PostProcessing {
    disposition: StepDisposition,
    accepted: bool,
    error_msg: Option<String>,
    outcome_enum: Option<EpisodeOutcome>,
    term_reason: Option<TerminationReason>,
    trunc_reason: Option<TruncationReason>,
    next_req_id: Option<Uuid>,
}

#[allow(clippy::too_many_arguments)]
fn run_step_post_processing(
    tx: &Transaction,
    ep_uuid: Uuid,
    episode_id: &str,
    attempt_uuid: Uuid,
    action: &TypedAction,
    outcome_res: Result<chatdb_proof_core::models::LeanVerificationOutcome, step::StepError>,
    target_obligation_id: &Option<String>,
    state_hash_before: &str,
) -> Result<PostProcessing, McpError> {
    let (disposition, accepted, error_msg) = match &outcome_res {
        Ok(chatdb_proof_core::models::LeanVerificationOutcome::KernelPass) => {
            (StepDisposition::Accepted, true, None)
        }
        Ok(_) => (StepDisposition::Accepted, false, None),
        Err(step::StepError::Conflict) => (
            StepDisposition::StaleRevision, false,
            Some("Revision conflict — retry episode_step with the episode's current revision (see episode_status); the claim is still valid".to_string()),
        ),
        Err(step::StepError::InvalidAttempt) => (
            StepDisposition::InvalidResponse, false,
            Some("Invalid attempt claim or status".to_string()),
        ),
        Err(e) => (StepDisposition::Error, false, Some(format!("{:?}", e))),
    };

    // Recovery: a Conflict means the client should retry with a corrected
    // revision using the SAME claim (nothing to reset). InvalidAttempt means
    // there was never a real, matching attempt row to reset (or, for a
    // finalize-stage InvalidAttempt, the attempt was reclaimed by an expiry
    // sweep while the Lean call was in flight — also nothing safe to reset).
    // Everything past that point (attempt already marked 'executing') failed
    // structurally and must be freed so the request doesn't wedge until the
    // 5-minute expiry.
    if let Err(e) = &outcome_res {
        if matches!(e, step::StepError::LeanGatewayError(_) | step::StepError::ActionSchemaInvalid(_) | step::StepError::DatabaseError(_) | step::StepError::Internal(_)) {
            let new_status = if matches!(e, step::StepError::LeanGatewayError(_)) { "infrastructure_failed" } else { "abandoned" };
            attempts::attempt_abandon(tx, attempt_uuid, new_status).map_err(rs)?;
        }
    }

    let mut is_terminated = false;
    let mut is_truncated = false;
    let mut term_reason = None;
    let mut trunc_reason = None;
    let mut outcome_enum: Option<EpisodeOutcome> = None;

    if disposition == StepDisposition::Accepted {
        let is_give_up = matches!(action, TypedAction::GiveUp);

        if is_give_up {
            tx.execute(
                "UPDATE episodes SET state = 'terminated', outcome = ?1, termination_reason = ?2, completed_at = ?3 WHERE id = ?4",
                (EpisodeOutcome::GaveUp.to_string(), TerminationReason::ModelGaveUp.to_string(), Utc::now().to_rfc3339(), episode_id),
            ).map_err(rs)?;
            is_terminated = true;
            term_reason = Some(TerminationReason::ModelGaveUp);
            outcome_enum = Some(EpisodeOutcome::GaveUp);
        } else {
            let root_proved: bool = tx.query_row(
                "SELECT status FROM episode_obligations WHERE episode_id = ?1 AND kind = 'root'",
                [episode_id],
                |row| row.get::<_, String>(0),
            ).optional().map_err(rs)?.map(|s| s == "proved").unwrap_or(false);

            if root_proved {
                // PROOF SOUNDNESS ("Lean proved this exact formal statement")
                // and STATEMENT FIDELITY ("this formal statement represents the
                // source problem") are independent claims. A kernel-verified root
                // is only 'certified' — and only promotes the problem to COMPLETE
                // — when the problem's fidelity_status is ALSO 'verified'. This is
                // the fix for the weakened-root exploit: proving a trivially-true
                // relaxation of the source statement must never present as
                // certifying the source claim.
                let fidelity_status: String = tx.query_row(
                    "SELECT pv.fidelity_status FROM episodes e JOIN problem_versions pv ON e.problem_version_id = pv.id WHERE e.id = ?1",
                    [episode_id],
                    |row| row.get(0),
                ).map_err(rs)?;
                let fidelity_verified = fidelity_status == "verified";

                let final_outcome = if fidelity_verified { EpisodeOutcome::Certified } else { EpisodeOutcome::KernelVerified };
                tx.execute(
                    "UPDATE episodes SET state = 'terminated', outcome = ?1, termination_reason = ?2, completed_at = ?3 WHERE id = ?4",
                    (final_outcome.to_string(), TerminationReason::RootProved.to_string(), Utc::now().to_rfc3339(), episode_id),
                ).map_err(rs)?;

                if fidelity_verified {
                    // Advance the problem lifecycle too, so problem_list is a
                    // status board rather than a stale cache of PROVING rows.
                    tx.execute(
                        "UPDATE problem_versions SET state = 'COMPLETE'
                         WHERE id = (SELECT problem_version_id FROM episodes WHERE id = ?1)
                         AND state = 'PROVING'",
                        [episode_id],
                    ).map_err(rs)?;
                } else {
                    // Root is proved but fidelity isn't — park the problem in
                    // FIDELITY_REVIEW rather than PROVING (proof search is done)
                    // or COMPLETE (nothing has been certified). A later
                    // problem_submit_fidelity_review(decision=verified) promotes
                    // this episode's outcome to 'certified' retroactively.
                    tx.execute(
                        "UPDATE problem_versions SET state = 'FIDELITY_REVIEW'
                         WHERE id = (SELECT problem_version_id FROM episodes WHERE id = ?1)
                         AND state = 'PROVING'",
                        [episode_id],
                    ).map_err(rs)?;
                }
                is_terminated = true;
                term_reason = Some(TerminationReason::RootProved);
                outcome_enum = Some(final_outcome);
            } else {
                let (steps, max_steps, budget): (i64, Option<i64>, Option<i64>) = tx.query_row(
                    "SELECT step_count, max_steps, cost_budget_micros FROM episodes WHERE id = ?1",
                    [episode_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                ).map_err(rs)?;

                let steps_exhausted = max_steps.map(|m| steps >= m).unwrap_or(false);
                let budget_exhausted = budget.map(|b| b <= 0).unwrap_or(false);

                if steps_exhausted || budget_exhausted {
                    tx.execute(
                        "UPDATE episodes SET state = 'truncated', outcome = ?1, truncation_reason = ?2, completed_at = ?3 WHERE id = ?4",
                        (EpisodeOutcome::BudgetExhausted.to_string(), TruncationReason::BudgetExhausted.to_string(), Utc::now().to_rfc3339(), episode_id),
                    ).map_err(rs)?;
                    is_truncated = true;
                    trunc_reason = Some(TruncationReason::BudgetExhausted);
                    outcome_enum = Some(EpisodeOutcome::BudgetExhausted);
                }
            }
        }
    }

    // If not ended, call advance to prepare the next request
    let next_req_id = if !is_terminated && !is_truncated && disposition == StepDisposition::Accepted {
        lifecycle::advance(tx, ep_uuid).map_err(rs)?
    } else {
        None
    };

    // Trajectory: always record what was attempted (append-only truth,
    // including rejected/conflicted/errored attempts), then terminal markers.
    let env_hash = episode_env_hash(tx, episode_id).map_err(rs)?;
    let obligation_info: Option<(String, String, String)> = match target_obligation_id {
        Some(oid) => tx.query_row(
            "SELECT problem_version_id, lean_statement, statement_hash FROM episode_obligations WHERE id = ?1",
            [oid],
            |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
        ).optional().map_err(rs)?,
        None => None,
    };
    let dependency_obligation_ids: Vec<String> = match target_obligation_id {
        Some(oid) => {
            let mut s = tx.prepare(
                "SELECT dependency_obligation_id FROM episode_obligation_edges e
                 JOIN episode_obligations dep ON dep.id = e.dependency_obligation_id
                 WHERE e.parent_obligation_id = ?1 AND dep.status = 'proved'",
            ).map_err(rs)?;
            s.query_map([oid], |row| row.get::<_, String>(0)).map_err(rs)?
                .collect::<Result<Vec<_>, _>>().map_err(rs)?
        }
        None => vec![],
    };
    let lean_outcome_str = outcome_res.as_ref().ok().map(|o| o.to_string());
    let state_hash_after = episode_progress_hash(tx, episode_id)?;

    // For an accepted SubmitModule, record the verified module's source +
    // declaration-manifest hashes in the trajectory payload so replay can
    // confirm the exact artifact re-derives (issue #4). Read back from the
    // just-inserted row inside the same transaction.
    let module_artifact: Option<(String, String)> = match (action, target_obligation_id, accepted) {
        (TypedAction::SubmitModule { .. }, Some(oid), true) => tx.query_row(
            "SELECT module_source_hash, declaration_manifest_hash FROM episode_verified_modules
             WHERE root_obligation_id = ?1 ORDER BY verified_at DESC LIMIT 1",
            [oid],
            |row| Ok((row.get(0)?, row.get(1)?)),
        ).optional().map_err(rs)?,
        _ => None,
    };

    let payload = serde_json::json!({
        "obligation_id": target_obligation_id,
        "problem_version_id": obligation_info.as_ref().map(|(pv, _, _)| pv),
        "lean_statement": obligation_info.as_ref().map(|(_, s, _)| s),
        "statement_hash": obligation_info.as_ref().map(|(_, _, h)| h),
        "dependency_obligation_ids": dependency_obligation_ids,
        "action": action,
        "outcome": lean_outcome_str,
        "disposition": disposition,
        "accepted": accepted,
        "diagnostics": error_msg,
        "module_source_hash": module_artifact.as_ref().map(|(s, _)| s),
        "declaration_manifest_hash": module_artifact.as_ref().map(|(_, d)| d),
    });
    trajectories::record_event(
        tx, ep_uuid, "action_committed", state_hash_before, &state_hash_after, &env_hash,
        &payload.to_string(),
    ).map_err(mcp_internal_error)?;

    if is_terminated {
        trajectories::record_event(
            tx, ep_uuid, "episode_terminated", &state_hash_after, &state_hash_after, &env_hash,
            &serde_json::json!({"outcome": outcome_enum, "termination_reason": term_reason}).to_string(),
        ).map_err(mcp_internal_error)?;
    } else if is_truncated {
        trajectories::record_event(
            tx, ep_uuid, "episode_truncated", &state_hash_after, &state_hash_after, &env_hash,
            &serde_json::json!({"outcome": outcome_enum, "truncation_reason": trunc_reason}).to_string(),
        ).map_err(mcp_internal_error)?;
    }

    Ok(PostProcessing { disposition, accepted, error_msg, outcome_enum, term_reason, trunc_reason, next_req_id })
}

// ---------------------------------------------------------------------------
// Proof export rendering
// ---------------------------------------------------------------------------

struct ExportObligation {
    id: String,
    theorem_name: String,
    lean_statement: String,
    status: String,
    kind: String,
    failure_lesson: Option<String>,
}

struct ExportAttempt {
    seq: i64,
    obligation_name: String,
    action_type: String,
    detail: String,
    verdict: String,
    created_at: String,
}

fn status_marker(status: &str) -> &'static str {
    match status {
        "proved" => "✅",
        "refuted" => "❌",
        "in_progress" => "🔄",
        "open" => "⏳",
        "abandoned" | "superseded" => "🚫",
        _ => "❔",
    }
}

fn render_proof_export(conn: &Connection, episode_id: &str, format: &str) -> Result<String, McpError> {
    let ep: Option<(String, String, Option<String>, Option<String>, i64, Option<i64>, String, Option<String>)> = conn.query_row(
        "SELECT problem_version_id, state, outcome, termination_reason, step_count, cost_budget_micros, created_at, completed_at
         FROM episodes WHERE id = ?1",
        [episode_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?, row.get(6)?, row.get(7)?)),
    ).optional().map_err(rs)?;
    let Some((pv_id, state, outcome, term_reason, step_count, budget_left, created_at, completed_at)) = ep else {
        return Err(mcp_invalid_params(format!("unknown episode_id: {}", episode_id)));
    };

    let (source_text, root_statement, fidelity_status, manifest_json, manifest_hash, env_hash):
        (String, String, String, String, String, String) = conn.query_row(
        "SELECT source_problem_text, root_formal_statement, fidelity_status,
                import_manifest_json, import_manifest_hash, environment_hash
         FROM problem_versions WHERE id = ?1",
        [&pv_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?)),
    ).map_err(rs)?;
    // The export must be a receipt of what the verifier actually compiled, not a
    // reconstructed approximation — so the assembled Lean source carries the
    // problem's real, immutable import manifest (never a hardcoded Ring/NormNum
    // stub). A malformed stored manifest is a corrupted receipt, not a normal
    // condition to paper over: fall back to the base set so export doesn't crash,
    // but flag it loudly in both formats (a WARNING comment in the lean source, a
    // visible callout in the dossier) rather than silently rendering an artifact
    // that looks like a normal, trustworthy receipt when it isn't one.
    let manifest_parse_failed = serde_json::from_str::<Vec<String>>(&manifest_json).is_err();
    let import_manifest: Vec<String> = serde_json::from_str::<Vec<String>>(&manifest_json)
        .unwrap_or_else(|_| vec!["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()]);

    // Verified modules (issue #4): a SubmitModule proves its obligation as a
    // whole. When present, the export renders the EXACT module source —
    // re-assembled deterministically from the stored structured items, so its
    // hash equals the recorded module_source_hash — making the lean export
    // byte-for-byte replayable and the dossier show the development, not just a
    // proof tree.
    #[derive(Deserialize)]
    struct StoredModule { module_items: Vec<LeanModuleItem>, root_theorem: ModuleTheorem }
    struct RenderedModule {
        source: String,
        source_hash: String,
        items: Vec<(i64, String, String)>,
        /// True if re-assembling `module_items_json` (against the problem's
        /// CURRENT import_manifest_json — the same one this whole export
        /// already uses) produced source that does NOT hash to the recorded
        /// `module_source_hash`. This is a real, surfaced-not-swallowed signal
        /// that the receipt may no longer describe what was actually verified
        /// (e.g. the manifest was extended after this module verified).
        hash_mismatch: bool,
    }
    let mut rendered_modules: Vec<RenderedModule> = Vec::new();
    // Every module row that failed to re-render — parse failure or policy
    // re-check failure — surfaced as a loud warning instead of silently
    // vanishing from the export (the same discipline already applied to a
    // corrupted import_manifest_json above). A module that verified but can no
    // longer be reconstructed is exactly the kind of receipt failure this
    // export exists to catch, not hide.
    let mut broken_modules: Vec<(String, String)> = Vec::new();
    {
        let ns16 = pv_id.replace('-', "");
        let problem_namespace = format!("ChatDB.P_{}", &ns16[..16.min(ns16.len())]);
        let mut mstmt = conn.prepare(
            "SELECT id, root_statement_hash, module_items_json, module_source_hash
             FROM episode_verified_modules WHERE episode_id = ?1 ORDER BY verified_at ASC",
        ).map_err(rs)?;
        let rows: Vec<(String, String, String, String)> = mstmt
            .query_map([episode_id], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)))
            .map_err(rs)?
            .collect::<Result<Vec<_>, _>>()
            .map_err(rs)?;
        for (mod_id, root_hash, items_json, src_hash) in rows {
            let stored = match serde_json::from_str::<StoredModule>(&items_json) {
                Ok(s) => s,
                Err(e) => { broken_modules.push((mod_id, format!("stored module_items_json failed to parse: {}", e))); continue; }
            };
            let asm = match assemble_module(&problem_namespace, &root_hash, &stored.module_items, &stored.root_theorem, &import_manifest) {
                Ok(a) => a,
                Err(e) => { broken_modules.push((mod_id, format!("re-assembly no longer passes policy: {}", e))); continue; }
            };
            let mut istmt = conn.prepare(
                "SELECT item_order, item_kind, lean_name FROM episode_verified_module_items WHERE module_id = ?1 ORDER BY item_order ASC",
            ).map_err(rs)?;
            let items: Vec<(i64, String, String)> = istmt
                .query_map([&mod_id], |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?)))
                .map_err(rs)?
                .collect::<Result<Vec<_>, _>>()
                .map_err(rs)?;
            let hash_mismatch = asm.module_source_hash != src_hash;
            rendered_modules.push(RenderedModule { source: asm.source, source_hash: src_hash, items, hash_mismatch });
        }
    }

    let mut stmt = conn.prepare(
        "SELECT id, theorem_name, lean_statement, status, kind, failure_lesson
         FROM episode_obligations WHERE episode_id = ?1 ORDER BY created_at ASC",
    ).map_err(rs)?;
    let obligations: Vec<ExportObligation> = stmt.query_map([episode_id], |row| {
        Ok(ExportObligation {
            id: row.get(0)?, theorem_name: row.get(1)?, lean_statement: row.get(2)?,
            status: row.get(3)?, kind: row.get(4)?, failure_lesson: row.get(5)?,
        })
    }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT parent_obligation_id, dependency_obligation_id FROM episode_obligation_edges
         WHERE parent_obligation_id IN (SELECT id FROM episode_obligations WHERE episode_id = ?1)",
    ).map_err(rs)?;
    let edges: Vec<(String, String)> = stmt.query_map([episode_id], |row| Ok((row.get(0)?, row.get(1)?)))
        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    drop(stmt);

    // Walk trajectory: collect winning proofs per obligation + full attempt history.
    let mut stmt = conn.prepare(
        "SELECT event_sequence_number, event_type, payload_json, created_at FROM trajectory_events
         WHERE episode_id = ?1 ORDER BY event_sequence_number ASC",
    ).map_err(rs)?;
    let events: Vec<(i64, String, String, String)> = stmt.query_map([episode_id], |row| {
        Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?))
    }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    drop(stmt);

    let name_of = |oid: &Option<String>| -> String {
        oid.as_ref()
            .and_then(|o| obligations.iter().find(|x| &x.id == o))
            .map(|x| x.theorem_name.clone())
            .unwrap_or_else(|| "—".to_string())
    };

    let mut winning_proof: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let mut attempts: Vec<ExportAttempt> = Vec::new();
    let (mut first_hash, mut last_hash) = (String::new(), String::new());

    for (seq, event_type, payload_json, ev_created) in &events {
        if event_type != "action_committed" {
            continue;
        }
        let Ok(payload) = serde_json::from_str::<serde_json::Value>(payload_json) else { continue };
        let action = &payload["action"];
        let action_type = action["type"].as_str().unwrap_or("?").to_string();
        let obligation_id = payload["obligation_id"].as_str().map(|s| s.to_string());
        let accepted = payload["accepted"].as_bool().unwrap_or(false);
        let disposition = payload["disposition"].as_str().unwrap_or("?");
        let outcome = payload["outcome"].as_str();

        let (detail, verdict) = match action_type.as_str() {
            "solve" => {
                let proof = action["proof_term"].as_str().unwrap_or("").to_string();
                if accepted && outcome == Some("kernel_pass") {
                    if let Some(oid) = &obligation_id {
                        winning_proof.insert(oid.clone(), proof.clone());
                    }
                }
                let verdict = if disposition != "accepted" {
                    format!("⚠️ {}", disposition)
                } else if outcome == Some("kernel_pass") {
                    "✅ kernel_pass".to_string()
                } else {
                    format!("❌ {}", outcome.unwrap_or("kernel_fail"))
                };
                (format!("`{}`", proof.trim().replace('\n', " ; ")), verdict)
            }
            "submit_module" => {
                // A module has no single flat proof_term — the closest analogue
                // for the theorem-by-theorem fallback rendering is the root
                // theorem's own proof_term (helper defs/theorems aren't shown by
                // this fallback path; a caller wanting the exact verified module
                // should get it from the dedicated module rendering instead).
                // Populating winning_proof here is a correctness requirement, not
                // cosmetic: without it, the fallback render below embeds a
                // fabricated `sorry` for an obligation the kernel actually
                // verified — exactly the dishonest-receipt bug this export
                // exists to prevent.
                let proof = action["root_theorem"]["proof_term"].as_str().unwrap_or("").to_string();
                if accepted && outcome == Some("kernel_pass") {
                    if let Some(oid) = &obligation_id {
                        winning_proof.insert(oid.clone(), proof.clone());
                    }
                }
                let verdict = if disposition != "accepted" {
                    format!("⚠️ {}", disposition)
                } else if outcome == Some("kernel_pass") {
                    "✅ kernel_pass (module)".to_string()
                } else {
                    format!("❌ {}", outcome.unwrap_or("kernel_fail"))
                };
                (format!("module root: `{}`", proof.trim().replace('\n', " ; ")), verdict)
            }
            "decompose" => {
                let subs: Vec<String> = action["sub_lemmas"].as_array().map(|a| {
                    a.iter().filter_map(|v| v.as_str()).map(|s| format!("`{}`", s)).collect()
                }).unwrap_or_default();
                (format!("split into {}", subs.join(" and ")), if accepted { "✅ accepted".to_string() } else { format!("⚠️ {}", disposition) })
            }
            "give_up" => ("gave up".to_string(), "🏳️".to_string()),
            other => (other.to_string(), disposition.to_string()),
        };

        attempts.push(ExportAttempt {
            seq: *seq,
            obligation_name: name_of(&obligation_id),
            action_type,
            detail,
            verdict,
            created_at: ev_created.clone(),
        });
    }

    // Hash chain endpoints for the integrity line.
    let chain: Option<(String, String, i64)> = conn.query_row(
        "SELECT (SELECT event_hash FROM trajectory_events WHERE episode_id = ?1 ORDER BY event_sequence_number ASC LIMIT 1),
                (SELECT event_hash FROM trajectory_events WHERE episode_id = ?1 ORDER BY event_sequence_number DESC LIMIT 1),
                (SELECT COUNT(*) FROM trajectory_events WHERE episode_id = ?1)",
        [episode_id],
        |row| Ok((row.get::<_, Option<String>>(0)?.unwrap_or_default(), row.get::<_, Option<String>>(1)?.unwrap_or_default(), row.get(2)?)),
    ).optional().map_err(rs)?;
    if let Some((f, l, _)) = &chain {
        first_hash = f.clone();
        last_hash = l.clone();
    }
    let event_count = chain.map(|(_, _, n)| n).unwrap_or(0);

    // Assembled Lean source: proved obligations, children before parents (leaves
    // carry no unproved deps by construction), root last.
    fn children_of<'a>(pid: &str, obligations: &'a [ExportObligation], edges: &[(String, String)]) -> Vec<&'a ExportObligation> {
        edges.iter().filter(|(p, _)| p == pid)
            .filter_map(|(_, c)| obligations.iter().find(|o| &o.id == c))
            .collect()
    }
    fn push_postorder<'a>(
        o: &'a ExportObligation,
        obligations: &'a [ExportObligation],
        edges: &[(String, String)],
        out: &mut Vec<&'a ExportObligation>,
    ) {
        for c in children_of(&o.id, obligations, edges) {
            push_postorder(c, obligations, edges, out);
        }
        if !out.iter().any(|x| x.id == o.id) {
            out.push(o);
        }
    }
    let root = obligations.iter().find(|o| o.kind == "root");
    let mut lean_order: Vec<&ExportObligation> = Vec::new();
    if let Some(r) = root {
        push_postorder(r, &obligations, &edges, &mut lean_order);
    }
    // Orphans (obligations not reachable from root) still deserve to show up.
    for o in &obligations {
        if !lean_order.iter().any(|x| x.id == o.id) {
            lean_order.insert(0, o);
        }
    }

    let mut lean_src = String::new();
    if manifest_parse_failed {
        lean_src.push_str(&format!(
            "-- WARNING: stored import_manifest_json for this problem_version failed to parse; \
             the imports below are the historical Ring/NormNum fallback, NOT the manifest this proof \
             was actually verified against. This export is NOT a trustworthy receipt (manifest_hash={}).\n",
            manifest_hash
        ));
    }
    for module in &import_manifest {
        lean_src.push_str(&format!("import {}\n", module));
    }
    lean_src.push('\n');
    for o in &lean_order {
        if o.status != "proved" {
            continue;
        }
        let proof = winning_proof.get(&o.id).cloned()
            .unwrap_or_else(|| "  sorry -- proof term not recorded in trajectory".to_string());
        lean_src.push_str(&format!("theorem {} : {} := by\n{}\n\n", o.theorem_name, o.lean_statement, proof.trim_end()));
    }

    if format == "lean" {
        // A verified module is the exact, replayable artifact — prefer it over the
        // theorem-by-theorem reconstruction when one exists.
        if !rendered_modules.is_empty() || !broken_modules.is_empty() {
            let mut out = String::new();
            for (mod_id, reason) in &broken_modules {
                out.push_str(&format!(
                    "-- WARNING: verified module {} could not be re-rendered ({}) — this export is INCOMPLETE, not a full receipt.\n",
                    mod_id, reason
                ));
            }
            for m in &rendered_modules {
                if m.hash_mismatch {
                    out.push_str(&format!(
                        "-- WARNING: re-assembled source below does NOT hash-match the recorded module_source_hash ({}) — \
                         the problem's import manifest or policy may have changed since this module verified. This is NOT a trustworthy receipt.\n",
                        m.source_hash
                    ));
                }
                out.push_str(&m.source);
                out.push_str("\n\n");
            }
            return Ok(out);
        }
        return Ok(lean_src);
    }

    // Markdown dossier. Proof soundness (did Lean verify this exact formal
    // statement?) and statement fidelity (does that formal statement represent
    // the source problem?) are independent claims — a kernel-verified root of a
    // weakened or vacuous formalization must never render as if it certified the
    // source claim. Only outcome == "certified" (which requires BOTH) gets the
    // unqualified CERTIFIED headline.
    let is_certified = outcome.as_deref() == Some("certified");
    let is_kernel_verified_only = outcome.as_deref() == Some("kernel_verified");
    let training_eligible = fidelity_status == "verified";

    let mut md = String::new();
    let headline_marker = match outcome.as_deref() {
        Some("certified") => "✅ CERTIFIED",
        Some("kernel_verified") if fidelity_status == "rejected" => "⚠️ FORMAL PROOF VALID, STATEMENT FIDELITY REJECTED",
        Some("kernel_verified") => "⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED",
        Some("refuted") => "❌ REFUTED",
        Some("gave_up") => "🏳️ GAVE UP",
        Some(other) => other,
        None => "🔄 IN PROGRESS",
    };
    md.push_str(&format!("# {} — {}\n\n", headline_marker, source_text.trim()));

    if is_kernel_verified_only {
        md.push_str(&format!(
            "> This proof establishes:\n>\n> `{}`\n>\n> It does {}certify the source claim above.\n\n",
            root_statement,
            if fidelity_status == "rejected" { "**not** " } else { "**not yet** " },
        ));
    }

    md.push_str(&format!("**Root goal (formal):** `{}`\n\n", root_statement));

    // The three independent claims, always shown together so a reader can never
    // mistake one for the others.
    let proof_soundness = match outcome.as_deref() {
        Some("certified") | Some("kernel_verified") => "VERIFIED",
        Some("refuted") => "REFUTED",
        None => "PENDING",
        Some(_) => "INCOMPLETE",
    };
    let fidelity_display = match fidelity_status.as_str() {
        "verified" => "VERIFIED",
        "rejected" => "REJECTED",
        "revoked" => "REVOKED",
        "attested" => "ATTESTED (unsafe_dev_attestation — not reviewed)",
        _ => "UNVERIFIED",
    };
    let promotion_display = if is_certified { "PROMOTED" } else { "BLOCKED" };
    md.push_str(&format!(
        "| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |\n|---|---|---|---|\n| {} | {} | {} | {} |\n\n",
        proof_soundness, fidelity_display, promotion_display,
        if training_eligible { "eligible" } else { "QUARANTINED" },
    ));

    md.push_str(&format!(
        "| episode | state | steps | budget left (μ$) | started | finished |\n|---|---|---|---|---|---|\n| `{}` | {}{} | {} | {} | {} | {} |\n\n",
        episode_id, state,
        term_reason.map(|r| format!(" ({})", r)).unwrap_or_default(),
        step_count,
        budget_left.map(|b| b.to_string()).unwrap_or_else(|| "—".to_string()),
        &created_at[..created_at.len().min(19)],
        completed_at.map(|c| c[..c.len().min(19)].to_string()).unwrap_or_else(|| "—".to_string()),
    ));

    md.push_str("## Proof tree\n\n");
    fn render_tree(
        o: &ExportObligation,
        obligations: &[ExportObligation],
        edges: &[(String, String)],
        depth: usize,
        md: &mut String,
    ) {
        let indent = "  ".repeat(depth);
        md.push_str(&format!("{}- {} **{}** : `{}`\n", indent, status_marker(&o.status), o.theorem_name, o.lean_statement));
        if let Some(lesson) = &o.failure_lesson {
            if o.status != "proved" {
                md.push_str(&format!("{}  - 💡 last lesson: {}\n", indent, lesson.trim().replace('\n', " ")));
            }
        }
        for c in children_of(&o.id, obligations, edges) {
            render_tree(c, obligations, edges, depth + 1, md);
        }
    }
    match root {
        Some(r) => render_tree(r, &obligations, &edges, 0, &mut md),
        None => md.push_str("*(no obligations seeded yet)*\n"),
    }

    // A verified module is a structured development, not a single proof term —
    // show its declaration manifest and the exact assembled source, so the dossier
    // reflects the module, not only a proof tree.
    if !rendered_modules.is_empty() || !broken_modules.is_empty() {
        md.push_str("\n## Verified module\n\n");
        for (mod_id, reason) in &broken_modules {
            md.push_str(&format!(
                "> ⚠️ **WARNING: incomplete receipt.** Verified module `{}` could not be re-rendered ({}). \
                 This episode has a verified module that is NOT shown below — do not treat this export as complete.\n\n",
                mod_id, reason.replace('|', "\\|"),
            ));
        }
        for (mi, m) in rendered_modules.iter().enumerate() {
            if rendered_modules.len() > 1 {
                md.push_str(&format!("### Module {}\n\n", mi + 1));
            }
            if m.hash_mismatch {
                md.push_str(
                    "> ⚠️ **WARNING: hash mismatch.** The re-assembled source below does NOT hash-match the \
                     recorded `module_source_hash` — the problem's import manifest or policy may have changed \
                     since this module verified. Do not treat this as a trustworthy receipt.\n\n"
                );
            }
            md.push_str(&format!("`module_source_hash: {}`\n\n", m.source_hash));
            md.push_str("| # | kind | name |\n|---|---|---|\n");
            for (order, kind, name) in &m.items {
                md.push_str(&format!("| {} | {} | `{}` |\n", order, kind, name));
            }
            md.push_str(&format!("\n```lean\n{}\n```\n", m.source.trim_end()));
        }
    }

    md.push_str("\n## The proof, assembled\n\n");
    if !rendered_modules.is_empty() || !broken_modules.is_empty() {
        md.push_str("*(see Verified module above — this episode was proved as a structured module)*\n");
    } else if lean_order.iter().any(|o| o.status == "proved") {
        md.push_str(&format!("```lean\n{}```\n", lean_src));
    } else {
        md.push_str("*(nothing proved yet)*\n");
    }

    md.push_str("\n## How it went — every attempt, in order\n\n");
    if attempts.is_empty() {
        md.push_str("*(no actions taken yet)*\n");
    } else {
        md.push_str("| # | obligation | action | detail | verdict |\n|---|---|---|---|---|\n");
        for a in &attempts {
            md.push_str(&format!("| {} | `{}` | {} | {} | {} |\n", a.seq, a.obligation_name, a.action_type, a.detail.replace('|', "\\|"), a.verdict));
        }
    }

    // Verification context: the export is a receipt, so it must state exactly
    // which pinned environment and import manifest the kernel checked this proof
    // under. These are the problem_version's immutable values — the same ones the
    // gateway used — not a reconstruction. A reader can pin a third-party
    // toolchain to `environment_hash` and re-derive `import_manifest_hash` from
    // the listed manifest to confirm they are re-verifying the same artifact.
    md.push_str("\n## Verification context\n\n");
    if manifest_parse_failed {
        md.push_str(&format!(
            "> ⚠️ **WARNING: corrupted receipt.** The stored `import_manifest_json` for this \
             problem_version failed to parse. The Lean export below falls back to the historical \
             Ring/NormNum manifest so export doesn't crash, but that fallback is **not** what this \
             proof was actually verified against (raw stored value: `{}`). Do not treat this export \
             as a trustworthy replay artifact until the stored manifest is repaired.\n\n",
            manifest_json.replace('|', "\\|"),
        ));
    }
    md.push_str(&format!("- **Environment hash:** `{}`\n", env_hash));
    md.push_str(&format!("- **Import manifest hash:** `{}`\n", manifest_hash));
    md.push_str(&format!("- **Import manifest:** `{}`\n", manifest_json));

    md.push_str(&format!(
        "\n## Integrity\n\n{} hash-chained trajectory events, `{}…` → `{}…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.\n",
        event_count,
        &first_hash[..first_hash.len().min(12)],
        &last_hash[..last_hash.len().min(12)],
    ));

    // Lessons applied (issue #24 proof-pattern memory): listed separately from
    // the verified proof above, and never affects it — a pattern application
    // is advisory metadata (see proof_pattern_record_application), not a proof
    // status. Only rendered if at least one was actually recorded for this
    // episode, so a dossier with no pattern activity stays exactly as before.
    let mut pstmt = conn.prepare(
        "SELECT p.title, p.recommended_repair, a.role, a.notes
         FROM proof_pattern_applications a JOIN proof_patterns p ON p.id = a.pattern_id
         WHERE a.episode_id = ?1 ORDER BY a.created_at ASC"
    ).map_err(rs)?;
    let lessons: Vec<(String, String, String, Option<String>)> = pstmt
        .query_map([episode_id], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)))
        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    if !lessons.is_empty() {
        md.push_str("\n## Lessons applied (advisory — not part of the verified proof)\n\n");
        md.push_str("| role | pattern | recommended repair | notes |\n|---|---|---|---|\n");
        for (title, repair, role, notes) in &lessons {
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                role, title.replace('|', "\\|"), repair.replace('|', "\\|"),
                notes.as_deref().unwrap_or("—").replace('|', "\\|"),
            ));
        }
    }

    // Drafts (issue #23): informal content explicitly tied to this episode, or
    // created for this problem_version before any episode existed. Marked
    // loudly as informal — a draft can never mark anything proved, and this
    // listing never affects the proof tree above.
    let mut dstmt = conn.prepare(
        "SELECT content, author, created_at FROM drafts
         WHERE episode_id = ?1 OR (episode_id IS NULL AND problem_version_id = ?2)
         ORDER BY created_at ASC"
    ).map_err(rs)?;
    let drafts: Vec<(String, String, String)> = dstmt
        .query_map((episode_id, &pv_id), |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)))
        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    if !drafts.is_empty() {
        md.push_str("\n## Drafts (informal — not part of the verified proof)\n\n");
        for (content, author, created_at) in &drafts {
            md.push_str(&format!("**{}** ({}):\n\n> {}\n\n", author, created_at, content.replace('\n', "\n> ")));
        }
    }

    // Formalization plans (issues #10, #23): problem-scoped planning
    // scaffolding — required concepts/definitions/lemmas/modules and their
    // Mathlib coverage status. Advisory: a plan's status/coverage never
    // affects the proof tree above; only a real Lean kernel pass does.
    let mut plstmt = conn.prepare(
        "SELECT id, title, status FROM formalization_plans WHERE problem_version_id = ?1 ORDER BY created_at ASC"
    ).map_err(rs)?;
    let plans: Vec<(String, String, String)> = plstmt
        .query_map([&pv_id], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)))
        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    if !plans.is_empty() {
        md.push_str("\n## Formalization plans (advisory — not part of the verified proof)\n\n");
        for (plan_id, title, status) in &plans {
            md.push_str(&format!("**{}** (`{}`, status: {})\n\n", title, plan_id, status));
            let mut istmt = conn.prepare(
                "SELECT kind, description, mathlib_coverage_status, status FROM formalization_plan_items WHERE plan_id = ?1 ORDER BY item_order ASC"
            ).map_err(rs)?;
            let items: Vec<(String, String, String, String)> = istmt
                .query_map([plan_id], |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)))
                .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
            if !items.is_empty() {
                md.push_str("| kind | description | Mathlib coverage | item status |\n|---|---|---|---|\n");
                for (kind, description, coverage, item_status) in &items {
                    md.push_str(&format!(
                        "| {} | {} | {} | {} |\n",
                        kind, description.replace('|', "\\|"), coverage, item_status,
                    ));
                }
                md.push('\n');
            }
        }
    }

    Ok(md)
}

// ---------------------------------------------------------------------------
// Server
// ---------------------------------------------------------------------------

pub struct ChatDbMcp {
    pub conn: Arc<Mutex<Connection>>,
    pub gateway: Box<dyn LeanGateway + Send + Sync>,
    pub lean_available: bool,
    /// The server's own read of what it actually verifies against — the only
    /// trustworthy source for this, since a client can't see the installed
    /// toolchain. `None` when lean-checker isn't set up (`lean_available == false`
    /// implies this is `None`, but the manifest can also be absent independently).
    pub lean_environment: Option<chatdb_proof_core::lean::LeanEnvironmentInfo>,
    /// Stored independently of `gateway` (a trait object with no filesystem
    /// accessor) so the Mathlib librarian (issue #25) can scan the real
    /// pinned Mathlib source tree at `<lean_project_path>/.lake/packages/mathlib/Mathlib`
    /// (or the legacy `lake-packages/` layout) — read-only, no Lean invocation.
    pub lean_project_path: PathBuf,
}

impl ChatDbMcp {
    pub fn new(conn: Arc<Mutex<Connection>>, lean_project_path: PathBuf, elan_bin_path: PathBuf) -> Self {
        let lean_available = elan_bin_path.join("lake.exe").exists()
            && (lean_project_path.join("lakefile.toml").exists() || lean_project_path.join("lakefile.lean").exists());
        let lean_environment = chatdb_proof_core::lean::detect_environment(&lean_project_path);
        let stored_lean_project_path = lean_project_path.clone();
        let gateway = Box::new(RealLeanGateway::new(lean_project_path, elan_bin_path));
        Self { conn, gateway, lean_available, lean_environment, lean_project_path: stored_lean_project_path }
    }
}

pub fn init_db(conn: &Connection) -> rusqlite::Result<()> {
    schema_v1::initialize_v1_db(conn)
}

impl ServerHandler for ChatDbMcp {
    fn get_info(&self) -> ServerInfo {
        ServerInfo::new(ServerCapabilities::default())
            .with_server_info(Implementation::new("chatdb-mcp", "0.3.4"))
    }

    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, McpError> {
        let tools = vec![
            make_tool::<EnvironmentDescribeArgs>("environment_describe", "Return environment version, supported protocol, tool schemas, capabilities"),
            make_tool::<ProblemCreateArgs>("problem_create", "Register a new problem version (source text + root formal statement). fidelity_status starts 'unreviewed' — proving requires either a real problem_submit_fidelity_review or the honestly-named unsafe_dev_attestation=true (which can reach outcome=kernel_verified but never 'certified')"),
            make_tool::<ProblemSubmitFidelityReviewArgs>("problem_submit_fidelity_review", "Record an evidence-backed determination of whether a problem's formal statement represents its source text. Requires the CURRENT source/statement/rendering hashes (recomputed server-side; mismatches are rejected as stale). decision='verified' is the ONLY path to outcome='certified' and problem state COMPLETE; 'rejected' blocks it. This is a review record, not a flag flip — proof soundness (Lean kernel) and statement fidelity (this tool) are independent claims"),
            make_tool::<ProblemListArgs>("problem_list", "List known problem versions (id, state, fidelity_status, root statement)"),
            make_tool::<EpisodeCreateArgs>("episode_create", "Initialize an episode from a problem version whose fidelity_status is 'verified' or 'attested' + config. Returns first observation"),
            make_tool::<EpisodeResetArgs>("episode_reset", "Nondestructive: creates new episode from existing config, sets parent_episode_id"),
            make_tool::<EpisodeObserveArgs>("episode_observe", "Get the active observation and pending action request"),
            make_tool::<AttemptClaimArgs>("attempt_claim", "Claim a pending action request to obtain the action_attempt_id + claim_token required by episode_step. Idempotent on idempotency_key"),
            make_tool::<EpisodeStepArgs>("episode_step", "Submit a typed action against a claimed attempt. `action` is internally tagged — exactly one of: {\"type\":\"solve\",\"proof_term\":\"  norm_num\"} (Lean tactic block proving the target obligation), {\"type\":\"decompose\",\"sub_lemmas\":[\"<lean statement>\", ...]} (split the obligation into child lemmas), {\"type\":\"give_up\"} (terminate the episode). `expected_revision` must equal the episode_revision advertised on the action_request. Settles any lease attached to the attempt atomically"),
            make_tool::<EpisodeStatusArgs>("episode_status", "Retrieve current episode state, revision, budget, step count"),
            make_tool::<EpisodeCloseArgs>("episode_close", "Gracefully truncate an episode"),
            make_tool::<ModelCallReserveArgs>("model_call_reserve", "Reserve a budget lease for a model call"),
            make_tool::<ModelCallSettleArgs>("model_call_settle", "Settle or release a lease without submitting an action (provider failure, cancellation)"),
            make_tool::<TrajectoryExportArgs>("trajectory_export", "Export trajectory with pagination (cursor + page_size)"),
            make_tool::<EpisodeReplayArgs>("episode_replay", "Re-execute typed actions through canonical reducer with Lean re-verification"),
            make_tool::<ProofExportArgs>("proof_export", "Render an episode as a human-readable proof dossier: proof tree with statuses, assembled Lean source (dependencies before root), full attempt history including failures, and the hash-chain integrity line. format: \"markdown\" (default) | \"lean\" (bare assembled source)"),
            make_tool::<LeanDeclarationLookupArgs>("lean_declaration_lookup", "Check whether declaration names resolve — WITHOUT changing proof strategy first. An 'unknown identifier' error from episode_step only ever proves a name didn't resolve under the exact import manifest that attempt used; it never proves the name is absent from the pinned Mathlib. By default this only checks under the problem's own manifest (fast, a few seconds) and returns 'not_available_under_current_manifest' if it fails to resolve — that result alone does NOT mean the name is absent from the library, only that it needs an import. Pass deep_check=true to additionally check under the full Mathlib umbrella and distinguish 'not_in_current_import_scope' (add an import to problem_imports, see problem_create) from genuinely 'unknown_declaration' (misspelled, wrong namespace, or absent); deep_check loads all of Mathlib and reliably takes 15-40+ seconds. Epistemic rule: before concluding an API is unavailable, call this tool with deep_check=true — do not infer library capability from one elaboration failure or from a fast-path result alone"),
            make_tool::<ProofPatternCreateArgs>("proof_pattern_create", "Register a reusable proof-pattern lesson (issue #24 proof-pattern memory) — a failure_signature + recommended_repair pair, e.g. \"decide fails on a def-wrapped goal\" -> \"unfold the def first\". Purely advisory: a pattern can never mark anything proved or change fidelity/certification status. Rejects a duplicate pattern_key rather than overwriting it"),
            make_tool::<ProofPatternSearchArgs>("proof_pattern_search", "Search the proof-pattern library (free-text over pattern_key/title/failure_signature/recommended_repair, or omit query to list the active library). Call this before repeating a failure another attempt already diagnosed"),
            make_tool::<ProofPatternRecordApplicationArgs>("proof_pattern_record_application", "Record that a pattern was relevant to a real (episode[, attempt]) — a failed_example, a repair_example, or a suggested_hint. Insert-only metadata: never writes to episodes/episode_obligations/action_attempts, so it can never change proof/fidelity/certification status"),
            make_tool::<DraftCreateArgs>("draft_create", "Register an informal Draft artifact (issue #23) — untrusted planning/reasoning content preserved before formalization begins. A draft can never mark anything proved"),
            make_tool::<DraftObserveArgs>("draft_observe", "Read back a draft's content and any moves recorded against it"),
            make_tool::<DraftExtractMovesArgs>("draft_extract_moves", "Record structured moves (construction, auxiliary_lemma, case_split, induction, reduction, bijection, counterexample_search, asymptotic_step, external_citation, unknown) the external agent identified in a draft. Metadata only — moves are not obligations until explicitly promoted into a formalization plan item"),
            make_tool::<FormalizationPlanCreateArgs>("formalization_plan_create", "Create a formalization plan (issue #10) for a problem, optionally seeded from selected moves of an existing draft. Tracks required concepts/definitions/lemmas/modules and their Mathlib coverage status — advisory scaffolding, not a proof authority"),
            make_tool::<FormalizationPlanObserveArgs>("formalization_plan_observe", "Read back a formalization plan and all its items"),
            make_tool::<FormalizationPlanUpdateArgs>("formalization_plan_update", "Update a formalization plan's title, status, or risk flags"),
            make_tool::<FormalizationPlanAddItemArgs>("formalization_plan_add_item", "Add a planning item (concept, missing_definition, missing_lemma, planned_module, or external_citation) to an existing formalization plan"),
            make_tool::<FormalizationPlanAttachLookupArgs>("formalization_plan_attach_lookup", "Attach a lean_declaration_lookup result to a plan item, updating its Mathlib coverage status (found/not_found/partial/unknown). A hint attachment, not a re-check — never changes proof status"),
            make_tool::<FormalizationPlanPromoteItemToObligationArgs>("formalization_plan_promote_item_to_obligation", "Link a plan item to an episode_obligation that ALREADY EXISTS (created through a normal Decompose action via episode_step). Records the link only — this tool never creates the obligation itself, so it can never bypass the episode's budget/CAS accounting"),
            make_tool::<MathlibSearchDeclarationsArgs>("mathlib_search_declarations", "Search the REAL pinned Mathlib source tree (issue #25 librarian) for declaration names containing a substring — beyond exact-name lookup, for when the exact name isn't known. A dotted query like \"Nat.factorization\" is matched on its last segment, since results are reported by file-local name only. Returns declaration name, keyword, derived import module, file path, and a signature snippet, with confidence exact_match/nearby_name. Advisory only: a hit can never mark anything proved. Unavailable (empty results, mathlib_available=false) if lean-checker isn't set up"),
            make_tool::<MathlibSearchLocalArtifactsArgs>("mathlib_search_local_artifacts", "Search THIS ChatDB instance's own previously-verified theorem/def names for a substring match — a local usage_example precedent, not a Mathlib-library result"),
            make_tool::<FormalizationPlanAttachLibrarianResultArgs>("formalization_plan_attach_librarian_result", "Attach a mathlib_search_declarations/mathlib_search_local_artifacts result to a formalization plan item, updating its Mathlib coverage status. A hint attachment, not a re-check — never changes proof status"),
        ];
        Ok(ListToolsResult::with_all_items(tools))
    }

    async fn call_tool(
        &self,
        request: CallToolRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<CallToolResult, McpError> {
        let args_map = request.arguments.unwrap_or_default();
        let args_val = serde_json::Value::Object(args_map);

        match request.name.as_ref() {
            "environment_describe" => {
                let action_schema = schemars::schema_for!(TypedAction);
                let res = serde_json::json!({
                    "environment_version": "0.3.4",
                    "protocol_version": "2025-11-25",
                    "supported_roles": ["prover"],
                    "schema_versions": {
                        "observation_schema_version": "1.0",
                        "action_schema_version": "1.0",
                        "reward_policy_version": "1.0"
                    },
                    "lean_gateway": if self.lean_available { "ready" } else { "unavailable" },
                    "lean_environment": self.lean_environment.as_ref().map(|e| serde_json::json!({
                        "descriptor": e.descriptor, "hash": e.hash
                    })),
                    "action_schema": action_schema,
                    "action_examples": [
                        {"type": "solve", "proof_term": "  norm_num"},
                        {"type": "decompose", "sub_lemmas": ["n + 0 = n", "0 + n = n"]},
                        {"type": "submit_module", "module_items": [
                            {"item_kind": "def", "name": "double", "type_signature": "Nat → Nat", "body": "fun n => n + n"}
                        ], "root_theorem": {"name": "root", "statement": "double 2 = 4", "proof_term": "  rfl"}},
                        {"type": "submit_module", "module_items": [
                            {"item_kind": "mutual_group", "members": [
                                {"item_kind": "def", "name": "isEven", "type_signature": "Nat → Bool", "body": "fun n => match n with\n  | 0 => true\n  | (k+1) => isOdd k"},
                                {"item_kind": "def", "name": "isOdd", "type_signature": "Nat → Bool", "body": "fun n => match n with\n  | 0 => false\n  | (k+1) => isEven k"}
                            ]}
                        ], "root_theorem": {"name": "root", "statement": "isEven 4 = true", "proof_term": "  rfl"}},
                        {"type": "give_up"}
                    ],
                    "submit_module_boundary": "The server assembles the Lean file: it owns imports, the ChatDB.P_<problem> namespace, and server set_options. Clients send structured items only — never raw import/namespace/end/set_option lines, and never axiom/opaque/unsafe/instance declarations. Every name is sanitized to a single namespace-local identifier. The root_theorem.statement must canonical-hash to the problem's registered root_statement_hash. Either the whole module passes the kernel and is recorded, or nothing enters the trusted namespace. A `mutual_group` item groups 2+ def/theorem members that must forward-reference each other (e.g. mutually recursive functions) into one server-owned `mutual ... end` block — still never raw Lean from the client.",
                    "prover_loop": "problem_create -> problem_submit_fidelity_review (or unsafe_dev_attestation=true for dev use) -> episode_create -> episode_observe -> attempt_claim -> episode_step(action, expected_revision = action_request.episode_revision) -> repeat observe/claim/step until outcome is set",
                    "epistemic_rules": [
                        "An 'unknown_declaration'/'unknown identifier' result under the active import manifest establishes ONLY that the name didn't resolve under that exact import closure. It does NOT establish that the declaration is absent from the pinned library. Before concluding an API is unavailable, call lean_declaration_lookup — do not infer a global capability limit from one local elaboration failure.",
                        "lean_declaration_lookup defaults to a fast (few-second) check against only the problem's own import manifest, returning 'not_available_under_current_manifest' on failure — that status by itself does not prove absence from the library. Pass deep_check=true (15-40+ seconds, loads the full Mathlib umbrella) to get a conclusive 'not_in_current_import_scope' vs 'unknown_declaration' verdict before concluding a declaration is genuinely unavailable.",
                        "A prior model's proof (from another session, another model, a paper, etc.) is a candidate artifact, not evidence of correctness, until it passes THIS pinned verifier. Do not skip verification because a candidate 'looks complete'."
                    ]
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_create" => {
                let args: ProblemCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                if args.source_problem_text.trim().is_empty() || args.root_formal_statement.trim().is_empty() {
                    return Err(mcp_invalid_params("source_problem_text and root_formal_statement must be non-empty"));
                }

                // The gateway wraps the root statement as `theorem <name> : <statement> := by ...`.
                // A declaration-shaped input would nest to `theorem root_theorem : theorem foo : ...`,
                // which can never elaborate — reject it at the source instead of at solve time.
                let first_word = args.root_formal_statement.trim().split_whitespace().next().unwrap_or("");
                if matches!(first_word, "theorem" | "lemma" | "example" | "def" | "abbrev" | "instance") {
                    return Err(mcp_invalid_params(format!(
                        "root_formal_statement must be a bare proposition (what goes AFTER the ':' in a theorem), not a '{}' declaration — e.g. \"∀ a b : ℕ, Even a → Even b → Even (a + b)\" or \"1 + 1 = 2\"",
                        first_word
                    )));
                }

                let extra_imports = args.problem_imports.unwrap_or_default();
                if extra_imports.len() > 50 {
                    return Err(mcp_invalid_params("problem_imports: at most 50 modules per problem"));
                }
                for m in &extra_imports {
                    if !valid_lean_module_path(m) {
                        return Err(mcp_invalid_params(format!(
                            "problem_imports entry {:?} is not a valid Lean module path — must be dot-separated identifier segments only (letters, digits, underscore), no whitespace, comments, or command syntax",
                            m
                        )));
                    }
                }
                if !extra_imports.is_empty() {
                    self.gateway.validate_import_manifest(&extra_imports)
                        .map_err(|e| mcp_invalid_params(format!("problem_imports rejected — {}", e)))?;
                }
                let mut import_manifest: Vec<String> = BASE_IMPORT_MANIFEST.iter().map(|s| s.to_string()).collect();
                import_manifest.extend(extra_imports);
                let import_manifest_json = serde_json::to_string(&import_manifest).unwrap();
                let import_manifest_hash = canonical_hash(&import_manifest).map_err(mcp_internal_error)?;

                let pv_id = Uuid::new_v4();
                let source_hash = canonical_hash(&args.source_problem_text).map_err(mcp_internal_error)?;
                let root_hash = canonical_hash(&args.root_formal_statement).map_err(mcp_internal_error)?;
                let rendering = args.normalized_root_rendering.unwrap_or_else(|| args.root_formal_statement.clone());
                // The server, not the client, is the source of truth for what Lean
                // environment actually verifies proofs — a client-supplied hash was
                // almost always omitted and silently defaulted to a meaningless
                // placeholder, which made `replay`'s determinism claim untraceable
                // to any specific toolchain/Mathlib pin. Auto-detect; still allow an
                // explicit override for advanced/cross-environment bookkeeping.
                let env_hash = args.environment_hash
                    .or_else(|| self.lean_environment.as_ref().map(|e| e.hash.clone()))
                    .unwrap_or_else(|| "lean-gateway-unavailable".to_string());
                let metadata = args.metadata_json.unwrap_or_else(|| "{}".to_string());
                serde_json::from_str::<serde_json::Value>(&metadata)
                    .map_err(|e| mcp_invalid_params(format!("metadata_json is not valid JSON: {}", e)))?;

                // 'attested' permits proving (episode_create checks for this) but can
                // NEVER reach 'verified' by itself — only problem_submit_fidelity_review
                // can do that, and the DB CHECK on state='COMPLETE' enforces it even if
                // application logic has a bug. No path here ever writes 'verified'.
                let (fidelity_status, state) = if args.unsafe_dev_attestation {
                    ("attested", "PROVING")
                } else {
                    ("unreviewed", "CREATED")
                };
                let fidelity_approval_id = if args.unsafe_dev_attestation { Some(Uuid::new_v4().to_string()) } else { None };

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                tx.execute(
                    "INSERT INTO problem_versions (
                        id, source_problem_text, source_problem_hash, source_metadata_json,
                        root_formal_statement, root_statement_hash, normalized_root_rendering,
                        environment_hash, import_manifest_json, import_manifest_hash,
                        fidelity_status, fidelity_method, fidelity_approval_id,
                        state, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, 'manual', ?12, ?13, ?14)",
                    (
                        pv_id.to_string(), &args.source_problem_text, &source_hash, &metadata,
                        &args.root_formal_statement, &root_hash, &rendering,
                        &env_hash, &import_manifest_json, &import_manifest_hash,
                        fidelity_status, &fidelity_approval_id, state,
                        Utc::now().to_rfc3339(),
                    ),
                ).map_err(rs)?;
                tx.commit().map_err(rs)?;

                let res = serde_json::json!({
                    "problem_version_id": pv_id.to_string(),
                    "fidelity_status": fidelity_status,
                    "state": state,
                    "environment_hash": env_hash,
                    "import_manifest": import_manifest,
                    "import_manifest_hash": import_manifest_hash,
                    // A fidelity reviewer must submit these back unchanged in
                    // problem_submit_fidelity_review — the server recomputes and
                    // compares them independently, so a client can copy these values
                    // rather than needing to reimplement the canonical hash algorithm.
                    "source_problem_hash": source_hash,
                    "root_statement_hash": root_hash,
                    "rendering_hash": canonical_hash(&rendering).map_err(mcp_internal_error)?,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_submit_fidelity_review" => {
                let args: ProblemSubmitFidelityReviewArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let current: Option<(String, String, String)> = tx.query_row(
                    "SELECT source_problem_hash, root_statement_hash, normalized_root_rendering FROM problem_versions WHERE id = ?1",
                    [&args.problem_version_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                ).optional().map_err(rs)?;
                let Some((cur_source_hash, cur_root_hash, cur_rendering)) = current else {
                    return Err(mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id)));
                };
                let cur_rendering_hash = canonical_hash(&cur_rendering).map_err(mcp_internal_error)?;

                // A review can only authorize the EXACT text it reviewed. Recompute
                // independently — never trust the submitted hashes — and reject if
                // the problem has changed (or the review targeted a different one)
                // since the evidence was gathered. This is the anti-staleness check
                // the fix plan calls "hash invalidation."
                if args.source_problem_hash != cur_source_hash
                    || args.root_statement_hash != cur_root_hash
                    || args.rendering_hash != cur_rendering_hash
                {
                    return Err(mcp_invalid_params(
                        "submitted hashes do not match the problem_version's CURRENT source/statement/rendering — \
                         the problem changed since this review's evidence was gathered, or the review targeted a \
                         different problem_version_id. Re-review the current text and resubmit."
                    ));
                }

                let (decision_str, new_status) = match args.decision {
                    FidelityDecision::Verified => ("verified", "verified"),
                    FidelityDecision::Rejected => ("rejected", "rejected"),
                };

                serde_json::from_str::<serde_json::Value>(&args.evidence_json)
                    .map_err(|e| mcp_invalid_params(format!("evidence_json is not valid JSON: {}", e)))?;

                let review_id = Uuid::new_v4().to_string();
                tx.execute(
                    "INSERT INTO problem_fidelity_reviews (
                        id, problem_version_id, source_problem_hash, root_statement_hash, normalized_rendering_hash,
                        decision, method, approver_id, rubric_version, evidence_json, notes, signature, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13)",
                    (
                        &review_id, &args.problem_version_id, &cur_source_hash, &cur_root_hash, &cur_rendering_hash,
                        decision_str, &args.method, &args.approver_id, &args.rubric_version, &args.evidence_json,
                        &args.notes, &args.signature, Utc::now().to_rfc3339(),
                    ),
                ).map_err(rs)?;

                tx.execute(
                    "UPDATE problem_versions SET fidelity_status = ?1, fidelity_method = ?2, fidelity_approval_id = ?3 WHERE id = ?4",
                    (new_status, &args.method, &review_id, &args.problem_version_id),
                ).map_err(rs)?;

                // A verified review is what actually unlocks proving for a problem
                // that was never touched by the dev-bypass path (still 'CREATED').
                if new_status == "verified" {
                    tx.execute(
                        "UPDATE problem_versions SET state = 'PROVING' WHERE id = ?1 AND state = 'CREATED'",
                        [&args.problem_version_id],
                    ).map_err(rs)?;
                }

                // A review landing 'verified' after the root was already
                // kernel-verified (episode outcome kernel_verified, problem state
                // FIDELITY_REVIEW) completes the promotion retroactively — this is
                // the only place 'COMPLETE' / 'certified' get assigned after the fact.
                if new_status == "verified" {
                    let pending_episodes: Vec<String> = {
                        let mut s = tx.prepare(
                            "SELECT id FROM episodes WHERE problem_version_id = ?1 AND outcome = 'kernel_verified'"
                        ).map_err(rs)?;
                        s.query_map([&args.problem_version_id], |row| row.get::<_, String>(0)).map_err(rs)?
                            .collect::<Result<Vec<_>, _>>().map_err(rs)?
                    };
                    for ep_id in &pending_episodes {
                        tx.execute(
                            "UPDATE episodes SET outcome = 'certified' WHERE id = ?1",
                            [ep_id],
                        ).map_err(rs)?;
                    }
                    if !pending_episodes.is_empty() {
                        tx.execute(
                            "UPDATE problem_versions SET state = 'COMPLETE' WHERE id = ?1",
                            [&args.problem_version_id],
                        ).map_err(rs)?;
                    }
                }

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({
                    "problem_version_id": args.problem_version_id,
                    "fidelity_review_id": review_id,
                    "decision": decision_str,
                    "fidelity_status": new_status,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "problem_list" => {
                let args: ProblemListArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                let limit = args.limit.unwrap_or(50).clamp(1, 500);

                let conn = self.conn.lock().await;
                let mut stmt = conn.prepare(
                    "SELECT id, state, fidelity_status, root_formal_statement, created_at,
                            source_problem_hash, root_statement_hash, normalized_root_rendering
                     FROM problem_versions ORDER BY created_at DESC LIMIT ?1"
                ).map_err(rs)?;
                let rows = stmt.query_map([limit], |row| {
                    let rendering: String = row.get(7)?;
                    Ok((serde_json::json!({
                        "problem_version_id": row.get::<_, String>(0)?,
                        "state": row.get::<_, String>(1)?,
                        "fidelity_status": row.get::<_, String>(2)?,
                        "root_formal_statement": row.get::<_, String>(3)?,
                        "created_at": row.get::<_, String>(4)?,
                        "source_problem_hash": row.get::<_, String>(5)?,
                        "root_statement_hash": row.get::<_, String>(6)?,
                    }), rendering))
                }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                let rows: Vec<serde_json::Value> = rows.into_iter().map(|(mut v, rendering): (serde_json::Value, String)| {
                    let rendering_hash = canonical_hash(&rendering).unwrap_or_default();
                    v.as_object_mut().unwrap().insert("rendering_hash".to_string(), serde_json::Value::String(rendering_hash));
                    v
                }).collect();

                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&rows).unwrap())]))
            }
            "episode_create" => {
                let args: EpisodeCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let problem_uuid = Uuid::parse_str(&args.problem_version_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid problem Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let fidelity_status: Option<String> = tx.query_row(
                    "SELECT fidelity_status FROM problem_versions WHERE id = ?1",
                    [problem_uuid.to_string()],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                match fidelity_status.as_deref() {
                    None => return Err(mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id))),
                    Some("verified") | Some("attested") => {}
                    Some(other) => return Err(mcp_invalid_params(format!(
                        "problem_version {} has fidelity_status={}; proving requires 'verified' (call problem_submit_fidelity_review) \
                         or 'attested' (problem_create's unsafe_dev_attestation=true — training-quarantined)",
                        args.problem_version_id, other
                    ))),
                }

                let episode_uuid = lifecycle::episode_create(&tx, problem_uuid).map_err(rs)?;

                if let Some(ms) = args.max_steps {
                    tx.execute("UPDATE episodes SET max_steps = ?1 WHERE id = ?2", (ms, episode_uuid.to_string())).map_err(rs)?;
                }
                if let Some(cb) = args.cost_budget_micros {
                    tx.execute("UPDATE episodes SET cost_budget_micros = ?1 WHERE id = ?2", (cb, episode_uuid.to_string())).map_err(rs)?;
                }

                let next_req_id = lifecycle::advance(&tx, episode_uuid).map_err(rs)?;

                let progress_hash = episode_progress_hash(&tx, &episode_uuid.to_string())?;
                let env_hash = episode_env_hash(&tx, &episode_uuid.to_string()).map_err(rs)?;
                trajectories::record_event(
                    &tx, episode_uuid, "episode_created", "GENESIS", &progress_hash, &env_hash,
                    &serde_json::json!({"problem_version_id": args.problem_version_id, "max_steps": args.max_steps, "cost_budget_micros": args.cost_budget_micros}).to_string(),
                ).map_err(mcp_internal_error)?;

                tx.commit().map_err(rs)?;

                let (state,): (String,) = conn.query_row(
                    "SELECT state FROM episodes WHERE id = ?1",
                    [episode_uuid.to_string()],
                    |row| Ok((row.get(0)?,)),
                ).map_err(rs)?;

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(rs)?)
                } else {
                    None
                };

                let res = serde_json::json!({
                    "episode_id": episode_uuid.to_string(),
                    "state": state,
                    "next_action_request": next_action_request
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_reset" => {
                let args: EpisodeResetArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let old_ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let exists: Option<i64> = tx.query_row(
                    "SELECT 1 FROM episodes WHERE id = ?1", [old_ep_uuid.to_string()], |row| row.get(0)
                ).optional().map_err(rs)?;
                if exists.is_none() {
                    return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id)));
                }

                let new_ep_uuid = lifecycle::episode_reset(&tx, old_ep_uuid).map_err(rs)?;

                let next_req_id = lifecycle::advance(&tx, new_ep_uuid).map_err(rs)?;

                let progress_hash = episode_progress_hash(&tx, &new_ep_uuid.to_string())?;
                let env_hash = episode_env_hash(&tx, &new_ep_uuid.to_string()).map_err(rs)?;
                trajectories::record_event(
                    &tx, new_ep_uuid, "episode_created", "GENESIS", &progress_hash, &env_hash,
                    &serde_json::json!({"reset_from": args.episode_id}).to_string(),
                ).map_err(mcp_internal_error)?;

                tx.commit().map_err(rs)?;

                let (state,): (String,) = conn.query_row(
                    "SELECT state FROM episodes WHERE id = ?1",
                    [new_ep_uuid.to_string()],
                    |row| Ok((row.get(0)?,)),
                ).map_err(rs)?;

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(rs)?)
                } else {
                    None
                };

                let res = serde_json::json!({
                    "episode_id": new_ep_uuid.to_string(),
                    "state": state,
                    "next_action_request": next_action_request
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_observe" => {
                let args: EpisodeObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                attempts::attempt_recover_expired(&tx).map_err(rs)?;
                attempts::request_recover_expired(&tx, ep_uuid).map_err(rs)?;
                // If the only pending request just lapsed, advance() notices there's
                // no live one and mints a fresh one against the same target obligation.
                lifecycle::advance(&tx, ep_uuid).map_err(rs)?;
                tx.commit().map_err(rs)?;

                let active_req_id_str: Option<String> = conn.query_row(
                    "SELECT id FROM action_requests WHERE episode_id = ?1 AND status IN ('pending', 'claimed') ORDER BY created_at DESC LIMIT 1",
                    [args.episode_id.clone()],
                    |row| row.get(0),
                ).optional().map_err(rs)?;

                if let Some(req_id_str) = active_req_id_str {
                    let req_id = Uuid::parse_str(&req_id_str).unwrap();
                    let action_request = query_action_request(&conn, req_id).map_err(rs)?;

                    let obs_json: Option<String> = conn.query_row(
                        "SELECT observation_json FROM action_requests WHERE id = ?1",
                        [req_id_str],
                        |row| row.get(0),
                    ).map_err(rs)?;

                    let observation = obs_json.and_then(|s| serde_json::from_str(&s).ok()).unwrap_or(serde_json::Value::Null);

                    let res = serde_json::json!({
                        "action_request": action_request,
                        "observation": observation
                    });
                    Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
                } else {
                    let episode_exists: Option<String> = conn.query_row(
                        "SELECT state FROM episodes WHERE id = ?1", [args.episode_id.clone()], |row| row.get(0)
                    ).optional().map_err(rs)?;
                    match episode_exists {
                        None => Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id))),
                        Some(state) => Err(mcp_invalid_params(format!("No active request (episode state = {})", state))),
                    }
                }
            }
            "attempt_claim" => {
                let args: AttemptClaimArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;
                let req_uuid = Uuid::parse_str(&args.action_request_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid action_request Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                attempts::attempt_recover_expired(&tx).map_err(rs)?;
                attempts::request_recover_expired(&tx, ep_uuid).map_err(rs)?;

                let ep_state: Option<String> = tx.query_row(
                    "SELECT state FROM episodes WHERE id = ?1", [&args.episode_id], |row| row.get(0)
                ).optional().map_err(rs)?;
                match ep_state.as_deref() {
                    None => return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id))),
                    Some("terminated") | Some("truncated") => return Err(mcp_invalid_params(format!(
                        "episode {} is {} — create a new episode (episode_create) or fork it (episode_reset)",
                        args.episode_id, ep_state.as_deref().unwrap()
                    ))),
                    _ => {}
                }

                let claim = attempts::attempt_claim(&tx, ep_uuid, req_uuid, &args.idempotency_key, args.expected_revision)
                    .map_err(rs)?;

                match claim {
                    Some(c) => {
                        tx.commit().map_err(rs)?;
                        let res = serde_json::json!({
                            "action_attempt_id": c.attempt_id.to_string(),
                            "claim_token": c.claim_token,
                        });
                        Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
                    }
                    None => {
                        // Diagnose exactly why the claim was refused instead of a bare error.
                        let req_info: Option<(String, Option<String>)> = tx.query_row(
                            "SELECT status, expiration_at FROM action_requests WHERE id = ?1 AND episode_id = ?2",
                            (&args.action_request_id, &args.episode_id),
                            |row| Ok((row.get(0)?, row.get(1)?)),
                        ).optional().map_err(rs)?;

                        let key_used: Option<String> = tx.query_row(
                            "SELECT status FROM action_attempts WHERE episode_id = ?1 AND idempotency_key = ?2",
                            (&args.episode_id, &args.idempotency_key),
                            |row| row.get(0),
                        ).optional().map_err(rs)?;

                        let msg = if let Some(attempt_status) = key_used {
                            format!(
                                "idempotency_key '{}' was already used by an attempt now in state '{}' — retry with a fresh idempotency_key",
                                args.idempotency_key, attempt_status
                            )
                        } else {
                            match req_info {
                                None => format!("unknown action_request_id {} for episode {} — call episode_observe for the current request", args.action_request_id, args.episode_id),
                                Some((status, exp)) => match status.as_str() {
                                    "claimed" => "request is currently claimed by another attempt (claims auto-expire ~5 min after issue and are recovered on the next observe/claim) — call episode_observe and retry".to_string(),
                                    "fulfilled" => "request was already fulfilled by a committed step — call episode_observe for the next request".to_string(),
                                    "expired" | "cancelled" => format!(
                                        "action request {}{} — call episode_observe for the current request",
                                        status,
                                        exp.map(|e| format!(" (expired at {})", e)).unwrap_or_default()
                                    ),
                                    other => format!("request is in state '{}' and not claimable — call episode_observe", other),
                                },
                            }
                        };
                        Err(mcp_invalid_params(msg))
                    }
                }
            }
            "episode_step" => {
                let args: EpisodeStepArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!(
                        "Invalid params: {}. `action` must be one of: {{\"type\":\"solve\",\"proof_term\":\"  norm_num\"}} | {{\"type\":\"decompose\",\"sub_lemmas\":[\"...\"]}} | {{\"type\":\"submit_module\",\"module_items\":[{{\"item_kind\":\"def\",\"name\":\"f\",\"type_signature\":\"Nat → Nat\",\"body\":\"fun n => n\"}}],\"root_theorem\":{{\"name\":\"root\",\"statement\":\"<must hash-match registered root>\",\"proof_term\":\"  rfl\"}}}} | {{\"type\":\"give_up\"}} (see environment_describe.action_schema)", e
                    )))?;

                if args.cost_micros < 0 {
                    return Err(mcp_invalid_params("cost_micros must be >= 0"));
                }

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let attempt_uuid = Uuid::parse_str(&args.action_attempt_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid attempt Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;

                // Everything that touches `tx1` lives in this block and the block ends
                // (dropping `tx1`) before any `.await` — a `Transaction` borrows from
                // `Connection`, which is `!Sync` (hence `!Send`), so it must be
                // LEXICALLY out of scope, not merely logically unused, before crossing
                // an await point in an async fn (the generator transform otherwise
                // reserves state for it and the whole future stops being `Send`).
                // `conn` itself is only ever mutably BORROWED by `tx1.transaction()`,
                // never moved, so it's still ours to use/drop once this block ends.
                enum Prepared {
                    Resolved(PostProcessing),
                    NeedsGateway { request: step::GatewayRequest, ctx: step::FinalizeContext },
                }
                let (prepared, target_obligation_id, state_hash_before) = {
                    let tx1 = conn.transaction().map_err(rs)?;
                    attempts::attempt_recover_expired(&tx1).map_err(rs)?;

                    // Capture what this attempt targets before attempt_prepare mutates
                    // state, so the trajectory payload reflects what was actually acted on.
                    let action_request_id: Option<String> = tx1.query_row(
                        "SELECT action_request_id FROM action_attempts WHERE id = ?1",
                        [args.action_attempt_id.clone()],
                        |row| row.get(0),
                    ).optional().map_err(rs)?;
                    let target_obligation_id: Option<String> = match &action_request_id {
                        Some(rid) => tx1.query_row(
                            "SELECT target_obligation_id FROM action_requests WHERE id = ?1",
                            [rid], |row| row.get::<_, Option<String>>(0),
                        ).optional().map_err(rs)?.flatten(),
                        None => None,
                    };
                    let state_hash_before: String = match &action_request_id {
                        Some(rid) => tx1.query_row(
                            "SELECT state_hash_before FROM action_requests WHERE id = ?1",
                            [rid], |row| row.get::<_, Option<String>>(0),
                        ).optional().map_err(rs)?.flatten().unwrap_or_else(|| "GENESIS".to_string()),
                        None => "GENESIS".to_string(),
                    };

                    // Deduct or settle leases if any exist
                    tx1.execute(
                        "UPDATE model_call_leases SET status = 'settled', actual_cost_micros = ?1, settled_at = ?2
                         WHERE episode_id = ?3 AND action_attempt_id = ?4 AND status = 'reserved'",
                        (args.cost_micros, Utc::now().to_rfc3339(), args.episode_id.clone(), args.action_attempt_id.clone()),
                    ).map_err(rs)?;

                    // Two-phase commit: `attempt_prepare` validates the attempt/claim/CAS
                    // and either (a) fully executes a non-Lean action (Decompose / GiveUp /
                    // ExternalResponseRejected / a policy-rejected SubmitModule) within
                    // tx1, or (b) marks the attempt 'executing' and returns exactly what's
                    // needed to call the Lean gateway — WITHOUT calling it. Case (b) is why
                    // this is split: the gateway call (up to 60-120s) must never run while
                    // the DB mutex (`self.conn`) is held, or every other concurrent tool
                    // call on this session blocks on it for the duration.
                    let prep_res = step::attempt_prepare(
                        &tx1, attempt_uuid, args.expected_revision, &args.claim_token, &args.action, args.cost_micros as i128,
                    );

                    let prepared = match prep_res {
                        Err(e) => {
                            let post = run_step_post_processing(
                                &tx1, ep_uuid, &args.episode_id, attempt_uuid, &args.action,
                                Err(e), &target_obligation_id, &state_hash_before,
                            )?;
                            tx1.commit().map_err(rs)?;
                            Prepared::Resolved(post)
                        }
                        Ok(step::PrepOutcome::Done { outcome, .. }) => {
                            let post = run_step_post_processing(
                                &tx1, ep_uuid, &args.episode_id, attempt_uuid, &args.action,
                                Ok(outcome), &target_obligation_id, &state_hash_before,
                            )?;
                            tx1.commit().map_err(rs)?;
                            Prepared::Resolved(post)
                        }
                        Ok(step::PrepOutcome::NeedsGateway { request, ctx }) => {
                            tx1.commit().map_err(rs)?; // commit prepare-only writes (mark-executing, attempt_count)
                            Prepared::NeedsGateway { request, ctx }
                        }
                    };
                    (prepared, target_obligation_id, state_hash_before)
                }; // tx1 fully out of scope here — safe to cross an .await below.

                let post = match prepared {
                    Prepared::Resolved(post) => post,
                    Prepared::NeedsGateway { request, ctx } => {
                        drop(conn); // RELEASE THE LOCK — no other tool call is blocked while Lean runs.

                        let response = match request {
                            step::GatewayRequest::Solve { obl, proof_term, dep_ids, env_hash, import_manifest } => {
                                step::GatewayResponse::Solve(self.gateway.verify_exact(&obl, &proof_term, &dep_ids, &env_hash, &import_manifest))
                            }
                            step::GatewayRequest::SubmitModule { assembled, env_hash } => {
                                step::GatewayResponse::SubmitModule(self.gateway.verify_module(&assembled, &env_hash))
                            }
                        };

                        conn = self.conn.lock().await; // reacquire
                        let post = {
                            let tx2 = conn.transaction().map_err(rs)?;
                            let finalize_res = step::attempt_finalize(&tx2, attempt_uuid, &args.claim_token, args.cost_micros as i128, ctx, response);
                            let post = run_step_post_processing(
                                &tx2, ep_uuid, &args.episode_id, attempt_uuid, &args.action,
                                finalize_res, &target_obligation_id, &state_hash_before,
                            )?;
                            tx2.commit().map_err(rs)?;
                            post
                        }; // tx2 out of scope here too.
                        post
                    }
                };

                let PostProcessing { disposition, accepted, error_msg, outcome_enum, term_reason, trunc_reason, next_req_id } = post;
                let is_terminated = term_reason.is_some();
                let is_truncated = trunc_reason.is_some();

                // Calculate reward. `accepted` doubles as "not a Lean kernel_fail" for
                // Solve/SubmitModule and as a generic accept/reject signal for
                // Decompose/GiveUp — only treat it as a proof-verification result
                // (kernel_pass/kernel_fail reward) for an actual verification action.
                let is_verification_action = matches!(args.action, TypedAction::Solve { .. } | TypedAction::SubmitModule { .. });
                let mut reward_components = Vec::new();
                let policy = RewardPolicy::default_policy();
                if disposition == StepDisposition::Accepted {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::StepPenalty,
                        value_scaled: policy.step_penalty,
                    });
                    if is_verification_action && accepted {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelPass,
                            value_scaled: policy.kernel_pass,
                        });
                    } else if is_verification_action && !is_terminated {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::KernelFail,
                            value_scaled: policy.kernel_fail,
                        });
                    }
                }
                if outcome_enum == Some(EpisodeOutcome::Certified) || outcome_enum == Some(EpisodeOutcome::KernelVerified) {
                    // Real work either way: the prover proved exactly the formal
                    // statement it was given. Composite success (TerminalSuccess) is
                    // reserved for when fidelity is ALSO verified — never award it for
                    // a kernel_verified-but-not-certified outcome, or a prover that
                    // faithfully proved a bad formalization looks identical to one
                    // that solved the real problem.
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::RootKernelVerified,
                        value_scaled: policy.root_kernel_verified,
                    });
                    if outcome_enum == Some(EpisodeOutcome::Certified) {
                        reward_components.push(RewardComponent {
                            id: RewardComponentId::TerminalSuccess,
                            value_scaled: policy.terminal_success,
                        });
                    }
                } else if is_truncated {
                    reward_components.push(RewardComponent {
                        id: RewardComponentId::TruncationPenalty,
                        value_scaled: policy.truncation_penalty,
                    });
                }

                let next_action_request = if let Some(req_id) = next_req_id {
                    Some(query_action_request(&conn, req_id).map_err(rs)?)
                } else {
                    None
                };

                let observation = if let Some(ref req) = next_action_request {
                    let obs_json: Option<String> = conn.query_row(
                        "SELECT observation_json FROM action_requests WHERE id = ?1",
                        [req.id.to_string()],
                        |row| row.get(0),
                    ).optional().map_err(rs)?.flatten();
                    obs_json.and_then(|s| serde_json::from_str(&s).ok()).unwrap_or(serde_json::Value::Null)
                } else {
                    serde_json::Value::Null
                };

                // A rejected verification action (a kernel-failed Solve, or a
                // module refused by policy or the staged kernel) preserves its
                // reason as the obligation's failure_lesson. Surface it directly on
                // the step response so a client gets structured feedback about WHY
                // the draft was rejected without a second observe round-trip — the
                // module trust boundary demands the rejection be legible, not silent.
                let rejection_diagnostic: Option<String> = if is_verification_action
                    && disposition == StepDisposition::Accepted && !accepted {
                    match &target_obligation_id {
                        Some(oid) => conn.query_row(
                            "SELECT failure_lesson FROM episode_obligations WHERE id = ?1",
                            [oid], |row| row.get::<_, Option<String>>(0),
                        ).optional().map_err(rs)?.flatten(),
                        None => None,
                    }
                } else {
                    None
                };

                let res = serde_json::json!({
                    "accepted": accepted,
                    "disposition": disposition,
                    "counts_as_environment_step": disposition == StepDisposition::Accepted,
                    "reward": reward_components,
                    "outcome": outcome_enum,
                    "termination_reason": term_reason,
                    "truncation_reason": trunc_reason,
                    "diagnostics": error_msg,
                    "rejection_diagnostic": rejection_diagnostic,
                    "next_action_request": next_action_request,
                    "observation": observation
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "episode_status" => {
                let args: EpisodeStatusArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let status = conn.query_row(
                    "SELECT state, current_revision, step_count, cost_budget_micros, invalid_action_count, outcome, termination_reason, truncation_reason
                     FROM episodes WHERE id = ?1",
                    [args.episode_id.clone()],
                    |row| {
                        Ok(serde_json::json!({
                            "state": row.get::<_, String>(0)?,
                            "current_revision": row.get::<_, i64>(1)?,
                            "step_count": row.get::<_, i64>(2)?,
                            "cost_budget_micros": row.get::<_, Option<i64>>(3)?,
                            "invalid_action_count": row.get::<_, i64>(4)?,
                            "outcome": row.get::<_, Option<String>>(5)?,
                            "termination_reason": row.get::<_, Option<String>>(6)?,
                            "truncation_reason": row.get::<_, Option<String>>(7)?,
                        }))
                    }
                ).optional().map_err(rs)?;

                match status {
                    Some(s) => Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&s).unwrap())])),
                    None => Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id))),
                }
            }
            "episode_close" => {
                let args: EpisodeCloseArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let current_state: Option<String> = tx.query_row(
                    "SELECT state FROM episodes WHERE id = ?1", [args.episode_id.clone()], |row| row.get(0)
                ).optional().map_err(rs)?;

                let Some(current_state) = current_state else {
                    return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id)));
                };

                if current_state == "terminated" || current_state == "truncated" {
                    tx.commit().map_err(rs)?;
                    let res = serde_json::json!({ "status": "already_closed", "state": current_state });
                    return Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]));
                }

                tx.execute(
                    "UPDATE episodes SET state = 'terminated', outcome = ?1, termination_reason = ?2, completed_at = ?3 WHERE id = ?4",
                    (EpisodeOutcome::GaveUp.to_string(), TerminationReason::HumanCancelled.to_string(), Utc::now().to_rfc3339(), args.episode_id.clone()),
                ).map_err(rs)?;

                let progress_hash = episode_progress_hash(&tx, &args.episode_id)?;
                let env_hash = episode_env_hash(&tx, &args.episode_id).map_err(rs)?;
                trajectories::record_event(
                    &tx, ep_uuid, "episode_terminated", &progress_hash, &progress_hash, &env_hash,
                    &serde_json::json!({"outcome": "gave_up", "termination_reason": "human_cancelled", "reason": args.reason}).to_string(),
                ).map_err(mcp_internal_error)?;

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({ "status": "closed" });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "model_call_reserve" => {
                let args: ModelCallReserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                if args.reserved_cost_micros < 0 {
                    return Err(mcp_invalid_params("reserved_cost_micros must be >= 0"));
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let attempt_exists: Option<i64> = tx.query_row(
                    "SELECT 1 FROM action_attempts WHERE id = ?1 AND episode_id = ?2",
                    (&args.action_attempt_id, &args.episode_id),
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                if attempt_exists.is_none() {
                    return Err(mcp_invalid_params(format!("unknown action_attempt_id {} for episode {}", args.action_attempt_id, args.episode_id)));
                }

                let remaining: Option<i64> = tx.query_row(
                    "SELECT cost_budget_micros FROM episodes WHERE id = ?1", [&args.episode_id], |row| row.get(0)
                ).optional().map_err(rs)?.flatten();
                if let Some(remaining) = remaining {
                    if args.reserved_cost_micros > remaining {
                        return Err(mcp_invalid_params(format!(
                            "budget_denied: reserved_cost_micros {} exceeds remaining budget {}",
                            args.reserved_cost_micros, remaining
                        )));
                    }
                }

                let lease_id = Uuid::new_v4();
                let descriptor = serde_json::json!({
                    "runner_id": args.runner_id,
                    "declared_model": args.declared_model,
                    "max_input_tokens": args.max_input_tokens,
                    "max_output_tokens": args.max_output_tokens,
                });
                let descriptor_json = serde_json::to_string(&descriptor).unwrap();

                tx.execute(
                    "INSERT INTO model_call_leases (
                        id, episode_id, action_attempt_id, model_descriptor_json, reserved_cost_micros, status, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, 'reserved', ?6)",
                    (
                        lease_id.to_string(),
                        args.episode_id.clone(),
                        args.action_attempt_id.clone(),
                        descriptor_json,
                        args.reserved_cost_micros,
                        Utc::now().to_rfc3339(),
                    ),
                ).map_err(rs)?;

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({ "lease_id": lease_id.to_string() });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "model_call_settle" => {
                let args: ModelCallSettleArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                if args.actual_cost_micros < 0 {
                    return Err(mcp_invalid_params("actual_cost_micros must be >= 0"));
                }
                if !matches!(args.status.as_str(), "settled" | "voided") {
                    return Err(mcp_invalid_params("status must be 'settled' or 'voided'"));
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                let lease: Option<(String, String)> = tx.query_row(
                    "SELECT episode_id, status FROM model_call_leases WHERE id = ?1",
                    [args.lease_id.clone()],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                ).optional().map_err(rs)?;

                let Some((episode_id, lease_status)) = lease else {
                    return Err(mcp_invalid_params(format!("unknown lease_id: {}", args.lease_id)));
                };
                if lease_status != "reserved" {
                    return Err(mcp_invalid_params(format!("lease {} is already {}", args.lease_id, lease_status)));
                }

                tx.execute(
                    "UPDATE model_call_leases SET status = ?1, actual_cost_micros = ?2, settled_at = ?3 WHERE id = ?4",
                    (args.status.clone(), args.actual_cost_micros, Utc::now().to_rfc3339(), args.lease_id.clone()),
                ).map_err(rs)?;

                if args.status == "settled" {
                    tx.execute(
                        "UPDATE episodes SET cost_budget_micros = cost_budget_micros - ?1 WHERE id = ?2",
                        (args.actual_cost_micros, &episode_id),
                    ).map_err(rs)?;
                }

                tx.commit().map_err(rs)?;

                let res = serde_json::json!({ "status": args.status });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "trajectory_export" => {
                let args: TrajectoryExportArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let page_size = args.page_size.unwrap_or(50);
                let cursor = args.cursor.unwrap_or(0);

                let conn = self.conn.lock().await;
                let mut stmt = conn.prepare(
                    "SELECT id, event_sequence_number, event_type, event_hash, previous_event_hash,
                            state_hash_before, state_hash_after, lean_environment_hash, payload_json, created_at
                     FROM trajectory_events
                     WHERE episode_id = ?1 AND event_sequence_number >= ?2
                     ORDER BY event_sequence_number ASC LIMIT ?3"
                ).map_err(rs)?;

                let rows = stmt.query_map((args.episode_id.clone(), cursor, page_size), |row| {
                    Ok(serde_json::json!({
                        "id": row.get::<_, i64>(0)?,
                        "event_sequence_number": row.get::<_, i64>(1)?,
                        "event_type": row.get::<_, String>(2)?,
                        "event_hash": row.get::<_, String>(3)?,
                        "previous_event_hash": row.get::<_, String>(4)?,
                        "state_hash_before": row.get::<_, String>(5)?,
                        "state_hash_after": row.get::<_, String>(6)?,
                        "lean_environment_hash": row.get::<_, String>(7)?,
                        "payload": serde_json::from_str::<serde_json::Value>(&row.get::<_, String>(8)?).unwrap_or(serde_json::Value::Null),
                        "created_at": row.get::<_, String>(9)?,
                    }))
                }).map_err(rs)?
                .collect::<Result<Vec<_>, _>>()
                .map_err(rs)?;

                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&rows).unwrap())]))
            }
            "episode_replay" => {
                let args: EpisodeReplayArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let ep_uuid = Uuid::parse_str(&args.episode_id)
                    .map_err(|e| mcp_invalid_params(format!("Invalid episode Uuid: {}", e)))?;

                let conn = self.conn.lock().await;
                let audit_ok = trajectories::audit_trajectory(&conn, ep_uuid).map_err(mcp_internal_error)?;

                let replay_status = trajectories::replay_trajectory(&conn, ep_uuid, &*self.gateway)
                    .map_err(mcp_internal_error)?;

                let events_replayed = match &replay_status {
                    trajectories::ReplayStatus::Empty => 0,
                    trajectories::ReplayStatus::Matched(n) => *n,
                };

                let res = serde_json::json!({
                    "audit_passed": audit_ok,
                    "events_replayed": events_replayed,
                    "replay_status": replay_status.to_string(),
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "proof_export" => {
                let args: ProofExportArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                let format = args.format.as_deref().unwrap_or("markdown");
                if !matches!(format, "markdown" | "lean") {
                    return Err(mcp_invalid_params("format must be \"markdown\" or \"lean\""));
                }
                let conn = self.conn.lock().await;
                let doc = render_proof_export(&conn, &args.episode_id, format)?;
                Ok(CallToolResult::success(vec![Content::text(doc)]))
            }
            "lean_declaration_lookup" => {
                let args: LeanDeclarationLookupArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.names.is_empty() {
                    return Err(mcp_invalid_params("names must be non-empty"));
                }
                if args.names.len() > 50 {
                    return Err(mcp_invalid_params("names: at most 50 declarations per call"));
                }
                for n in &args.names {
                    if !valid_lean_declaration_name(n) {
                        return Err(mcp_invalid_params(format!(
                            "name {:?} is not a valid Lean declaration name — no whitespace, comments, or command syntax",
                            n
                        )));
                    }
                }

                let (import_manifest_json, import_manifest_hash, env_hash): (String, String, String) = {
                    // Scoped so the DB mutex is released BEFORE the potentially
                    // 15-40+ second blocking Lean invocation below — holding it
                    // that long would stall every other concurrent tool call
                    // (episode_observe, episode_status, ...) on the same session.
                    let conn = self.conn.lock().await;
                    conn.query_row(
                        "SELECT import_manifest_json, import_manifest_hash, environment_hash FROM problem_versions WHERE id = ?1",
                        [&args.problem_version_id],
                        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                    ).map_err(|e| if matches!(e, rusqlite::Error::QueryReturnedNoRows) {
                        mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id))
                    } else {
                        rs(e)
                    })?
                };
                let import_manifest: Vec<String> = serde_json::from_str(&import_manifest_json).unwrap_or_default();

                let results = self.gateway.lookup_declarations(&args.names, &import_manifest, args.deep_check)
                    .map_err(mcp_internal_error)?;

                let res = serde_json::json!({
                    "environment_hash": env_hash,
                    "import_manifest_hash": import_manifest_hash,
                    "results": results.into_iter().map(|r| serde_json::json!({
                        "query": r.query,
                        "status": r.status.to_string(),
                        "diagnostics": r.diagnostics,
                    })).collect::<Vec<_>>(),
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "proof_pattern_create" => {
                let args: ProofPatternCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let confidence_str = match args.confidence {
                    PatternConfidence::Seed => "seed",
                    PatternConfidence::Mined => "mined",
                    PatternConfidence::Confirmed => "confirmed",
                };
                let applicable_when_json = serde_json::to_string(&args.applicable_when).unwrap();
                let avoid_when_json = serde_json::to_string(&args.avoid_when).unwrap();
                let source_attempt_ids_json = serde_json::to_string(&args.source_attempt_ids).unwrap();

                let conn = self.conn.lock().await;
                let pattern_id = Uuid::new_v4().to_string();
                let created_at = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO proof_patterns (
                        id, pattern_key, title, failure_signature, recommended_repair,
                        applicable_when_json, avoid_when_json, source_episode_id,
                        source_attempt_ids_json, confidence, status, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, 'active', ?11)",
                    (
                        &pattern_id, &args.pattern_key, &args.title, &args.failure_signature,
                        &args.recommended_repair, &applicable_when_json, &avoid_when_json,
                        &args.source_episode_id, &source_attempt_ids_json, confidence_str, &created_at,
                    ),
                ).map_err(|e| if matches!(&e, rusqlite::Error::SqliteFailure(err, _) if err.extended_code == rusqlite::ffi::SQLITE_CONSTRAINT_UNIQUE) {
                    mcp_invalid_params(format!("pattern_key {:?} already exists — patterns are not overwritten by a second create call", args.pattern_key))
                } else {
                    rs(e)
                })?;

                let res = serde_json::json!({
                    "pattern_id": pattern_id,
                    "pattern_key": args.pattern_key,
                    "status": "active",
                    "created_at": created_at,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "proof_pattern_search" => {
                let args: ProofPatternSearchArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                let limit = args.limit.unwrap_or(50).clamp(1, 500);

                let conn = self.conn.lock().await;
                let rows: Vec<(String, String, String, String, String, String, String, String, Option<String>, String)> = if let Some(q) = args.query.filter(|q| !q.trim().is_empty()) {
                    let like = format!("%{}%", q);
                    let mut stmt = conn.prepare(
                        "SELECT id, pattern_key, title, failure_signature, recommended_repair,
                                applicable_when_json, avoid_when_json, confidence, source_episode_id, created_at
                         FROM proof_patterns
                         WHERE status = 'active' AND (
                             pattern_key LIKE ?1 ESCAPE '\\' OR title LIKE ?1 ESCAPE '\\' OR
                             failure_signature LIKE ?1 ESCAPE '\\' OR recommended_repair LIKE ?1 ESCAPE '\\'
                         )
                         ORDER BY title ASC LIMIT ?2"
                    ).map_err(rs)?;
                    stmt.query_map((like, limit), |row| Ok((
                        row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?,
                        row.get(5)?, row.get(6)?, row.get(7)?, row.get(8)?, row.get(9)?,
                    ))).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?
                } else {
                    let mut stmt = conn.prepare(
                        "SELECT id, pattern_key, title, failure_signature, recommended_repair,
                                applicable_when_json, avoid_when_json, confidence, source_episode_id, created_at
                         FROM proof_patterns WHERE status = 'active' ORDER BY title ASC LIMIT ?1"
                    ).map_err(rs)?;
                    stmt.query_map([limit], |row| Ok((
                        row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?,
                        row.get(5)?, row.get(6)?, row.get(7)?, row.get(8)?, row.get(9)?,
                    ))).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?
                };

                let patterns: Vec<serde_json::Value> = rows.into_iter().map(|(id, key, title, sig, repair, aw_json, avw_json, confidence, source_ep, created_at)| {
                    serde_json::json!({
                        "pattern_id": id,
                        "pattern_key": key,
                        "title": title,
                        "failure_signature": sig,
                        "recommended_repair": repair,
                        "applicable_when": serde_json::from_str::<serde_json::Value>(&aw_json).unwrap_or(serde_json::Value::Array(vec![])),
                        "avoid_when": serde_json::from_str::<serde_json::Value>(&avw_json).unwrap_or(serde_json::Value::Array(vec![])),
                        "confidence": confidence,
                        "source_episode_id": source_ep,
                        "created_at": created_at,
                    })
                }).collect();

                let res = serde_json::json!({ "patterns": patterns });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "proof_pattern_record_application" => {
                let args: ProofPatternRecordApplicationArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let role_str = match args.role {
                    PatternApplicationRole::FailedExample => "failed_example",
                    PatternApplicationRole::RepairExample => "repair_example",
                    PatternApplicationRole::SuggestedHint => "suggested_hint",
                };

                let conn = self.conn.lock().await;
                let pattern_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM proof_patterns WHERE id = ?1", [&args.pattern_id], |row| row.get(0),
                ).map_err(rs)?;
                if pattern_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown pattern_id: {}", args.pattern_id)));
                }
                let episode_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM episodes WHERE id = ?1", [&args.episode_id], |row| row.get(0),
                ).map_err(rs)?;
                if episode_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id)));
                }

                // Pure insert — this is the entire operation. Deliberately never
                // touches episodes/episode_obligations/action_attempts: a pattern
                // application is advisory metadata, not a proof-status change.
                let application_id = Uuid::new_v4().to_string();
                let created_at = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO proof_pattern_applications (
                        id, pattern_id, episode_id, action_attempt_id, role, notes, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
                    (&application_id, &args.pattern_id, &args.episode_id, &args.action_attempt_id, role_str, &args.notes, &created_at),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "application_id": application_id,
                    "pattern_id": args.pattern_id,
                    "episode_id": args.episode_id,
                    "role": role_str,
                    "created_at": created_at,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "draft_create" => {
                let args: DraftCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let pv_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM problem_versions WHERE id = ?1", [&args.problem_version_id], |row| row.get(0),
                ).map_err(rs)?;
                if pv_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id)));
                }
                if let Some(ep_id) = &args.episode_id {
                    let ep_pv_id: Option<String> = conn.query_row(
                        "SELECT problem_version_id FROM episodes WHERE id = ?1", [ep_id], |row| row.get(0),
                    ).optional().map_err(rs)?;
                    let Some(ep_pv_id) = ep_pv_id else {
                        return Err(mcp_invalid_params(format!("unknown episode_id: {}", ep_id)));
                    };
                    if ep_pv_id != args.problem_version_id {
                        return Err(mcp_invalid_params(format!("episode_id {} belongs to a different problem_version", ep_id)));
                    }
                }

                let draft_id = Uuid::new_v4().to_string();
                let content_hash = canonical_hash(&args.content).map_err(mcp_internal_error)?;
                let created_at = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO drafts (id, problem_version_id, episode_id, content, content_hash, author, created_at)
                     VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
                    (&draft_id, &args.problem_version_id, &args.episode_id, &args.content, &content_hash, &args.author, &created_at),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "draft_id": draft_id,
                    "content_hash": content_hash,
                    "created_at": created_at,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "draft_observe" => {
                let args: DraftObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let draft: Option<(String, Option<String>, String, String, String, String)> = conn.query_row(
                    "SELECT problem_version_id, episode_id, content, content_hash, author, created_at FROM drafts WHERE id = ?1",
                    [&args.draft_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?)),
                ).optional().map_err(rs)?;
                let Some((pv_id, ep_id, content, content_hash, author, created_at)) = draft else {
                    return Err(mcp_invalid_params(format!("unknown draft_id: {}", args.draft_id)));
                };

                let mut stmt = conn.prepare(
                    "SELECT id, move_order, move_kind, description, promoted_plan_item_id FROM draft_moves WHERE draft_id = ?1 ORDER BY move_order ASC"
                ).map_err(rs)?;
                let moves: Vec<serde_json::Value> = stmt.query_map([&args.draft_id], |row| {
                    Ok(serde_json::json!({
                        "move_id": row.get::<_, String>(0)?,
                        "move_order": row.get::<_, i64>(1)?,
                        "move_kind": row.get::<_, String>(2)?,
                        "description": row.get::<_, String>(3)?,
                        "promoted_plan_item_id": row.get::<_, Option<String>>(4)?,
                    }))
                }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;

                let res = serde_json::json!({
                    "draft_id": args.draft_id,
                    "problem_version_id": pv_id,
                    "episode_id": ep_id,
                    "content": content,
                    "content_hash": content_hash,
                    "author": author,
                    "created_at": created_at,
                    "moves": moves,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "draft_extract_moves" => {
                let args: DraftExtractMovesArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.moves.is_empty() {
                    return Err(mcp_invalid_params("moves must be non-empty"));
                }

                let mut conn = self.conn.lock().await;
                let draft_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM drafts WHERE id = ?1", [&args.draft_id], |row| row.get(0),
                ).map_err(rs)?;
                if draft_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown draft_id: {}", args.draft_id)));
                }

                let tx = conn.transaction().map_err(rs)?;
                let next_order: i64 = tx.query_row(
                    "SELECT COALESCE(MAX(move_order), -1) + 1 FROM draft_moves WHERE draft_id = ?1", [&args.draft_id], |row| row.get(0),
                ).map_err(rs)?;

                let mut created_move_ids = Vec::new();
                let created_at = Utc::now().to_rfc3339();
                for (i, m) in args.moves.iter().enumerate() {
                    let move_kind_str = match m.move_kind {
                        DraftMoveKind::Construction => "construction",
                        DraftMoveKind::AuxiliaryLemma => "auxiliary_lemma",
                        DraftMoveKind::CaseSplit => "case_split",
                        DraftMoveKind::Induction => "induction",
                        DraftMoveKind::Reduction => "reduction",
                        DraftMoveKind::Bijection => "bijection",
                        DraftMoveKind::CounterexampleSearch => "counterexample_search",
                        DraftMoveKind::AsymptoticStep => "asymptotic_step",
                        DraftMoveKind::ExternalCitation => "external_citation",
                        DraftMoveKind::Unknown => "unknown",
                    };
                    let move_id = Uuid::new_v4().to_string();
                    tx.execute(
                        "INSERT INTO draft_moves (id, draft_id, move_order, move_kind, description, promoted_plan_item_id, created_at)
                         VALUES (?1, ?2, ?3, ?4, ?5, NULL, ?6)",
                        (&move_id, &args.draft_id, next_order + i as i64, move_kind_str, &m.description, &created_at),
                    ).map_err(rs)?;
                    created_move_ids.push(move_id);
                }
                tx.commit().map_err(rs)?;

                let res = serde_json::json!({
                    "draft_id": args.draft_id,
                    "created_move_ids": created_move_ids,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "formalization_plan_create" => {
                let args: FormalizationPlanCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let pv_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM problem_versions WHERE id = ?1", [&args.problem_version_id], |row| row.get(0),
                ).map_err(rs)?;
                if pv_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown problem_version_id: {}", args.problem_version_id)));
                }
                if let Some(draft_id) = &args.source_draft_id {
                    let draft_pv_id: Option<String> = conn.query_row(
                        "SELECT problem_version_id FROM drafts WHERE id = ?1", [draft_id], |row| row.get(0),
                    ).optional().map_err(rs)?;
                    let Some(draft_pv_id) = draft_pv_id else {
                        return Err(mcp_invalid_params(format!("unknown source_draft_id: {}", draft_id)));
                    };
                    if draft_pv_id != args.problem_version_id {
                        return Err(mcp_invalid_params(format!("source_draft_id {} belongs to a different problem_version", draft_id)));
                    }
                }
                // Self-review finding: the same draft_move_id appearing twice in
                // one call would pass per-move validation (each check sees the
                // not-yet-committed state) and then get promoted into TWO
                // separate plan items, silently orphaning the first — reject the
                // whole batch up front instead.
                {
                    let mut seen = std::collections::HashSet::new();
                    for seed in &args.seed_items_from_draft_moves {
                        if !seen.insert(&seed.draft_move_id) {
                            return Err(mcp_invalid_params(format!("draft_move_id {} appears more than once in seed_items_from_draft_moves", seed.draft_move_id)));
                        }
                    }
                }
                // Every seed move validated BEFORE any row is written, so a bad
                // move in the batch never leaves a partially-seeded plan behind.
                for seed in &args.seed_items_from_draft_moves {
                    let owner: Option<(String, Option<String>)> = conn.query_row(
                        "SELECT draft_id, promoted_plan_item_id FROM draft_moves WHERE id = ?1",
                        [&seed.draft_move_id],
                        |row| Ok((row.get(0)?, row.get(1)?)),
                    ).optional().map_err(rs)?;
                    let Some((owning_draft_id, already_promoted)) = owner else {
                        return Err(mcp_invalid_params(format!("unknown draft_move_id: {}", seed.draft_move_id)));
                    };
                    if Some(&owning_draft_id) != args.source_draft_id.as_ref() {
                        return Err(mcp_invalid_params(format!("draft_move {} does not belong to source_draft_id", seed.draft_move_id)));
                    }
                    if already_promoted.is_some() {
                        return Err(mcp_invalid_params(format!("draft_move {} was already promoted into a plan item", seed.draft_move_id)));
                    }
                }

                let tx = conn.transaction().map_err(rs)?;
                let plan_id = Uuid::new_v4().to_string();
                let risk_flags_json = serde_json::to_string(&args.risk_flags).unwrap();
                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "INSERT INTO formalization_plans (id, problem_version_id, source_draft_id, title, status, risk_flags_json, created_at, updated_at)
                     VALUES (?1, ?2, ?3, ?4, 'draft', ?5, ?6, ?6)",
                    (&plan_id, &args.problem_version_id, &args.source_draft_id, &args.title, &risk_flags_json, &now),
                ).map_err(rs)?;

                let mut created_item_ids = Vec::new();
                for (i, seed) in args.seed_items_from_draft_moves.iter().enumerate() {
                    let description: String = tx.query_row(
                        "SELECT description FROM draft_moves WHERE id = ?1", [&seed.draft_move_id], |row| row.get(0),
                    ).map_err(rs)?;
                    let item_id = Uuid::new_v4().to_string();
                    let kind_str = plan_item_kind_str(&seed.kind);
                    tx.execute(
                        "INSERT INTO formalization_plan_items (
                            id, plan_id, item_order, kind, description, mathlib_coverage_status,
                            mathlib_candidate_names_json, lookup_result_json, promoted_obligation_id, status, created_at
                        ) VALUES (?1, ?2, ?3, ?4, ?5, 'unknown', '[]', NULL, NULL, 'open', ?6)",
                        (&item_id, &plan_id, i as i64, kind_str, &description, &now),
                    ).map_err(rs)?;
                    tx.execute(
                        "UPDATE draft_moves SET promoted_plan_item_id = ?1 WHERE id = ?2",
                        (&item_id, &seed.draft_move_id),
                    ).map_err(rs)?;
                    created_item_ids.push(item_id);
                }
                tx.commit().map_err(rs)?;

                let res = serde_json::json!({
                    "plan_id": plan_id,
                    "status": "draft",
                    "seeded_item_ids": created_item_ids,
                    "created_at": now,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "formalization_plan_observe" => {
                let args: FormalizationPlanObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let plan: Option<(String, Option<String>, String, String, String, String, String)> = conn.query_row(
                    "SELECT problem_version_id, source_draft_id, title, status, risk_flags_json, created_at, updated_at
                     FROM formalization_plans WHERE id = ?1",
                    [&args.plan_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?, row.get(6)?)),
                ).optional().map_err(rs)?;
                let Some((pv_id, source_draft_id, title, status, risk_flags_json, created_at, updated_at)) = plan else {
                    return Err(mcp_invalid_params(format!("unknown plan_id: {}", args.plan_id)));
                };

                let mut stmt = conn.prepare(
                    "SELECT id, item_order, kind, description, mathlib_coverage_status, mathlib_candidate_names_json,
                            lookup_result_json, promoted_obligation_id, status
                     FROM formalization_plan_items WHERE plan_id = ?1 ORDER BY item_order ASC"
                ).map_err(rs)?;
                let items: Vec<serde_json::Value> = stmt.query_map([&args.plan_id], |row| {
                    let lookup_result_json: Option<String> = row.get(6)?;
                    Ok(serde_json::json!({
                        "plan_item_id": row.get::<_, String>(0)?,
                        "item_order": row.get::<_, i64>(1)?,
                        "kind": row.get::<_, String>(2)?,
                        "description": row.get::<_, String>(3)?,
                        "mathlib_coverage_status": row.get::<_, String>(4)?,
                        "mathlib_candidate_names": serde_json::from_str::<serde_json::Value>(&row.get::<_, String>(5)?).unwrap_or(serde_json::Value::Array(vec![])),
                        "lookup_result": lookup_result_json.and_then(|s| serde_json::from_str::<serde_json::Value>(&s).ok()),
                        "promoted_obligation_id": row.get::<_, Option<String>>(7)?,
                        "status": row.get::<_, String>(8)?,
                    }))
                }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;

                let res = serde_json::json!({
                    "plan_id": args.plan_id,
                    "problem_version_id": pv_id,
                    "source_draft_id": source_draft_id,
                    "title": title,
                    "status": status,
                    "risk_flags": serde_json::from_str::<serde_json::Value>(&risk_flags_json).unwrap_or(serde_json::Value::Array(vec![])),
                    "created_at": created_at,
                    "updated_at": updated_at,
                    "items": items,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "formalization_plan_update" => {
                let args: FormalizationPlanUpdateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let current: Option<(String, String, String)> = conn.query_row(
                    "SELECT title, status, risk_flags_json FROM formalization_plans WHERE id = ?1",
                    [&args.plan_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                ).optional().map_err(rs)?;
                let Some((cur_title, cur_status, cur_risk_flags_json)) = current else {
                    return Err(mcp_invalid_params(format!("unknown plan_id: {}", args.plan_id)));
                };

                let new_title = args.title.unwrap_or(cur_title);
                let new_status = match args.status {
                    Some(PlanStatus::Draft) => "draft".to_string(),
                    Some(PlanStatus::Active) => "active".to_string(),
                    Some(PlanStatus::Completed) => "completed".to_string(),
                    Some(PlanStatus::Abandoned) => "abandoned".to_string(),
                    None => cur_status,
                };
                let new_risk_flags_json = match args.risk_flags {
                    Some(flags) => serde_json::to_string(&flags).unwrap(),
                    None => cur_risk_flags_json,
                };
                let now = Utc::now().to_rfc3339();

                conn.execute(
                    "UPDATE formalization_plans SET title = ?1, status = ?2, risk_flags_json = ?3, updated_at = ?4 WHERE id = ?5",
                    (&new_title, &new_status, &new_risk_flags_json, &now, &args.plan_id),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "plan_id": args.plan_id,
                    "title": new_title,
                    "status": new_status,
                    "updated_at": now,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "formalization_plan_add_item" => {
                let args: FormalizationPlanAddItemArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let plan_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM formalization_plans WHERE id = ?1", [&args.plan_id], |row| row.get(0),
                ).map_err(rs)?;
                if plan_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown plan_id: {}", args.plan_id)));
                }

                let next_order: i64 = conn.query_row(
                    "SELECT COALESCE(MAX(item_order), -1) + 1 FROM formalization_plan_items WHERE plan_id = ?1", [&args.plan_id], |row| row.get(0),
                ).map_err(rs)?;
                let kind_str = plan_item_kind_str(&args.kind);
                let candidate_names_json = serde_json::to_string(&args.mathlib_candidate_names).unwrap();
                let item_id = Uuid::new_v4().to_string();
                let created_at = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO formalization_plan_items (
                        id, plan_id, item_order, kind, description, mathlib_coverage_status,
                        mathlib_candidate_names_json, lookup_result_json, promoted_obligation_id, status, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, 'unknown', ?6, NULL, NULL, 'open', ?7)",
                    (&item_id, &args.plan_id, next_order, kind_str, &args.description, &candidate_names_json, &created_at),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "plan_item_id": item_id,
                    "item_order": next_order,
                    "kind": kind_str,
                    "created_at": created_at,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "formalization_plan_attach_lookup" => {
                let args: FormalizationPlanAttachLookupArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let item_status: Option<String> = conn.query_row(
                    "SELECT status FROM formalization_plan_items WHERE id = ?1", [&args.plan_item_id], |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(item_status) = item_status else {
                    return Err(mcp_invalid_params(format!("unknown plan_item_id: {}", args.plan_item_id)));
                };
                if item_status != "open" {
                    return Err(mcp_invalid_params(format!("plan_item {} is not open (status={}) — cannot attach a lookup to a promoted/dropped item", args.plan_item_id, item_status)));
                }

                // Mirrors lean_declaration_lookup's status vocabulary: a hint
                // mapping, not a re-check — the raw status/diagnostics are
                // stored verbatim too, in lookup_result_json.
                let coverage_status = match args.lookup_status.as_str() {
                    "available" => "found",
                    "unknown_declaration" => "not_found",
                    "not_available_under_current_manifest" | "not_in_current_import_scope" => "partial",
                    _ => "unknown",
                };
                let lookup_result_json = serde_json::json!({
                    "lookup_status": args.lookup_status,
                    "matched_name": args.matched_name,
                    "diagnostics": args.diagnostics,
                }).to_string();

                conn.execute(
                    "UPDATE formalization_plan_items SET mathlib_coverage_status = ?1, lookup_result_json = ?2 WHERE id = ?3",
                    (coverage_status, &lookup_result_json, &args.plan_item_id),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "plan_item_id": args.plan_item_id,
                    "mathlib_coverage_status": coverage_status,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "formalization_plan_promote_item_to_obligation" => {
                let args: FormalizationPlanPromoteItemToObligationArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let item_status: Option<String> = conn.query_row(
                    "SELECT status FROM formalization_plan_items WHERE id = ?1", [&args.plan_item_id], |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(item_status) = item_status else {
                    return Err(mcp_invalid_params(format!("unknown plan_item_id: {}", args.plan_item_id)));
                };
                if item_status != "open" {
                    return Err(mcp_invalid_params(format!("plan_item {} is not open (status={}) — already promoted or dropped", args.plan_item_id, item_status)));
                }
                // The obligation must be real (created through a normal
                // Decompose action via episode_step) and belong to the given
                // episode — this tool only records the link, never creates it.
                let obligation_episode: Option<String> = conn.query_row(
                    "SELECT episode_id FROM episode_obligations WHERE id = ?1", [&args.obligation_id], |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(obligation_episode) = obligation_episode else {
                    return Err(mcp_invalid_params(format!("unknown obligation_id: {}", args.obligation_id)));
                };
                if obligation_episode != args.episode_id {
                    return Err(mcp_invalid_params(format!("obligation {} does not belong to episode {}", args.obligation_id, args.episode_id)));
                }

                // Self-review finding: a partial UNIQUE index on
                // promoted_obligation_id (schema_v1.rs) stops two plan items
                // from both claiming the same real obligation — enforced at
                // the DB layer, not just by this handler's own logic.
                conn.execute(
                    "UPDATE formalization_plan_items SET status = 'promoted', promoted_obligation_id = ?1 WHERE id = ?2",
                    (&args.obligation_id, &args.plan_item_id),
                ).map_err(|e| if matches!(&e, rusqlite::Error::SqliteFailure(err, _) if err.extended_code == rusqlite::ffi::SQLITE_CONSTRAINT_UNIQUE) {
                    mcp_invalid_params(format!("obligation_id {} is already linked to a different plan item", args.obligation_id))
                } else {
                    rs(e)
                })?;

                let res = serde_json::json!({
                    "plan_item_id": args.plan_item_id,
                    "obligation_id": args.obligation_id,
                    "status": "promoted",
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "mathlib_search_declarations" => {
                let args: MathlibSearchDeclarationsArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.query.trim().is_empty() {
                    return Err(mcp_invalid_params("query must be non-empty"));
                }
                let limit = args.limit.unwrap_or(20).clamp(1, 200) as usize;

                // Pure filesystem scan — no DB lock held, matching this
                // codebase's convention of not holding the connection Mutex
                // during a slow (here: filesystem-bound, not Lean-bound)
                // operation other concurrent tool calls shouldn't stall on.
                let Some(mathlib_dir) = mathlib_source_dir(&self.lean_project_path) else {
                    let res = serde_json::json!({
                        "mathlib_available": false,
                        "hits": [],
                    });
                    return Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]));
                };
                // Found via real end-to-end testing (playtest.rs against the
                // actual Mathlib source): scanned names are file-local only
                // (this tool's documented namespace-resolution limitation),
                // so a natural dotted query like "Nat.factorization" — the
                // form a declaration is actually REFERENCED by, not how it's
                // WRITTEN in source — would otherwise match nothing at all.
                // Strip any dotted prefix and search on the last segment.
                // Self-review finding: a trailing-dot query (e.g. "Nat.")
                // would otherwise strip to an EMPTY string, which then
                // matches every declaration name — an unintended
                // match-everything scan. Fall back to the original query
                // whenever the stripped segment is empty.
                let bare_query = args.query.rsplit('.').next()
                    .filter(|s| !s.is_empty())
                    .unwrap_or(&args.query);
                let hits = scan_mathlib_declarations(&mathlib_dir, bare_query, limit);
                let res = serde_json::json!({
                    "mathlib_available": true,
                    "hits": hits.into_iter().map(|h| serde_json::json!({
                        "declaration_name": h.declaration_name,
                        "keyword": h.keyword,
                        "import_module": h.import_module,
                        "file_relative_path": h.file_relative_path,
                        "signature_snippet": h.signature_snippet,
                        "confidence": h.confidence,
                    })).collect::<Vec<_>>(),
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "mathlib_search_local_artifacts" => {
                let args: MathlibSearchLocalArtifactsArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.query.trim().is_empty() {
                    return Err(mcp_invalid_params("query must be non-empty"));
                }
                let limit = args.limit.unwrap_or(20).clamp(1, 200);
                let like = format!("%{}%", args.query);

                let conn = self.conn.lock().await;
                let mut lstmt = conn.prepare(
                    "SELECT theorem_name FROM episode_verified_lemmas WHERE theorem_name LIKE ?1 ORDER BY verified_at DESC LIMIT ?2"
                ).map_err(rs)?;
                let lemma_hits: Vec<String> = lstmt.query_map((&like, limit), |row| row.get(0))
                    .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                let mut mstmt = conn.prepare(
                    "SELECT lean_name FROM episode_verified_module_items WHERE lean_name LIKE ?1 ORDER BY id DESC LIMIT ?2"
                ).map_err(rs)?;
                let module_hits: Vec<String> = mstmt.query_map((&like, limit), |row| row.get(0))
                    .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;

                let mut names: Vec<String> = lemma_hits.into_iter().chain(module_hits).collect();
                names.sort();
                names.dedup();
                names.truncate(limit as usize);

                let res = serde_json::json!({
                    "hits": names.into_iter().map(|name| serde_json::json!({
                        "declaration_name": name,
                        "confidence": "usage_example",
                    })).collect::<Vec<_>>(),
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "formalization_plan_attach_librarian_result" => {
                let args: FormalizationPlanAttachLibrarianResultArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let row: Option<(String, String)> = conn.query_row(
                    "SELECT status, mathlib_candidate_names_json FROM formalization_plan_items WHERE id = ?1",
                    [&args.plan_item_id],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                ).optional().map_err(rs)?;
                let Some((item_status, candidate_names_json)) = row else {
                    return Err(mcp_invalid_params(format!("unknown plan_item_id: {}", args.plan_item_id)));
                };
                if item_status != "open" {
                    return Err(mcp_invalid_params(format!("plan_item {} is not open (status={}) — cannot attach a librarian result to a promoted/dropped item", args.plan_item_id, item_status)));
                }

                let confidence_str = match args.confidence {
                    LibrarianConfidence::ExactMatch => "exact_match",
                    LibrarianConfidence::NearbyName => "nearby_name",
                    LibrarianConfidence::TypeMatch => "type_match",
                    LibrarianConfidence::UsageExample => "usage_example",
                    LibrarianConfidence::Unknown => "unknown",
                };
                // Same vocabulary formalization_plan_attach_lookup writes into
                // mathlib_coverage_status, so a plan item's coverage reads
                // consistently regardless of which tool populated it.
                let coverage_status = match args.confidence {
                    LibrarianConfidence::ExactMatch => "found",
                    LibrarianConfidence::NearbyName | LibrarianConfidence::TypeMatch | LibrarianConfidence::UsageExample => "partial",
                    LibrarianConfidence::Unknown => "unknown",
                };

                // Accumulate candidate names across multiple attached results
                // (deduped) rather than overwriting — a plan item can
                // reasonably collect several librarian suggestions before one
                // is chosen. The full latest result (confidence/import/snippet)
                // still overwrites lookup_result_json — see the doc comment on
                // formalization_plan_attach_lookup for the same "latest wins"
                // convention on that field.
                let mut candidate_names: Vec<String> = serde_json::from_str(&candidate_names_json).unwrap_or_default();
                if !candidate_names.contains(&args.declaration_name) {
                    candidate_names.push(args.declaration_name.clone());
                }
                let candidate_names_json = serde_json::to_string(&candidate_names).unwrap();
                let lookup_result_json = serde_json::json!({
                    "source": "librarian",
                    "declaration_name": args.declaration_name,
                    "confidence": confidence_str,
                    "import_module": args.import_module,
                    "snippet": args.snippet,
                }).to_string();

                conn.execute(
                    "UPDATE formalization_plan_items SET mathlib_coverage_status = ?1, mathlib_candidate_names_json = ?2, lookup_result_json = ?3 WHERE id = ?4",
                    (coverage_status, &candidate_names_json, &lookup_result_json, &args.plan_item_id),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "plan_item_id": args.plan_item_id,
                    "mathlib_coverage_status": coverage_status,
                    "mathlib_candidate_names": candidate_names,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            _ => Err(McpError::new(ErrorCode::METHOD_NOT_FOUND, format!("Method not found: {}", request.name), None)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rmcp::service::{serve_client, serve_server};
    use rmcp::model::CallToolRequestParams;
    use rmcp::transport::async_rw::AsyncRwTransport;
    use chatdb_proof_core::lean::LeanGateway;
    use chatdb_proof_core::lean::module::AssembledModule;
    use chatdb_proof_core::models::{Obligation, LeanVerificationOutcome, LeanVerificationResult, LeanModuleVerificationResult, LeanDiagnostic, LeanDiagnosticCategory};

    struct MockGateway;
    impl LeanGateway for MockGateway {
        fn verify_exact(
            &self,
            obligation: &Obligation,
            candidate_source: &str,
            _approved_dependency_ids: &[Uuid],
            environment: &str,
            _import_manifest: &[String],
        ) -> Result<LeanVerificationResult, String> {
            let outcome = if candidate_source.contains("sorry") {
                LeanVerificationOutcome::KernelFail
            } else {
                LeanVerificationOutcome::KernelPass
            };
            Ok(LeanVerificationResult {
                outcome,
                attempt_id: Uuid::new_v4(),
                obligation_id: obligation.id,
                theorem_name: obligation.theorem_name.clone(),
                expected_statement_hash: obligation.statement_hash.clone(),
                elaborated_statement_hash: None,
                environment_hash: environment.to_string(),
                proof_source_hash: "".to_string(),
                compiled_artifact_hash: None,
                proof_term_hash: None,
                diagnostic: None,
                all_diagnostics: vec![],
                dependency_use_report: None,
                wall_time_ms: 1,
                lean_cpu_time_ms: 1,
            })
        }

        // The trait default now fails closed (see lean/mod.rs) — MockGateway
        // deliberately vouches for any import so tests can isolate
        // manifest-extension bookkeeping from real Lean validation, which is
        // covered live separately (see test_problem_create_extends_import_manifest).
        fn validate_import_manifest(&self, _imports: &[String]) -> Result<(), String> {
            Ok(())
        }

        // Mock module verification: a module "passes" the kernel unless its
        // assembled source carries the explicit MOCK_KERNEL_FAIL marker, so tests
        // can drive both the pass and kernel-fail commit paths without a real Lean
        // toolchain. Policy rejections (bad names, prohibited constructs, root hash
        // mismatch) happen in chatdb-core BEFORE this is ever reached.
        fn verify_module(&self, assembled: &AssembledModule, environment: &str) -> Result<LeanModuleVerificationResult, String> {
            let fail = assembled.source.contains("MOCK_KERNEL_FAIL");
            let outcome = if fail { LeanVerificationOutcome::KernelFail } else { LeanVerificationOutcome::KernelPass };
            Ok(LeanModuleVerificationResult {
                outcome,
                problem_namespace: assembled.namespace.clone(),
                root_lean_name: assembled.root_lean_name.clone(),
                module_source_hash: assembled.module_source_hash.clone(),
                declaration_manifest_hash: assembled.declaration_manifest_hash.clone(),
                environment_hash: environment.to_string(),
                kernel_result_hash: format!("mock-kernel-{}", &assembled.module_source_hash[..8.min(assembled.module_source_hash.len())]),
                diagnostic: if fail {
                    Some(LeanDiagnostic {
                        category: LeanDiagnosticCategory::TacticFailure,
                        primary_message: "mock kernel failure".to_string(),
                        source_span: None, goal: None, local_context: vec![], unsolved_goals: vec![],
                        used_dependencies: vec![], error_code: None, canonical_goal_hash: None,
                    })
                } else { None },
                all_diagnostics: vec![],
                wall_time_ms: 1,
            })
        }
    }

    fn test_handler() -> ChatDbMcp {
        test_handler_with_gateway(RealLeanGateway::new(PathBuf::from("dummy"), PathBuf::from("dummy")))
    }

    fn test_handler_with_gateway(gateway: impl LeanGateway + Send + Sync + 'static) -> ChatDbMcp {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        ChatDbMcp {
            conn: Arc::new(Mutex::new(conn)),
            gateway: Box::new(gateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        }
    }

    async fn connected_client(handler: ChatDbMcp) -> rmcp::service::RunningService<rmcp::RoleClient, InitializeRequestParams> {
        let (client_stream, server_stream) = tokio::io::duplex(1 << 20);
        let (client_read, client_write) = tokio::io::split(client_stream);
        let (server_read, server_write) = tokio::io::split(server_stream);

        let server_transport = AsyncRwTransport::new(server_read, server_write);
        let client_transport = AsyncRwTransport::new(client_read, client_write);

        tokio::spawn(async move {
            if let Ok(service) = serve_server(handler, server_transport).await {
                let _ = service.waiting().await;
            }
        });

        let client_info = Implementation::new("test-client", "1.0.0");
        let capabilities = ClientCapabilities::default();
        let init = InitializeRequestParams::new(capabilities, client_info);
        serve_client(init, client_transport).await.unwrap()
    }

    fn tool_json(res: &CallToolResult) -> serde_json::Value {
        assert!(!res.is_error.unwrap_or(false), "tool call returned isError: {:?}", res.content);
        serde_json::from_str(res.content[0].as_text().unwrap().text.as_str()).unwrap()
    }

    #[tokio::test]
    async fn test_mcp_list_tools_and_describe() {
        let client = connected_client(test_handler()).await;

        let list_res = client.peer().list_tools(None).await.unwrap();
        assert_eq!(list_res.tools.len(), 32);

        // The episode_step schema must be fully INLINE at the parameter site: no
        // $ref for the client to chase, and an explicit `type: "object"` on the
        // action node so coercion-by-declared-type harnesses treat it as an object
        // (found live: a client shipped the action as a string because the param
        // node only carried a $ref).
        let step_tool = list_res.tools.iter().find(|t| t.name == "episode_step").unwrap();
        let step_schema_val = serde_json::to_value(&step_tool.input_schema).unwrap();
        let step_schema = step_schema_val.to_string();
        assert!(!step_schema.contains("$ref"), "episode_step schema must not contain dangling refs: {step_schema}");
        assert!(step_schema.contains("proof_term"), "TypedAction variants must be visible in the schema: {step_schema}");
        assert!(step_schema.contains("give_up"), "internally-tagged variant names must be visible: {step_schema}");
        let action_node = &step_schema_val["properties"]["action"];
        assert_eq!(action_node["type"], "object", "action param must declare objecthood inline: {action_node}");
        assert!(action_node["oneOf"].is_array(), "action param must carry the oneOf variants inline: {action_node}");

        let call_params = CallToolRequestParams::new("environment_describe");
        let call_res = client.peer().call_tool(call_params).await.unwrap();
        let json = tool_json(&call_res);
        assert_eq!(json["protocol_version"], "2025-11-25");
        assert_eq!(json["lean_gateway"], "unavailable");
        assert!(json["lean_environment"].is_null(), "no lean-checker at the dummy test path -> no environment to report");
        assert!(json["action_schema"].is_object(), "environment_describe must expose the TypedAction schema");
        assert_eq!(json["action_examples"][0]["type"], "solve");
    }

    /// Full MCP-level playthrough: this is the scenario the live playtest against
    /// the release binary could never complete (attempt_claim missing, revision
    /// hardcoded to 1, outcome vocabulary violating the CHECK constraint). It must
    /// stay green — it's the regression guard for all of that.
    #[tokio::test]
    async fn test_decompose_and_giveup_playthrough() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "1 + 1 = 2",
            "root_formal_statement": "1 + 1 = 2",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 10, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        assert_eq!(ep["state"], "awaiting_external_action");
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let advertised_revision = req["episode_revision"].as_i64().unwrap();
        assert_eq!(advertised_revision, 0, "advance() must advertise the episode's ACTUAL current_revision, not a hardcoded value");

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "k1", "expected_revision": advertised_revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        // Decompose using the exact advertised revision (proves the revision fix).
        let step1 = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": advertised_revision, "claim_token": claim_token,
            "action": {"type": "decompose", "sub_lemmas": ["helper lemma"]},
            "cost_micros": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step1["disposition"], "accepted", "{:?}", step1);
        assert_eq!(step1["accepted"], true);
        let next_req = &step1["next_action_request"];
        assert!(!next_req.is_null(), "advance() must produce a next request without a UNIQUE(episode_id, episode_revision) collision");
        let next_revision = next_req["episode_revision"].as_i64().unwrap();
        assert_eq!(next_revision, 1, "revision must have incremented by exactly one");

        // GiveUp on the child obligation should terminate the episode.
        let request_id_2 = next_req["id"].as_str().unwrap().to_string();
        let claim2 = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id_2,
            "idempotency_key": "k2", "expected_revision": next_revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id_2 = claim2["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token_2 = claim2["claim_token"].as_str().unwrap().to_string();

        let step2 = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id_2,
            "expected_revision": next_revision, "claim_token": claim_token_2,
            "action": {"type": "give_up"}, "cost_micros": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step2["disposition"], "accepted", "{:?}", step2);
        assert_eq!(step2["outcome"], "gave_up");
        assert_eq!(step2["termination_reason"], "model_gave_up");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "terminated");
        assert_eq!(status["outcome"], "gave_up");

        // episode_close on an already-terminal episode must not hit the CHECK
        // constraint that killed it live (`outcome IN (...)` mismatch).
        let close = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_close").with_arguments(serde_json::json!({
            "episode_id": episode_id, "reason": "test",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(close["status"], "already_closed");

        let traj = tool_json(&peer.call_tool(CallToolRequestParams::new("trajectory_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert!(traj.as_array().unwrap().len() >= 3, "expected episode_created + 2 action_committed + episode_terminated events, got {:?}", traj);

        let replay = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_replay").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(replay["audit_passed"], true);
    }

    #[tokio::test]
    async fn test_fabricated_claim_and_stale_revision_still_rejected() {
        let handler = test_handler();
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let fabricated = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": Uuid::new_v4().to_string(),
            "expected_revision": 0, "claim_token": "made-up",
            "action": {"type": "give_up"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(fabricated["disposition"], "invalid_response");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["current_revision"], 0, "a rejected fabricated claim must not mutate episode state");
    }

    /// The scenario the fix plan calls the definition of done: create → observe →
    /// claim → solve → certified, with a non-empty audited trajectory. This never
    /// passed against the release binary (attempt_claim didn't exist, and even
    /// with SQL-claimed attempts the revision bug rolled back every accepted step).
    #[tokio::test]
    async fn test_solve_to_certified_playthrough() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Prove that 1 + 1 = 2 in the natural numbers.",
            "root_formal_statement": "1 + 1 = 2",
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": create["source_problem_hash"], "root_statement_hash": create["root_statement_hash"],
            "rendering_hash": create["rendering_hash"], "evidence_json": "{}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_observe").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["observation"]["root_theorem_signature"], "1 + 1 = 2");

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "solve-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "norm_num"},
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "{:?}", step);
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "certified", "{:?}", step);
        assert_eq!(step["termination_reason"], "root_proved", "{:?}", step);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "terminated");
        assert_eq!(status["outcome"], "certified");
        assert_eq!(status["step_count"], 1);
        assert_eq!(status["cost_budget_micros"], 999_900);

        let traj = tool_json(&peer.call_tool(CallToolRequestParams::new("trajectory_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let events = traj.as_array().unwrap();
        assert!(events.len() >= 3, "expected episode_created + action_committed + episode_terminated, got {:?}", events);

        let replay = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_replay").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(replay["audit_passed"], true, "{:?}", replay);
        assert_eq!(replay["events_replayed"], 1, "the one solve event must be re-verified through the gateway, not vacuously passed");
        assert_eq!(replay["replay_status"], "matched(1)");

        // proof_export: markdown dossier carries the verdict, the goal, the tree,
        // the winning proof term, and the attempt table; lean format is bare source.
        let export_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        assert!(!export_res.is_error.unwrap_or(false));
        let md = export_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains("CERTIFIED"), "{md}");
        assert!(md.contains("1 + 1 = 2"), "{md}");
        assert!(md.contains("## Proof tree"), "{md}");
        assert!(md.contains("norm_num"), "the winning proof term must appear: {md}");
        assert!(md.contains("kernel_pass"), "{md}");

        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("theorem root_theorem : 1 + 1 = 2 := by"), "{lean}");
        assert!(!lean.contains("## "), "lean format must be bare source, not markdown: {lean}");
        // The assembled source must carry the problem's REAL import manifest, not
        // a hardcoded Ring/NormNum stub. This problem used the default manifest.
        assert!(lean.contains("import Mathlib.Tactic.Ring"), "real manifest must be rendered: {lean}");
        assert!(lean.contains("import Mathlib.Tactic.NormNum"), "real manifest must be rendered: {lean}");
        // The dossier must state the pinned verification context as a receipt.
        assert!(md.contains("## Verification context"), "dossier must carry verification context: {md}");
        assert!(md.contains("Import manifest hash:"), "dossier must carry manifest hash: {md}");
        assert!(md.contains("Environment hash:"), "dossier must carry environment hash: {md}");
    }

    /// Review feedback on #16/#17: `episode_step` must NOT hold the DB mutex while
    /// the Lean gateway call is in flight, or every other concurrent tool call on
    /// this session blocks on it for the whole verification (up to 60-120s for a
    /// real toolchain). This gateway holds the SAME `Arc<Mutex<Connection>>` the
    /// handler uses and asserts `try_lock()` succeeds from INSIDE `verify_exact`/
    /// `verify_module` — a deterministic, non-timing-dependent proof: if the
    /// handler still held the lock at the moment it calls the gateway, `try_lock`
    /// would fail and the assertion would trip. Exercises both the Solve AND
    /// SubmitModule paths, since both defer their gateway call across the lock
    /// release (see `step::PrepOutcome::NeedsGateway` in chatdb-core).
    struct LockCheckingGateway {
        conn: Arc<Mutex<Connection>>,
    }
    impl LeanGateway for LockCheckingGateway {
        fn verify_exact(
            &self,
            obligation: &Obligation,
            _candidate_source: &str,
            _approved_dependency_ids: &[Uuid],
            environment: &str,
            _import_manifest: &[String],
        ) -> Result<LeanVerificationResult, String> {
            // Returning Err (a normal, non-panicking gateway failure) rather than
            // panicking/asserting: a panic here unwinds inside the spawned server
            // task, which is fragile to test against (the client sees a transport
            // error, not a clean tool-result failure). An Err propagates through
            // the ordinary StepError::LeanGatewayError path instead.
            if self.conn.try_lock().is_err() {
                return Err("DB mutex must be released before invoking the Lean gateway (verify_exact)".to_string());
            }
            Ok(LeanVerificationResult {
                outcome: LeanVerificationOutcome::KernelPass,
                attempt_id: Uuid::new_v4(),
                obligation_id: obligation.id,
                theorem_name: obligation.theorem_name.clone(),
                expected_statement_hash: obligation.statement_hash.clone(),
                elaborated_statement_hash: None,
                environment_hash: environment.to_string(),
                proof_source_hash: "".to_string(),
                compiled_artifact_hash: None,
                proof_term_hash: None,
                diagnostic: None,
                all_diagnostics: vec![],
                dependency_use_report: None,
                wall_time_ms: 1,
                lean_cpu_time_ms: 1,
            })
        }
        fn validate_import_manifest(&self, _imports: &[String]) -> Result<(), String> { Ok(()) }
        fn verify_module(&self, assembled: &AssembledModule, environment: &str) -> Result<LeanModuleVerificationResult, String> {
            if self.conn.try_lock().is_err() {
                return Err("DB mutex must be released before invoking the Lean gateway (verify_module)".to_string());
            }
            Ok(LeanModuleVerificationResult {
                outcome: LeanVerificationOutcome::KernelPass,
                problem_namespace: assembled.namespace.clone(),
                root_lean_name: assembled.root_lean_name.clone(),
                module_source_hash: assembled.module_source_hash.clone(),
                declaration_manifest_hash: assembled.declaration_manifest_hash.clone(),
                environment_hash: environment.to_string(),
                kernel_result_hash: "k".to_string(),
                diagnostic: None,
                all_diagnostics: vec![],
                wall_time_ms: 1,
            })
        }
    }

    #[tokio::test]
    async fn test_episode_step_releases_db_lock_before_solve_gateway_call() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(LockCheckingGateway { conn: conn_arc }),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "lock release check", "root_formal_statement": "1 + 1 = 2",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "lock-check", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        // If the DB mutex were still held during verify_exact, LockCheckingGateway
        // returns Err, which surfaces as disposition="error" in the response
        // payload (episode_step's transport-level call still succeeds either way —
        // the tool call itself doesn't fail; the internal Lean-gateway failure is
        // reported in the JSON body). Assert the step actually reached
        // disposition="accepted" with a real kernel_pass to confirm the lock was
        // genuinely free.
        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "norm_num"},
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "a tripped lock check means the DB mutex was still held during verify_exact: {:?}", step);
        assert_eq!(step["accepted"], true, "{:?}", step);
    }

    /// Same proof as above, for the `SubmitModule` gateway path.
    #[tokio::test]
    async fn test_episode_step_releases_db_lock_before_module_gateway_call() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(LockCheckingGateway { conn: conn_arc }),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "lock release check (module)", "root_formal_statement": "True",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "lock-check-mod", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module", "module_items": [],
                "root_theorem": {"name": "root", "statement": "True", "proof_term": "trivial"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "a tripped lock check means the DB mutex was still held during verify_module: {:?}", step);
        assert_eq!(step["accepted"], true, "{:?}", step);
    }

    /// Drives an episode through observe → claim → submit_module. A helper `def`
    /// plus a root theorem whose statement hash-matches the registered root must
    /// verify as one module and prove the root obligation. Under an attested (not
    /// fidelity-verified) problem the terminal outcome is `kernel_verified`.
    #[tokio::test]
    async fn test_submit_module_def_and_root_passes() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Define double and show double 2 = 4.",
            "root_formal_statement": "double 2 = 4",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "mod-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [
                    {"item_kind": "def", "name": "double", "type_signature": "Nat → Nat", "body": "fun n => n + n"}
                ],
                "root_theorem": {"name": "double_two", "statement": "double 2 = 4", "proof_term": "rfl"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "{:?}", step);
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "kernel_verified", "attested problem: module root proof reaches kernel_verified, not certified: {:?}", step);
        assert_eq!(step["termination_reason"], "root_proved", "{:?}", step);
        // Kernel pass reward earned by the module verification action.
        let reward = step["reward"].as_array().unwrap();
        assert!(reward.iter().any(|r| r["id"] == "kernel_pass"), "module verification must earn kernel_pass: {:?}", reward);
        assert!(reward.iter().any(|r| r["id"] == "root_kernel_verified"), "{:?}", reward);
        assert!(!reward.iter().any(|r| r["id"] == "terminal_success"), "attested-only must NOT earn terminal_success: {:?}", reward);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "terminated");
        assert_eq!(status["outcome"], "kernel_verified");

        // Self-review finding: proof_export's attempt-log renderer had no
        // "submit_module" arm, so winning_proof was never populated for a
        // module-proved obligation — the format="lean" fallback rendering then
        // embedded a fabricated `sorry` for a theorem the kernel actually
        // verified. Must never happen: the real root proof_term ("rfl") must
        // appear, and "sorry" must not.
        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(!lean.contains("sorry"), "a kernel-verified module theorem must never be exported with a fabricated sorry: {lean}");
        assert!(lean.contains("rfl"), "the real root proof_term must appear in the export: {lean}");
    }

    /// A module whose root theorem statement does NOT hash-match the registered
    /// root is rejected by policy (before Lean), the obligation stays open, and the
    /// episode does not terminate. This is the "cannot silently prove a different
    /// goal" guard.
    #[tokio::test]
    async fn test_submit_module_root_statement_mismatch_rejected() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Show 2 + 2 = 4.",
            "root_formal_statement": "2 + 2 = 4",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "mod-bad", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [],
                // A trivially-true DIFFERENT statement — must be refused, not accepted.
                "root_theorem": {"name": "sneaky", "statement": "True", "proof_term": "trivial"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "the step itself commits (as a rejected attempt): {:?}", step);
        assert_eq!(step["accepted"], false, "a root-hash mismatch must not be accepted: {:?}", step);
        assert!(step["outcome"] != "kernel_verified" && step["outcome"] != "certified", "{:?}", step);
        assert!(step["termination_reason"].is_null(), "a rejected module must not terminate the episode: {:?}", step);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_ne!(status["state"], "terminated", "{:?}", status);
        assert_eq!(status["invalid_action_count"], 1, "{:?}", status);
    }

    /// Drives one attested-problem episode all the way to a single submit_module
    /// step and returns the step-result JSON. Keeps the rejection-matrix tests to
    /// the essential difference — the module payload — instead of repeating the
    /// whole observe/claim/step dance.
    async fn attested_module_step(root_statement: &str, action: serde_json::Value) -> serde_json::Value {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": format!("staging test for: {}", root_statement),
            "root_formal_statement": root_statement,
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "stage-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": action, "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap())
    }

    /// Required test #12: under a fidelity-VERIFIED problem, a module root proof
    /// reaches `certified` (both proof soundness AND statement fidelity), promoting
    /// the problem to COMPLETE — the module analogue of the certified Solve path.
    #[tokio::test]
    async fn test_submit_module_with_verified_fidelity_reaches_certified() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Show 1 + 1 = 2.",
            "root_formal_statement": "1 + 1 = 2",
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": create["source_problem_hash"], "root_statement_hash": create["root_statement_hash"],
            "rendering_hash": create["rendering_hash"], "evidence_json": "{}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "cert-mod", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [],
                "root_theorem": {"name": "one_one", "statement": "1 + 1 = 2", "proof_term": "norm_num"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["outcome"], "certified", "verified fidelity + module root proof must certify: {:?}", step);
        let reward = step["reward"].as_array().unwrap();
        assert!(reward.iter().any(|r| r["id"] == "terminal_success"), "certified module must earn terminal_success: {:?}", reward);

        // Problem promoted to COMPLETE.
        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv_id || p["id"] == pv_id);
        if let Some(p) = mine {
            assert_eq!(p["state"], "COMPLETE", "certified module must promote the problem to COMPLETE: {:?}", p);
        }
    }

    /// Issue #4: a verified module round-trips through replay and proof_export.
    /// Replay re-assembles from structured JSON and re-verifies (matched(1)); the
    /// lean export IS the exact module source; the markdown dossier shows the
    /// module's declaration manifest, not only a proof tree.
    #[tokio::test]
    async fn test_submit_module_persist_export_and_replay_roundtrip() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Define quad and show quad 2 = 8.",
            "root_formal_statement": "quad 2 = 8",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "rt-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [
                    {"item_kind": "def", "name": "quad", "type_signature": "Nat → Nat", "body": "fun n => 4 * n"}
                ],
                "root_theorem": {"name": "quad_two", "statement": "quad 2 = 8", "proof_term": "rfl"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["outcome"], "kernel_verified", "{:?}", step);

        // Replay: the module re-assembles from structured JSON and re-verifies.
        let replay = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_replay").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(replay["audit_passed"], true, "{:?}", replay);
        assert_eq!(replay["events_replayed"], 1, "the module verification event must be re-verified, not vacuously passed: {:?}", replay);
        assert_eq!(replay["replay_status"], "matched(1)");

        // Lean export IS the exact module source, under the problem namespace.
        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("namespace ChatDB.P_"), "module export must carry the namespace: {lean}");
        assert!(lean.contains("def quad : Nat → Nat :="), "{lean}");
        assert!(lean.contains("theorem quad_two : quad 2 = 8 := by"), "{lean}");
        assert!(lean.trim_end().ends_with("end ChatDB.P_") || lean.contains("\nend ChatDB.P_"), "{lean}");

        // Markdown dossier shows the module's declaration manifest.
        let md_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = md_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains("## Verified module"), "{md}");
        assert!(md.contains("module_source_hash:"), "{md}");
        assert!(md.contains("root_theorem"), "the manifest must mark the root theorem item: {md}");
        assert!(md.contains("`quad`"), "the manifest must list the helper def: {md}");
    }

    /// Self-review finding: proof_export's module rendering paired freshly
    /// re-assembled source with the STORED module_source_hash unconditionally —
    /// if re-assembly (against the problem's CURRENT import manifest) ever
    /// produces source that no longer hashes to what was actually verified, the
    /// export would silently claim a hash for source it didn't compute the hash
    /// from. Directly corrupts the stored hash (simulating drift — no tool can
    /// produce this through normal use) and asserts BOTH export formats loudly
    /// flag the mismatch instead of silently presenting a receipt that lies.
    #[tokio::test]
    async fn test_proof_export_flags_module_hash_mismatch() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(MockGateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "hash mismatch check", "root_formal_statement": "True",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "hash-mismatch-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module", "module_items": [],
                "root_theorem": {"name": "root", "statement": "True", "proof_term": "trivial"}
            },
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["outcome"], "kernel_verified", "{:?}", step);

        {
            let conn = conn_arc.lock().await;
            conn.execute(
                "UPDATE episode_verified_modules SET module_source_hash = 'deadbeef_tampered' WHERE episode_id = ?1",
                [&episode_id],
            ).unwrap();
        }

        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("WARNING") && lean.contains("hash"), "lean export must flag the hash mismatch: {lean}");

        let md_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = md_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains("WARNING") && md.contains("hash mismatch"), "dossier must flag the hash mismatch: {md}");
    }

    /// Issue #3 acceptance: a helper def passes and the root theorem uses it — the
    /// whole module verifies together and the root obligation is proved.
    #[tokio::test]
    async fn test_submit_module_helper_def_used_by_root() {
        let step = attested_module_step("triple 3 = 9", serde_json::json!({
            "type": "submit_module",
            "module_items": [
                {"item_kind": "def", "name": "triple", "type_signature": "Nat → Nat", "body": "fun n => 3 * n"}
            ],
            "root_theorem": {"name": "triple_three", "statement": "triple 3 = 9", "proof_term": "rfl"}
        })).await;
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "kernel_verified", "{:?}", step);
    }

    /// Issue #3 acceptance: the root theorem is fine, but a NON-root helper carries
    /// a prohibited construct — the WHOLE module is rejected, atomically. Nothing is
    /// committed, the episode does not terminate, and the rejection is legible.
    /// Review feedback on #16/#17: extended beyond direct leading commands to also
    /// cover attribute-prefixed and modifier-prefixed declaration escapes, which a
    /// scanner checking only "is the line's first token a declaration keyword"
    /// would miss (`@[simp] theorem cheat`, `private theorem cheat`).
    #[tokio::test]
    async fn test_submit_module_prohibited_construct_matrix() {
        // Each case: a valid root theorem (`True`/`trivial`) plus one helper whose
        // content smuggles a prohibited construct. The token the client tried to
        // inject must appear in the surfaced rejection diagnostic.
        let cases: Vec<(&str, serde_json::Value)> = vec![
            ("import",     serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nimport Mathlib"})),
            ("namespace",  serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nnamespace Evil"})),
            ("end",        serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nend"})),
            ("set_option", serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\nset_option maxHeartbeats 0"})),
            ("axiom",      serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\n\naxiom cheat : False"})),
            ("opaque",     serde_json::json!({"item_kind":"theorem","name":"h","statement":"True","proof_term":"opaque trivial"})),
            ("unsafe",     serde_json::json!({"item_kind":"theorem","name":"h","statement":"True","proof_term":"unsafe trivial"})),
            ("sorry",      serde_json::json!({"item_kind":"theorem","name":"h","statement":"True","proof_term":"sorry"})),
            ("@[",         serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\n\n@[simp] theorem cheat : False := by trivial"})),
            ("private",    serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\n\nprivate theorem cheat : False := by trivial"})),
            ("protected",  serde_json::json!({"item_kind":"def","name":"h","type_signature":"Nat","body":"0\n\nprotected theorem cheat : False := by trivial"})),
        ];

        for (token, bad_item) in cases {
            let step = attested_module_step("True", serde_json::json!({
                "type": "submit_module",
                "module_items": [bad_item],
                "root_theorem": {"name": "root", "statement": "True", "proof_term": "trivial"}
            })).await;
            assert_eq!(step["accepted"], false, "module smuggling `{}` must be rejected: {:?}", token, step);
            assert!(step["termination_reason"].is_null(), "rejected `{}` module must not terminate the episode: {:?}", token, step);
            let diag = step["rejection_diagnostic"].as_str().unwrap_or("");
            assert!(diag.contains(token) || diag.contains("prohibited"),
                "rejection for `{}` must be legible (got {:?})", token, step["rejection_diagnostic"]);
        }
    }

    /// Issue #3 acceptance: a raw `import` (a helper theorem proof carrying its own
    /// import line) is rejected — the client never writes import lines; the server
    /// owns them. Also confirms the episode stays re-attemptable after rejection.
    #[tokio::test]
    async fn test_submit_module_raw_import_rejected_and_reattemptable() {
        let step = attested_module_step("True", serde_json::json!({
            "type": "submit_module",
            "module_items": [],
            "root_theorem": {"name": "root", "statement": "True", "proof_term": "trivial\nimport Mathlib.Tactic"}
        })).await;
        assert_eq!(step["accepted"], false, "{:?}", step);
        assert!(step["rejection_diagnostic"].as_str().unwrap_or("").contains("import"), "{:?}", step);
        // The obligation is still open: the step handed back a next_action_request
        // targeting the same (still-unproved) root, so the prover can try again.
        assert!(!step["next_action_request"].is_null(), "a rejected module must leave the obligation open for another attempt: {:?}", step);
    }

    /// Review feedback on #17: the existing no-write-on-failure test
    /// (`verify_module_does_not_write_on_failure` in chatdb-core) only proves
    /// filesystem no-write when the GATEWAY can't even spawn Lean. It never proves
    /// no-write when a module is rejected by POLICY — and policy rejection never
    /// reaches the gateway at all (a different code path entirely), so this
    /// exercises a genuinely distinct policy violation (an invalid dotted name,
    /// not the root-hash mismatch other tests already cover) through the actual
    /// MCP path and asserts the same invariant: no verified lemma row (the
    /// obligation stays open, re-attemptable), no episode termination, and no
    /// reward for the rejected attempt.
    #[tokio::test]
    async fn test_submit_module_policy_rejection_writes_nothing_trusted() {
        let step = attested_module_step("True", serde_json::json!({
            "type": "submit_module",
            "module_items": [
                {"item_kind": "def", "name": "Mathlib.evil", "type_signature": "Nat", "body": "0"}
            ],
            "root_theorem": {"name": "root", "statement": "True", "proof_term": "trivial"}
        })).await;
        assert_eq!(step["accepted"], false, "{:?}", step);
        assert!(step["termination_reason"].is_null(), "policy rejection must not terminate the episode: {:?}", step);
        assert!(!step["next_action_request"].is_null(), "policy rejection must leave the obligation open for another attempt: {:?}", step);
        // No kernel_pass reward — the reward list must not carry one for a rejected attempt.
        let reward = step["reward"].as_array().unwrap();
        assert!(!reward.iter().any(|r| r["id"] == "kernel_pass"), "a policy-rejected module must not earn kernel_pass: {:?}", step);
    }

    /// Review feedback on #15: a malformed stored `import_manifest_json` must not
    /// silently degrade to the historical Ring/NormNum fallback and look like a
    /// normal, trustworthy receipt. Both formats must flag it loudly. Corrupts the
    /// row directly (no tool can produce this — problem_create only ever writes
    /// server-generated, well-formed JSON) to simulate pre-existing data corruption.
    #[tokio::test]
    async fn test_proof_export_flags_corrupted_import_manifest() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(MockGateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "corrupted manifest check",
            "root_formal_statement": "True",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();

        {
            let conn = conn_arc.lock().await;
            conn.execute(
                "UPDATE problem_versions SET import_manifest_json = ?1 WHERE id = ?2",
                ("{not valid json", &pv_id),
            ).unwrap();
        }

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("WARNING"), "lean export must visibly flag a corrupted manifest: {lean}");

        let md_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = md_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains("WARNING") && md.contains("corrupted receipt"), "dossier must visibly flag a corrupted manifest: {md}");
    }

    /// `proof_export` must render the problem's actual (custom) import manifest,
    /// not a hardcoded Ring/NormNum stub. Regression guard for the bug that made
    /// the dossier export a non-replayable approximation.
    #[tokio::test]
    async fn test_proof_export_renders_custom_import_manifest() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "custom manifest export check",
            "root_formal_statement": "True",
            "problem_imports": ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum",
                                "Mathlib.Data.Real.Basic", "Mathlib.Tactic.LinearCombination"],
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let manifest_hash = create["import_manifest_hash"].as_str().unwrap().to_string();
        assert!(!manifest_hash.is_empty(), "custom manifest must have a real hash");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        // Even with nothing proved yet, the lean-format export must already reflect
        // the real manifest (imports are rendered before the obligation body).
        let lean_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "lean",
        }).as_object().unwrap().clone())).await.unwrap();
        let lean = lean_res.content[0].as_text().unwrap().text.clone();
        assert!(lean.contains("import Mathlib.Data.Real.Basic"), "custom manifest module missing from export: {lean}");
        assert!(lean.contains("import Mathlib.Tactic.LinearCombination"), "custom manifest module missing from export: {lean}");

        let md_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = md_res.content[0].as_text().unwrap().text.clone();
        assert!(md.contains(&manifest_hash), "dossier must carry the problem's manifest hash: {md}");
        assert!(md.contains("Mathlib.Data.Real.Basic"), "dossier must list the manifest modules: {md}");
    }

    /// A solve that fails Lean verification must NOT terminate the episode, must
    /// count as a step, and must leave the obligation open (re-attemptable). It
    /// also MUST still bump attempt_count — unlike a bare gateway/infrastructure
    /// error (see test_gateway_infrastructure_error_does_not_bump_attempt_count),
    /// a kernel_fail is a genuine verdict about the prover's submission.
    #[tokio::test]
    async fn test_solve_kernel_fail_does_not_terminate() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(MockGateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "fail-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "sorry"},
            "cost_micros": 50,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted");
        assert_eq!(step["accepted"], false);
        assert!(step["outcome"].is_null());
        assert!(!step["next_action_request"].is_null(), "a kernel-fail must re-offer the same (still open) obligation, not dead-end the episode");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["state"], "awaiting_external_action");
        assert_eq!(status["step_count"], 1);

        let attempt_count: i64 = {
            let conn = conn_arc.lock().await;
            conn.query_row(
                "SELECT attempt_count FROM episode_obligations WHERE episode_id = ?1 AND kind = 'root'",
                [&episode_id],
                |row| row.get(0),
            ).unwrap()
        };
        assert_eq!(attempt_count, 1, "a genuine kernel_fail verdict must count as an attempt");
    }

    /// Self-review finding: a bare gateway/infrastructure failure (spawn error,
    /// timeout — `Err(String)` from `verify_exact`, NOT a normal kernel_fail
    /// verdict) carries no information about the prover's submission and must
    /// NOT bump `episode_obligations.attempt_count` — scheduler.rs feeds
    /// attempt_count into difficulty estimation and uses it as a sort
    /// tie-breaker, so counting bare infra flakes would misrepresent how many
    /// real semantic attempts were made. A genuine kernel verdict (pass OR fail)
    /// DOES bump it, exactly as before the prepare/finalize split.
    struct FailingGateway;
    impl LeanGateway for FailingGateway {
        fn verify_exact(&self, _o: &Obligation, _p: &str, _d: &[Uuid], _e: &str, _m: &[String]) -> Result<LeanVerificationResult, String> {
            Err("simulated infrastructure failure: process spawn error".to_string())
        }
        fn validate_import_manifest(&self, _imports: &[String]) -> Result<(), String> { Ok(()) }
    }

    #[tokio::test]
    async fn test_gateway_infrastructure_error_does_not_bump_attempt_count() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(FailingGateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "infra-fail-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "norm_num"},
            "cost_micros": 50,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "error", "a gateway Err must surface as disposition=error: {:?}", step);

        let (attempt_count, budget): (i64, i64) = {
            let conn = conn_arc.lock().await;
            let attempt_count = conn.query_row(
                "SELECT attempt_count FROM episode_obligations WHERE episode_id = ?1 AND kind = 'root'",
                [&episode_id],
                |row| row.get(0),
            ).unwrap();
            let budget = conn.query_row(
                "SELECT cost_budget_micros FROM episodes WHERE id = ?1", [&episode_id], |row| row.get(0),
            ).unwrap();
            (attempt_count, budget)
        };
        assert_eq!(attempt_count, 0, "a bare gateway/infrastructure error must not count as an attempt");
        assert_eq!(budget, 1_000_000, "a bare gateway/infrastructure error must refund the pessimistic budget reservation, leaving budget unchanged");
    }

    /// Review feedback (self-review): `cost_budget_micros` must be reserved
    /// atomically with the CAS check in `attempt_prepare`, BEFORE the Lean
    /// gateway call runs with the DB lock released — otherwise a concurrent
    /// `model_call_reserve` could read the stale, not-yet-deducted budget during
    /// the gateway call and grant a lease against budget this attempt is already
    /// about to spend (a TOCTOU overcommit). This gateway peeks at the budget
    /// from INSIDE verify_exact (the same window a concurrent tool call would
    /// see) and asserts it is already reduced — proving the window is closed.
    struct BudgetPeekingGateway {
        conn: Arc<Mutex<Connection>>,
        episode_id: Arc<std::sync::Mutex<Option<String>>>,
    }
    impl LeanGateway for BudgetPeekingGateway {
        fn verify_exact(&self, obligation: &Obligation, _p: &str, _d: &[Uuid], environment: &str, _m: &[String]) -> Result<LeanVerificationResult, String> {
            let episode_id = self.episode_id.lock().unwrap().clone().expect("episode_id must be set before calling");
            let budget: i64 = {
                let conn = self.conn.try_lock().expect("DB mutex must be released during the gateway call");
                conn.query_row("SELECT cost_budget_micros FROM episodes WHERE id = ?1", [&episode_id], |row| row.get(0)).unwrap()
            };
            if budget != 999_900 {
                return Err(format!("budget was not reserved before the gateway call: expected 999900, got {}", budget));
            }
            Ok(LeanVerificationResult {
                outcome: LeanVerificationOutcome::KernelPass,
                attempt_id: Uuid::new_v4(),
                obligation_id: obligation.id,
                theorem_name: obligation.theorem_name.clone(),
                expected_statement_hash: obligation.statement_hash.clone(),
                elaborated_statement_hash: None,
                environment_hash: environment.to_string(),
                proof_source_hash: "".to_string(),
                compiled_artifact_hash: None,
                proof_term_hash: None,
                diagnostic: None,
                all_diagnostics: vec![],
                dependency_use_report: None,
                wall_time_ms: 1,
                lean_cpu_time_ms: 1,
            })
        }
        fn validate_import_manifest(&self, _imports: &[String]) -> Result<(), String> { Ok(()) }
    }

    #[tokio::test]
    async fn test_budget_reserved_before_gateway_call_closes_toctou_window() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let gateway_episode_id: Arc<std::sync::Mutex<Option<String>>> = Arc::new(std::sync::Mutex::new(None));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(BudgetPeekingGateway { conn: conn_arc.clone(), episode_id: gateway_episode_id.clone() }),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5, "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        *gateway_episode_id.lock().unwrap() = Some(episode_id.clone());
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "budget-toctou-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "norm_num"},
            "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["disposition"], "accepted", "if the gateway's budget check failed, this surfaces as disposition=error: {:?}", step);
        assert_eq!(step["accepted"], true, "{:?}", step);

        let budget: i64 = {
            let conn = conn_arc.lock().await;
            conn.query_row("SELECT cost_budget_micros FROM episodes WHERE id = ?1", [&episode_id], |row| row.get(0)).unwrap()
        };
        assert_eq!(budget, 999_900, "budget must be exactly once-deducted after a successful step (no double-charge from prepare+finalize)");
    }

    /// The idempotency key on attempt_claim must be safe to retry: same key while
    /// still claimed returns the SAME attempt instead of erroring on the unique index.
    #[tokio::test]
    async fn test_attempt_claim_idempotent_retry() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let request_id = ep["next_action_request"]["id"].as_str().unwrap().to_string();

        let claim_args = serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "retry-key", "expected_revision": 0,
        }).as_object().unwrap().clone();

        let first = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(claim_args.clone())).await.unwrap());
        let second = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(claim_args)).await.unwrap());

        assert_eq!(first["action_attempt_id"], second["action_attempt_id"], "retried claim with same idempotency_key must return the same attempt");
        assert_eq!(first["claim_token"], second["claim_token"]);
    }

    /// A problem_create with no lean-checker configured (test_handler's gateway
    /// points at a dummy path) must not silently write a meaningless placeholder
    /// like "unspecified-env" — that made replay's determinism claim untraceable
    /// to any actual toolchain/Mathlib pin. It should say plainly that the
    /// gateway was unavailable.
    #[tokio::test]
    async fn test_problem_create_env_hash_is_not_a_silent_placeholder() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();
        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(pv["environment_hash"], "lean-gateway-unavailable", "{:?}", pv);
    }

    /// A request nobody ever claimed still carries its own `expiration_at` timer,
    /// separate from an attempt's claim_expiration. Nothing previously checked it,
    /// so a lapsed unclaimed request displayed `status: pending` forever instead of
    /// being retired and replaced.
    #[tokio::test]
    async fn test_unclaimed_request_expiry_is_recovered() {
        let handler = test_handler();
        let conn_handle = handler.conn.clone();
        let client = connected_client(handler).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let stale_request_id = ep["next_action_request"]["id"].as_str().unwrap().to_string();

        {
            let conn = conn_handle.lock().await;
            conn.execute(
                "UPDATE action_requests SET expiration_at = '2000-01-01T00:00:00Z' WHERE id = ?1",
                [&stale_request_id],
            ).unwrap();
        }

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_observe").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let fresh_request_id = observed["action_request"]["id"].as_str().unwrap().to_string();
        assert_ne!(fresh_request_id, stale_request_id, "episode_observe must retire a lapsed request and mint a fresh one, not keep serving the stale one");
        assert_eq!(observed["action_request"]["status"], "pending");

        let conn = conn_handle.lock().await;
        let stale_status: String = conn.query_row(
            "SELECT status FROM action_requests WHERE id = ?1", [&stale_request_id], |row| row.get(0),
        ).unwrap();
        assert_eq!(stale_status, "expired", "the lapsed request must be marked expired, not left as pending");
    }

    async fn claim_and_solve(peer: &rmcp::service::Peer<rmcp::RoleClient>, episode_id: &str, proof_term: &str, idem: &str) -> serde_json::Value {
        let obs = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_observe").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let req = &obs["action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": idem, "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"], "expected_revision": req["episode_revision"],
            "claim_token": claim["claim_token"], "action": {"type": "solve", "proof_term": proof_term}, "cost_micros": 100,
        }).as_object().unwrap().clone())).await.unwrap())
    }

    /// THE EXPLOIT REGRESSION: a kernel-verified root of a weakened/vacuous
    /// formalization must reach `kernel_verified`, never `certified` — proof
    /// soundness and statement fidelity are independent claims. Uses
    /// unsafe_dev_attestation (the only way to prove without a real review),
    /// which itself must never be enough to reach `certified`.
    #[tokio::test]
    async fn test_weakened_root_reaches_kernel_verified_not_certified() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Every even natural is divisible by two.",
            "root_formal_statement": "∀ n : ℕ, Even n → True", // weakened: conclusion is trivially true
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(pv["fidelity_status"], "attested");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let step = claim_and_solve(&peer, &episode_id, "trivial", "weakened-root").await;
        assert_eq!(step["accepted"], true, "{:?}", step);
        assert_eq!(step["outcome"], "kernel_verified", "a weakened root must NOT present as certified: {:?}", step);
        assert_eq!(step["termination_reason"], "root_proved");
        let reward_ids: Vec<&str> = step["reward"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert!(reward_ids.contains(&"root_kernel_verified"), "{:?}", reward_ids);
        assert!(!reward_ids.contains(&"terminal_success"), "TerminalSuccess must never be paid without fidelity verification: {:?}", reward_ids);

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["outcome"], "kernel_verified");

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["state"], "FIDELITY_REVIEW", "root-proved-but-unverified must park in FIDELITY_REVIEW, never COMPLETE: {:?}", mine);
        assert_eq!(mine["fidelity_status"], "attested", "finalization must not silently upgrade fidelity_status");

        // And the dossier must never render this as CERTIFIED.
        let export_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = export_res.content[0].as_text().unwrap().text.clone();
        assert!(!md.contains("✅ CERTIFIED"), "dossier must not overclaim: {md}");
        assert!(md.contains("QUARANTINED"), "{md}");
    }

    /// A review can only authorize the exact text it reviewed — submitted hashes
    /// that don't match the problem's CURRENT source/statement/rendering must be
    /// rejected, not silently accepted as if they matched.
    #[tokio::test]
    async fn test_fidelity_review_wrong_hashes_rejected() {
        let client = connected_client(test_handler()).await;
        let peer = client.peer();
        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "y",
        }).as_object().unwrap().clone())).await.unwrap());

        // mcp_invalid_params surfaces as a JSON-RPC-level error (Err from call_tool),
        // not a CallToolResult with isError=true — this handler rejects the request
        // outright rather than returning a "soft" failure result.
        let res = peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": "0000000000000000000000000000000000000000000000000000000000000000",
            "root_statement_hash": pv["root_statement_hash"], "rendering_hash": pv["rendering_hash"],
            "evidence_json": "{}",
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "a hash mismatch must be rejected, not silently accepted");

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["fidelity_status"], "unreviewed", "a rejected submission must not mutate fidelity_status");
    }

    /// POSITIVE CONTROL: a real review verifying a faithful formalization, done
    /// BEFORE proving, reaches `certified` / COMPLETE directly on root proof —
    /// the split must not penalize the case where fidelity was already settled.
    #[tokio::test]
    async fn test_fidelity_verified_before_proving_reaches_certified_directly() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "Every even natural is divisible by two.",
            "root_formal_statement": "∀ n : ℕ, Even n → ∃ k : ℕ, n = 2 * k",
        }).as_object().unwrap().clone())).await.unwrap());

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": pv["source_problem_hash"], "root_statement_hash": pv["root_statement_hash"],
            "rendering_hash": pv["rendering_hash"], "evidence_json": "{\"note\":\"faithful\"}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "cost_budget_micros": 1_000_000,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let step = claim_and_solve(&peer, &episode_id, "exact ⟨n, by ring⟩", "positive-control").await;
        assert_eq!(step["outcome"], "certified", "{:?}", step);
        let reward_ids: Vec<&str> = step["reward"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert!(reward_ids.contains(&"terminal_success"), "{:?}", reward_ids);

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["state"], "COMPLETE");
    }

    /// A fidelity review landing 'verified' AFTER an episode already reached
    /// `kernel_verified` must promote that episode's outcome to `certified`
    /// retroactively — the review need not precede the proof.
    #[tokio::test]
    async fn test_fidelity_review_promotes_kernel_verified_episode_retroactively() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "y", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let step = claim_and_solve(&peer, &episode_id, "trivial", "retro-1").await;
        assert_eq!(step["outcome"], "kernel_verified");

        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": pv["source_problem_hash"], "root_statement_hash": pv["root_statement_hash"],
            "rendering_hash": pv["rendering_hash"], "evidence_json": "{}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let status = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(status["outcome"], "certified", "retroactive promotion must flip the episode's outcome: {:?}", status);

        let plist = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_list").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let mine = plist.as_array().unwrap().iter().find(|p| p["problem_version_id"] == pv["problem_version_id"]).unwrap();
        assert_eq!(mine["state"], "COMPLETE");
    }

    /// problem_create with problem_imports must extend the base manifest (never
    /// replace it), validate each new import through the gateway, and return a
    /// manifest hash a client can copy into lean_declaration_lookup/replay checks.
    #[tokio::test]
    async fn test_problem_create_extends_import_manifest() {
        // MockGateway explicitly overrides validate_import_manifest to Ok(())
        // (the trait default now fails closed) — this isolates "does the
        // manifest extend/return correctly" from "does the real Lean validation
        // work" (covered live separately). The module path still has to pass
        // the syntax-level valid_lean_module_path check, which runs before any
        // gateway is invoked regardless of which gateway is configured.
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
            "problem_imports": ["Mathlib.NumberTheory.Padics.PadicVal.Basic"],
        }).as_object().unwrap().clone())).await.unwrap());

        let manifest = pv["import_manifest"].as_array().unwrap();
        let manifest_strs: Vec<&str> = manifest.iter().map(|v| v.as_str().unwrap()).collect();
        assert!(manifest_strs.contains(&"Mathlib.Tactic.Ring"), "{:?}", manifest_strs);
        assert!(manifest_strs.contains(&"Mathlib.Tactic.NormNum"), "{:?}", manifest_strs);
        assert!(manifest_strs.contains(&"Mathlib.NumberTheory.Padics.PadicVal.Basic"), "{:?}", manifest_strs);
        assert!(pv["import_manifest_hash"].as_str().unwrap().len() > 0);

        // A bad module path must be rejected at creation, not discovered later at
        // solve time. Syntax-level rejection is covered by
        // test_problem_create_rejects_malformed_import_syntax below; rejection
        // by real Lean (a syntactically-valid but nonexistent module) is
        // exercised live against the real lean-checker rather than here, since
        // test_handler's RealLeanGateway points at a dummy, nonexistent path.
    }

    /// lean_declaration_lookup must return an honest per-name status even when
    /// the gateway can't check (default trait impl) — never silently fabricate
    /// availability or unavailability.
    #[tokio::test]
    async fn test_lean_declaration_lookup_reports_environment_error_honestly() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
        }).as_object().unwrap().clone())).await.unwrap());

        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("lean_declaration_lookup").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "names": ["Nat.factorization"],
        }).as_object().unwrap().clone())).await.unwrap());

        assert_eq!(res["import_manifest_hash"], pv["import_manifest_hash"]);
        let results = res["results"].as_array().unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0]["query"], "Nat.factorization");
        // test_handler's gateway doesn't override lookup_declarations, so the
        // honest default (environment_error) applies — this proves the tool
        // never guesses when it can't actually check.
        assert_eq!(results[0]["status"], "environment_error");
    }

    /// SOUNDNESS: `problem_imports` entries are written verbatim into
    /// `import {module}\n` Lean source (see build_import_block). Without
    /// syntax validation, a string containing a newline could append arbitrary
    /// Lean commands (e.g. `axiom cheat : False`) to every proof file checked
    /// against that problem's manifest — a full soundness bypass through a
    /// different door than the one the fidelity-review split closed. Every
    /// one of these must be rejected at problem_create, before it ever reaches
    /// the gateway or gets stored.
    #[tokio::test]
    async fn test_problem_create_rejects_malformed_import_syntax() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let malicious = [
            "Mathlib\naxiom cheat : False",
            "Mathlib\nset_option maxHeartbeats 0",
            "Mathlib -- comment",
            "Mathlib; axiom cheat : False",
            "Mathlib.Tactic (foo)",
            "",
            "   ",
            "Mathlib.\u{0}Tactic",
        ];
        for m in malicious {
            let res = peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
                "source_problem_text": "x", "root_formal_statement": "x",
                "problem_imports": [m],
            }).as_object().unwrap().clone())).await;
            assert!(res.is_err(), "malformed import {:?} must be rejected, not compiled", m);
        }

        // A well-formed module path must still be accepted (this isn't just
        // rejecting everything).
        let ok = peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
            "problem_imports": ["Mathlib.NumberTheory.Padics.PadicVal.Basic"],
        }).as_object().unwrap().clone())).await;
        assert!(ok.is_ok(), "a syntactically valid module path must not be rejected: {:?}", ok);
    }

    /// SOUNDNESS: `lean_declaration_lookup`'s `names` are written verbatim into
    /// `#check {name}\n` Lean source. Same injection surface as
    /// problem_imports, one door earlier — a name containing a newline could
    /// append arbitrary Lean commands that execute inside the verifier process
    /// during the lookup itself.
    #[tokio::test]
    async fn test_lean_declaration_lookup_rejects_malformed_names() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "x",
        }).as_object().unwrap().clone())).await.unwrap());

        let malicious = [
            "Nat.factorization\naxiom cheat : False",
            "Nat.factorization -- comment",
            "Nat.factorization; #exit",
            "",
            "   ",
        ];
        for n in malicious {
            let res = peer.call_tool(CallToolRequestParams::new("lean_declaration_lookup").with_arguments(serde_json::json!({
                "problem_version_id": pv["problem_version_id"], "names": [n],
            }).as_object().unwrap().clone())).await;
            assert!(res.is_err(), "malformed declaration name {:?} must be rejected", n);
        }

        let too_many: Vec<String> = (0..51).map(|i| format!("Nat.foo{}", i)).collect();
        let res = peer.call_tool(CallToolRequestParams::new("lean_declaration_lookup").with_arguments(serde_json::json!({
            "problem_version_id": pv["problem_version_id"], "names": too_many,
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "more than 50 names must be rejected");
    }

    // -- Proof-pattern memory (issue #24) ------------------------------------

    /// Issue #24 acceptance: the library is seeded from the v0.3.1 overnight
    /// sprint on a fresh database, and proof_pattern_search's no-query path
    /// lists the whole active library.
    #[tokio::test]
    async fn test_proof_pattern_library_is_seeded_on_fresh_db() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_search").with_arguments(serde_json::json!({}).as_object().unwrap().clone())).await.unwrap());
        let patterns = res["patterns"].as_array().unwrap();
        assert!(patterns.len() >= 7, "expected at least the 7 seeded patterns, got {}: {:?}", patterns.len(), patterns);
        assert!(patterns.iter().any(|p| p["pattern_key"] == "mutual_recursion_needs_mutual_group"), "{:?}", patterns);
        assert!(patterns.iter().all(|p| p["confidence"] == "seed" || p["pattern_key"].as_str().map(|k| !k.starts_with("test_")).unwrap_or(true)), "{:?}", patterns);
    }

    /// A pattern's failure_signature/recommended_repair must be findable by
    /// free-text search, and search results carry a usable pattern_id.
    #[tokio::test]
    async fn test_proof_pattern_search_free_text() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_search").with_arguments(serde_json::json!({
            "query": "well-founded",
        }).as_object().unwrap().clone())).await.unwrap());
        let patterns = res["patterns"].as_array().unwrap();
        assert!(patterns.iter().any(|p| p["pattern_key"] == "well_founded_recursion_needs_simp_not_rfl"), "{:?}", patterns);
        for p in patterns {
            assert!(p["pattern_id"].as_str().is_some_and(|s| !s.is_empty()), "{:?}", p);
        }
    }

    /// A client can register a new pattern, and a duplicate pattern_key is
    /// rejected rather than silently overwriting the existing one.
    #[tokio::test]
    async fn test_proof_pattern_create_and_reject_duplicate_key() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create_args = serde_json::json!({
            "pattern_key": "test_custom_pattern_xyz",
            "title": "Custom test pattern",
            "failure_signature": "some symptom",
            "recommended_repair": "some fix",
            "confidence": "mined",
        });
        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_create").with_arguments(create_args.as_object().unwrap().clone())).await.unwrap());
        assert!(created["pattern_id"].as_str().is_some_and(|s| !s.is_empty()), "{:?}", created);

        let dup = peer.call_tool(CallToolRequestParams::new("proof_pattern_create").with_arguments(create_args.as_object().unwrap().clone())).await;
        assert!(dup.is_err(), "duplicate pattern_key must be rejected, not silently overwritten");
    }

    /// Issue #24's core boundary, verified as a real regression test (not just
    /// asserted in a comment): recording a pattern application against a real
    /// episode must not change that episode's or its obligations' state in ANY
    /// way. Snapshots the full episodes + episode_obligations rows before and
    /// after, and asserts byte-for-byte equality — the ONLY table allowed to
    /// gain a row is proof_pattern_applications itself.
    #[tokio::test]
    async fn test_proof_pattern_application_cannot_change_proof_status() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp { conn: conn_arc.clone(), gateway: Box::new(MockGateway), lean_available: false, lean_environment: None, lean_project_path: PathBuf::from("dummy") };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "pattern-application boundary check", "root_formal_statement": "True",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let pattern = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_search").with_arguments(serde_json::json!({
            "query": "unfold",
        }).as_object().unwrap().clone())).await.unwrap());
        let pattern_id = pattern["patterns"][0]["pattern_id"].as_str().unwrap().to_string();

        // Snapshot every row (as raw JSON, columns and all) in the two tables a
        // real proof-status change would touch, before recording the application.
        let snapshot = |conn: &Connection| -> (String, String) {
            let episodes: Vec<String> = conn.prepare("SELECT * FROM episodes ORDER BY id").unwrap()
                .query_map([], |row| { let n = row.as_ref().column_count(); Ok((0..n).map(|i| format!("{:?}", row.get_ref(i).unwrap())).collect::<Vec<_>>().join(",")) }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            let obligations: Vec<String> = conn.prepare("SELECT * FROM episode_obligations ORDER BY id").unwrap()
                .query_map([], |row| { let n = row.as_ref().column_count(); Ok((0..n).map(|i| format!("{:?}", row.get_ref(i).unwrap())).collect::<Vec<_>>().join(",")) }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            (episodes.join("|"), obligations.join("|"))
        };
        let before = { let c = conn_arc.lock().await; snapshot(&c) };

        let app = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_record_application").with_arguments(serde_json::json!({
            "pattern_id": pattern_id, "episode_id": episode_id, "role": "suggested_hint",
        }).as_object().unwrap().clone())).await.unwrap());
        assert!(app["application_id"].as_str().is_some_and(|s| !s.is_empty()), "{:?}", app);

        let after = { let c = conn_arc.lock().await; snapshot(&c) };
        assert_eq!(before, after, "recording a pattern application must not change episodes or episode_obligations at all");

        // The application row itself DID get recorded (the tool did something).
        let app_count: i64 = { let c = conn_arc.lock().await; c.query_row("SELECT COUNT(*) FROM proof_pattern_applications WHERE episode_id = ?1", [&episode_id], |r| r.get(0)).unwrap() };
        assert_eq!(app_count, 1);
    }

    /// Recording an application against an unknown pattern_id or episode_id is
    /// rejected before any row is written — never a silent no-op or a foreign
    /// row pointing at nothing.
    #[tokio::test]
    async fn test_proof_pattern_record_application_rejects_unknown_ids() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "x", "root_formal_statement": "True", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": create["problem_version_id"], "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let res = peer.call_tool(CallToolRequestParams::new("proof_pattern_record_application").with_arguments(serde_json::json!({
            "pattern_id": "not-a-real-pattern-id", "episode_id": episode_id, "role": "suggested_hint",
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "unknown pattern_id must be rejected: {:?}", res);

        let pattern = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_search").with_arguments(serde_json::json!({
            "query": "unfold",
        }).as_object().unwrap().clone())).await.unwrap());
        let pattern_id = pattern["patterns"][0]["pattern_id"].as_str().unwrap().to_string();
        let res = peer.call_tool(CallToolRequestParams::new("proof_pattern_record_application").with_arguments(serde_json::json!({
            "pattern_id": pattern_id, "episode_id": "not-a-real-episode-id", "role": "suggested_hint",
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "unknown episode_id must be rejected: {:?}", res);
    }

    /// Issue #24 acceptance: proof_export's markdown dossier lists applied
    /// lessons in their own section, separate from the verified-proof content,
    /// and a dossier with NO recorded applications is completely unaffected
    /// (no empty "Lessons" header appears).
    #[tokio::test]
    async fn test_proof_export_lists_lessons_separately_from_proof() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "lessons dossier check", "root_formal_statement": "True", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        // No applications recorded yet: no Lessons section at all.
        let md_res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md = md_res.content[0].as_text().unwrap().text.clone();
        assert!(!md.contains("## Lessons applied"), "no Lessons section should appear with zero applications: {md}");

        let pattern = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_search").with_arguments(serde_json::json!({
            "query": "mutual recursion",
        }).as_object().unwrap().clone())).await.unwrap());
        let pattern_id = pattern["patterns"][0]["pattern_id"].as_str().unwrap().to_string();
        tool_json(&peer.call_tool(CallToolRequestParams::new("proof_pattern_record_application").with_arguments(serde_json::json!({
            "pattern_id": pattern_id, "episode_id": episode_id, "role": "suggested_hint", "notes": "tried mutual defs, hit unknown identifier",
        }).as_object().unwrap().clone())).await.unwrap());

        let md_res2 = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md2 = md_res2.content[0].as_text().unwrap().text.clone();
        assert!(md2.contains("## Lessons applied (advisory — not part of the verified proof)"), "{md2}");
        assert!(md2.contains("mutual_group") || md2.to_lowercase().contains("mutual"), "{md2}");
        assert!(md2.contains("suggested_hint"), "{md2}");
    }

    // -- Draft artifacts + formalization planning (issues #23, #10) ---------

    async fn create_problem(peer: &rmcp::service::Peer<rmcp::RoleClient>, statement: &str) -> String {
        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": format!("draft/plan test for: {}", statement),
            "root_formal_statement": statement,
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        create["problem_version_id"].as_str().unwrap().to_string()
    }

    #[tokio::test]
    async fn test_draft_create_and_observe_roundtrip() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;

        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "content": "Sketch: use a bijection between A and B.", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_id = created["draft_id"].as_str().unwrap().to_string();
        assert!(!created["content_hash"].as_str().unwrap().is_empty());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_observe").with_arguments(serde_json::json!({
            "draft_id": draft_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["content"], "Sketch: use a bijection between A and B.");
        assert_eq!(observed["author"], "model-x");
        assert_eq!(observed["moves"].as_array().unwrap().len(), 0);
    }

    #[tokio::test]
    async fn test_draft_extract_moves_appends_across_calls() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "content": "x", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_id = created["draft_id"].as_str().unwrap().to_string();

        tool_json(&peer.call_tool(CallToolRequestParams::new("draft_extract_moves").with_arguments(serde_json::json!({
            "draft_id": draft_id,
            "moves": [{"move_kind": "bijection", "description": "map A to B"}],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("draft_extract_moves").with_arguments(serde_json::json!({
            "draft_id": draft_id,
            "moves": [{"move_kind": "induction", "description": "induct on n"}],
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_observe").with_arguments(serde_json::json!({
            "draft_id": draft_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let moves = observed["moves"].as_array().unwrap();
        assert_eq!(moves.len(), 2, "{:?}", moves);
        assert_eq!(moves[0]["move_kind"], "bijection");
        assert_eq!(moves[0]["move_order"], 0);
        assert_eq!(moves[1]["move_kind"], "induction");
        assert_eq!(moves[1]["move_order"], 1, "second call must append, not overwrite move_order");
    }

    /// Issue #23's core regression test, verified as a real byte-level
    /// snapshot (not just a comment asserting the boundary): a draft
    /// containing an outright false proof claim, plus extracting moves from
    /// it, must not change episodes or episode_obligations in any way.
    #[tokio::test]
    async fn test_draft_with_false_claim_cannot_mark_obligation_proved() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp { conn: conn_arc.clone(), gateway: Box::new(MockGateway), lean_available: false, lean_environment: None, lean_project_path: PathBuf::from("dummy") };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "draft false-claim boundary check", "root_formal_statement": "True", "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let snapshot = |conn: &Connection| -> (String, String) {
            let episodes: Vec<String> = conn.prepare("SELECT * FROM episodes ORDER BY id").unwrap()
                .query_map([], |row| { let n = row.as_ref().column_count(); Ok((0..n).map(|i| format!("{:?}", row.get_ref(i).unwrap())).collect::<Vec<_>>().join(",")) }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            let obligations: Vec<String> = conn.prepare("SELECT * FROM episode_obligations ORDER BY id").unwrap()
                .query_map([], |row| { let n = row.as_ref().column_count(); Ok((0..n).map(|i| format!("{:?}", row.get_ref(i).unwrap())).collect::<Vec<_>>().join(",")) }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            (episodes.join("|"), obligations.join("|"))
        };
        let before = { let c = conn_arc.lock().await; snapshot(&c) };

        let draft = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "episode_id": episode_id,
            "content": "Claim: this theorem is trivially true by inspection, no further work needed. QED.",
            "author": "adversarial-model",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_id = draft["draft_id"].as_str().unwrap().to_string();
        tool_json(&peer.call_tool(CallToolRequestParams::new("draft_extract_moves").with_arguments(serde_json::json!({
            "draft_id": draft_id,
            "moves": [{"move_kind": "unknown", "description": "asserted trivially true, no actual argument given"}],
        }).as_object().unwrap().clone())).await.unwrap());

        let after = { let c = conn_arc.lock().await; snapshot(&c) };
        assert_eq!(before, after, "a draft (even one containing a false proof claim) must never change episodes or episode_obligations");
    }

    #[tokio::test]
    async fn test_formalization_plan_create_seeded_from_draft_moves() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let draft = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "content": "x", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_id = draft["draft_id"].as_str().unwrap().to_string();
        let extracted = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_extract_moves").with_arguments(serde_json::json!({
            "draft_id": draft_id,
            "moves": [
                {"move_kind": "auxiliary_lemma", "description": "need: sum of first n squares"},
                {"move_kind": "external_citation", "description": "cites a known bound from a paper"},
            ],
        }).as_object().unwrap().clone())).await.unwrap());
        let move_ids: Vec<String> = extracted["created_move_ids"].as_array().unwrap().iter().map(|v| v.as_str().unwrap().to_string()).collect();

        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan A", "source_draft_id": draft_id,
            "seed_items_from_draft_moves": [
                {"draft_move_id": move_ids[0], "kind": "missing_lemma"},
                {"draft_move_id": move_ids[1], "kind": "external_citation"},
            ],
            "risk_flags": ["relies on an uncited external bound"],
        }).as_object().unwrap().clone())).await.unwrap());
        let plan_id = plan["plan_id"].as_str().unwrap().to_string();
        assert_eq!(plan["seeded_item_ids"].as_array().unwrap().len(), 2);

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_observe").with_arguments(serde_json::json!({
            "plan_id": plan_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["title"], "Plan A");
        assert_eq!(observed["status"], "draft");
        let items = observed["items"].as_array().unwrap();
        assert_eq!(items.len(), 2, "{:?}", items);
        assert_eq!(items[0]["kind"], "missing_lemma");
        assert_eq!(items[0]["description"], "need: sum of first n squares");
        assert_eq!(items[1]["kind"], "external_citation");

        // The seeded draft moves are now marked promoted.
        let draft_after = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_observe").with_arguments(serde_json::json!({
            "draft_id": draft_id,
        }).as_object().unwrap().clone())).await.unwrap());
        for m in draft_after["moves"].as_array().unwrap() {
            assert!(!m["promoted_plan_item_id"].is_null(), "{:?}", m);
        }
    }

    #[tokio::test]
    async fn test_formalization_plan_create_rejects_double_promotion_and_wrong_draft() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;

        let draft_a = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "content": "a", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_a_id = draft_a["draft_id"].as_str().unwrap().to_string();
        let draft_b = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "content": "b", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_b_id = draft_b["draft_id"].as_str().unwrap().to_string();

        let extracted = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_extract_moves").with_arguments(serde_json::json!({
            "draft_id": draft_a_id, "moves": [{"move_kind": "unknown", "description": "m1"}],
        }).as_object().unwrap().clone())).await.unwrap());
        let move_id = extracted["created_move_ids"][0].as_str().unwrap().to_string();

        // Wrong draft: move belongs to draft_a, not draft_b.
        let bad = peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "P", "source_draft_id": draft_b_id,
            "seed_items_from_draft_moves": [{"draft_move_id": move_id, "kind": "concept"}],
        }).as_object().unwrap().clone())).await;
        assert!(bad.is_err(), "seeding from a move that belongs to a different draft must be rejected");

        // Correct draft, first promotion succeeds.
        tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "P", "source_draft_id": draft_a_id,
            "seed_items_from_draft_moves": [{"draft_move_id": move_id, "kind": "concept"}],
        }).as_object().unwrap().clone())).await.unwrap());

        // Second promotion of the SAME move must be rejected.
        let dup = peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "P2", "source_draft_id": draft_a_id,
            "seed_items_from_draft_moves": [{"draft_move_id": move_id, "kind": "concept"}],
        }).as_object().unwrap().clone())).await;
        assert!(dup.is_err(), "a move already promoted into a plan item must not be promotable again");
    }

    /// Self-review finding: the SAME draft_move_id appearing twice in one
    /// seed_items_from_draft_moves batch used to pass per-move validation
    /// (each check saw the not-yet-committed state) and then get promoted
    /// into two separate plan items, silently orphaning the first.
    #[tokio::test]
    async fn test_formalization_plan_create_rejects_duplicate_move_id_in_same_batch() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let draft = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "content": "x", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_id = draft["draft_id"].as_str().unwrap().to_string();
        let extracted = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_extract_moves").with_arguments(serde_json::json!({
            "draft_id": draft_id, "moves": [{"move_kind": "unknown", "description": "m1"}],
        }).as_object().unwrap().clone())).await.unwrap());
        let move_id = extracted["created_move_ids"][0].as_str().unwrap().to_string();

        let res = peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "P", "source_draft_id": draft_id,
            "seed_items_from_draft_moves": [
                {"draft_move_id": move_id, "kind": "concept"},
                {"draft_move_id": move_id, "kind": "missing_lemma"},
            ],
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "the same draft_move_id twice in one batch must be rejected, not silently create two items from one move");
    }

    /// Self-review finding: draft_create never verified that episode_id's OWN
    /// problem_version_id matches the given problem_version_id, and
    /// formalization_plan_create never verified that source_draft_id's OWN
    /// problem_version_id matches either — both would silently accept a
    /// cross-problem mismatch.
    #[tokio::test]
    async fn test_draft_and_plan_create_reject_cross_problem_mismatch() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_a = create_problem(&peer, "True").await;
        let pv_b = create_problem(&peer, "1 + 1 = 2").await;

        let ep_b = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_b, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_b_id = ep_b["episode_id"].as_str().unwrap().to_string();

        // episode_b belongs to problem B, not problem A.
        let bad_draft = peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_a, "episode_id": episode_b_id, "content": "x", "author": "model-x",
        }).as_object().unwrap().clone())).await;
        assert!(bad_draft.is_err(), "a draft's problem_version_id must match its episode_id's own problem_version_id");

        let draft_b = tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_b, "content": "x", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        let draft_b_id = draft_b["draft_id"].as_str().unwrap().to_string();

        // draft_b belongs to problem B, not problem A.
        let bad_plan = peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_a, "title": "P", "source_draft_id": draft_b_id,
        }).as_object().unwrap().clone())).await;
        assert!(bad_plan.is_err(), "a plan's problem_version_id must match its source_draft_id's own problem_version_id");
    }

    /// Self-review finding: promoting two different plan items to the SAME
    /// real obligation used to succeed silently — nothing stopped two
    /// plan-tracking rows from both "claiming" one obligation.
    #[tokio::test]
    async fn test_formalization_plan_promote_rejects_obligation_double_claim() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp { conn: conn_arc.clone(), gateway: Box::new(MockGateway), lean_available: false, lean_environment: None, lean_project_path: PathBuf::from("dummy") };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "dup-claim-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "decompose", "sub_lemmas": ["a helper lemma"]},
            "cost_micros": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        let obligation_id: String = { let c = conn_arc.lock().await; c.query_row(
            "SELECT id FROM episode_obligations WHERE episode_id = ?1 AND created_by = 'decomposition' ORDER BY created_at DESC LIMIT 1",
            [&episode_id], |row| row.get(0),
        ).unwrap() };

        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan",
        }).as_object().unwrap().clone())).await.unwrap());
        let plan_id = plan["plan_id"].as_str().unwrap().to_string();
        let item1 = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
            "plan_id": plan_id, "kind": "missing_lemma", "description": "item 1",
        }).as_object().unwrap().clone())).await.unwrap());
        let item2 = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
            "plan_id": plan_id, "kind": "missing_lemma", "description": "item 2",
        }).as_object().unwrap().clone())).await.unwrap());

        tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_promote_item_to_obligation").with_arguments(serde_json::json!({
            "plan_item_id": item1["plan_item_id"], "episode_id": episode_id, "obligation_id": obligation_id,
        }).as_object().unwrap().clone())).await.unwrap());

        // A second, DIFFERENT plan item claiming the SAME obligation must be rejected.
        let dup = peer.call_tool(CallToolRequestParams::new("formalization_plan_promote_item_to_obligation").with_arguments(serde_json::json!({
            "plan_item_id": item2["plan_item_id"], "episode_id": episode_id, "obligation_id": obligation_id,
        }).as_object().unwrap().clone())).await;
        assert!(dup.is_err(), "two plan items must not both be allowed to claim the same real obligation");
    }

    #[tokio::test]
    async fn test_formalization_plan_add_item_and_update() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan B",
        }).as_object().unwrap().clone())).await.unwrap());
        let plan_id = plan["plan_id"].as_str().unwrap().to_string();

        let item = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
            "plan_id": plan_id, "kind": "missing_definition", "description": "need padicValNat",
            "mathlib_candidate_names": ["padicValNat"],
        }).as_object().unwrap().clone())).await.unwrap());
        let item_id = item["plan_item_id"].as_str().unwrap().to_string();

        let updated = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_update").with_arguments(serde_json::json!({
            "plan_id": plan_id, "status": "active", "risk_flags": ["needs a fresh construction"],
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(updated["status"], "active");
        assert_eq!(updated["title"], "Plan B", "omitted title must be left unchanged, not cleared");

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_observe").with_arguments(serde_json::json!({
            "plan_id": plan_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["status"], "active");
        assert_eq!(observed["risk_flags"][0], "needs a fresh construction");
        assert_eq!(observed["items"][0]["plan_item_id"], item_id);
        assert_eq!(observed["items"][0]["mathlib_candidate_names"][0], "padicValNat");
    }

    #[tokio::test]
    async fn test_formalization_plan_attach_lookup_maps_status_and_rejects_non_open() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan C",
        }).as_object().unwrap().clone())).await.unwrap());
        let plan_id = plan["plan_id"].as_str().unwrap().to_string();

        let cases = [
            ("available", "found"),
            ("unknown_declaration", "not_found"),
            ("not_available_under_current_manifest", "partial"),
            ("not_in_current_import_scope", "partial"),
            ("environment_error", "unknown"),
        ];
        for (lookup_status, expected_coverage) in cases {
            let item = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
                "plan_id": plan_id, "kind": "missing_lemma", "description": format!("case for {lookup_status}"),
            }).as_object().unwrap().clone())).await.unwrap());
            let item_id = item["plan_item_id"].as_str().unwrap().to_string();

            let attached = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_attach_lookup").with_arguments(serde_json::json!({
                "plan_item_id": item_id, "lookup_status": lookup_status, "matched_name": "Nat.foo",
            }).as_object().unwrap().clone())).await.unwrap());
            assert_eq!(attached["mathlib_coverage_status"], expected_coverage, "lookup_status {lookup_status}");
        }
    }

    #[tokio::test]
    async fn test_formalization_plan_promote_item_to_obligation() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp { conn: conn_arc.clone(), gateway: Box::new(MockGateway), lean_available: false, lean_environment: None, lean_project_path: PathBuf::from("dummy") };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();

        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "plan-promote-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();

        // A real obligation, created through the normal budget-accounted
        // Decompose action — NOT through any plan tool.
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "decompose", "sub_lemmas": ["a helper lemma"]},
            "cost_micros": 10,
        }).as_object().unwrap().clone())).await.unwrap());

        let obligation_id: String = { let c = conn_arc.lock().await; c.query_row(
            "SELECT id FROM episode_obligations WHERE episode_id = ?1 AND created_by = 'decomposition' ORDER BY created_at DESC LIMIT 1",
            [&episode_id], |row| row.get(0),
        ).unwrap() };

        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan D",
        }).as_object().unwrap().clone())).await.unwrap());
        let plan_id = plan["plan_id"].as_str().unwrap().to_string();
        let item = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
            "plan_id": plan_id, "kind": "missing_lemma", "description": "a helper lemma",
        }).as_object().unwrap().clone())).await.unwrap());
        let item_id = item["plan_item_id"].as_str().unwrap().to_string();

        // Wrong episode_id must be rejected.
        let bad = peer.call_tool(CallToolRequestParams::new("formalization_plan_promote_item_to_obligation").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "episode_id": "not-a-real-episode", "obligation_id": obligation_id,
        }).as_object().unwrap().clone())).await;
        assert!(bad.is_err());

        let promoted = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_promote_item_to_obligation").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "episode_id": episode_id, "obligation_id": obligation_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(promoted["status"], "promoted");

        // Re-promoting the same (now-promoted) item must be rejected.
        let dup = peer.call_tool(CallToolRequestParams::new("formalization_plan_promote_item_to_obligation").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "episode_id": episode_id, "obligation_id": obligation_id,
        }).as_object().unwrap().clone())).await;
        assert!(dup.is_err(), "an already-promoted item must not be promotable again");

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_observe").with_arguments(serde_json::json!({
            "plan_id": plan_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["items"][0]["status"], "promoted");
        assert_eq!(observed["items"][0]["promoted_obligation_id"], obligation_id);
    }

    /// proof_export shows Drafts and Formalization plans in their own
    /// sections, separate from the verified proof, and shows neither when
    /// there is no draft/plan activity for the episode.
    #[tokio::test]
    async fn test_proof_export_shows_drafts_and_plans_separately() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let md0 = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md0 = md0.content[0].as_text().unwrap().text.clone();
        assert!(!md0.contains("## Drafts"), "no Drafts section with zero drafts: {md0}");
        assert!(!md0.contains("## Formalization plans"), "no plans section with zero plans: {md0}");

        tool_json(&peer.call_tool(CallToolRequestParams::new("draft_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "episode_id": episode_id, "content": "informal sketch here", "author": "model-x",
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan E",
        }).as_object().unwrap().clone())).await.unwrap());

        let md1 = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap();
        let md1 = md1.content[0].as_text().unwrap().text.clone();
        assert!(md1.contains("## Drafts (informal — not part of the verified proof)"), "{md1}");
        assert!(md1.contains("informal sketch here"), "{md1}");
        assert!(md1.contains("## Formalization plans (advisory — not part of the verified proof)"), "{md1}");
        assert!(md1.contains("Plan E"), "{md1}");
    }

    // -- Mathlib librarian (issue #25) ---------------------------------------

    /// Builds a synthetic Mathlib-shaped source tree under a temp directory
    /// (not the real, multi-GB Mathlib checkout) so the scanning/parsing
    /// logic is tested hermetically — no dependency on lean-checker being set
    /// up on whatever machine runs `cargo test`. The real toolchain path is
    /// verified separately via the playtest.rs harness, per this session's
    /// established practice for anything that needs the actual pinned Mathlib.
    struct SyntheticMathlib {
        root: std::path::PathBuf,
    }
    impl SyntheticMathlib {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!("chatdb_test_mathlib_{}", Uuid::new_v4()));
            let mathlib_dir = root.join(".lake").join("packages").join("mathlib").join("Mathlib").join("Algebra").join("Group");
            std::fs::create_dir_all(&mathlib_dir).unwrap();
            std::fs::write(mathlib_dir.join("Basic.lean"), concat!(
                "-- synthetic fixture, not real Mathlib\n",
                "theorem add_comm_synthetic (a b : Nat) : a + b = b + a := by ring\n",
                "\n",
                "lemma add_comm_synthetic_helper (a b : Nat) : a + b = b + a := add_comm_synthetic a b\n",
                "\n",
                "def not_a_theorem_like_prefix (n : Nat) : Nat := n\n",
                "\n",
                "protected theorem protected_synthetic_decl (a : Nat) : a = a := rfl\n",
                "\n",
                "@[simp] theorem attribute_prefixed_synthetic_decl (a : Nat) : a = a := rfl\n",
                "\n",
                "private noncomputable def stacked_modifier_synthetic_decl (n : Nat) : Nat := n\n",
            )).unwrap();
            SyntheticMathlib { root }
        }
    }
    impl Drop for SyntheticMathlib {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.root);
        }
    }

    /// Regression test for a real bug found via playtest.rs against the
    /// actual Mathlib source (not caught by the ASCII-only synthetic-tree
    /// test above): `extract_declaration_name` used to count characters but
    /// slice bytes, panicking on any declaration name containing a
    /// multi-byte Unicode character (e.g. Mathlib's `cast_add_comm`-adjacent
    /// forms reference `ℕ`/`α` nearby, and some real names carry subscripts
    /// like `₂`). A panic inside the tokio-spawned server task silently
    /// killed it, which looked like an indefinite hang to any client
    /// awaiting a response — not a clean error. This test exercises the
    /// exact multi-byte case directly, without needing the real 111MB
    /// Mathlib checkout.
    #[test]
    fn test_extract_declaration_name_handles_multibyte_unicode() {
        assert_eq!(extract_declaration_name("theorem foo₂ (n : Nat)", "theorem"), Some("foo₂"));
        assert_eq!(extract_declaration_name("theorem α_comm : True", "theorem"), Some("α_comm"));
        assert_eq!(extract_declaration_name("def bar' (x : α) : Nat", "def"), Some("bar'"));
    }

    #[tokio::test]
    async fn test_mathlib_search_declarations_unavailable_without_lean_checker() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
            "query": "add_comm",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(res["mathlib_available"], false, "{:?}", res);
        assert_eq!(res["hits"].as_array().unwrap().len(), 0);
    }

    #[tokio::test]
    async fn test_mathlib_search_declarations_scans_synthetic_tree() {
        let synthetic = SyntheticMathlib::new();
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let handler = ChatDbMcp {
            conn: Arc::new(Mutex::new(conn)),
            gateway: Box::new(MockGateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: synthetic.root.clone(),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
            "query": "add_comm_synthetic",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(res["mathlib_available"], true, "{:?}", res);
        let hits = res["hits"].as_array().unwrap();
        assert_eq!(hits.len(), 2, "{:?}", hits);
        // Exact match ranked first (shorter/exact name before the longer helper).
        assert_eq!(hits[0]["declaration_name"], "add_comm_synthetic");
        assert_eq!(hits[0]["confidence"], "exact_match");
        assert_eq!(hits[0]["keyword"], "theorem");
        assert_eq!(hits[0]["import_module"], "Mathlib.Algebra.Group.Basic");
        assert!(hits[0]["signature_snippet"].as_str().unwrap().contains("add_comm_synthetic"));
        assert_eq!(hits[1]["declaration_name"], "add_comm_synthetic_helper");
        assert_eq!(hits[1]["confidence"], "nearby_name");

        // A `def` whose NAME happens to contain the word "theorem" must still
        // be found correctly by name, and reported with keyword "def" (the
        // keyword actually starting its line), not confused with "theorem".
        let res2 = tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
            "query": "not_a_theorem_like_prefix",
        }).as_object().unwrap().clone())).await.unwrap());
        let hits2 = res2["hits"].as_array().unwrap();
        assert_eq!(hits2.len(), 1, "{:?}", hits2);
        assert_eq!(hits2[0]["declaration_name"], "not_a_theorem_like_prefix");
        assert_eq!(hits2[0]["keyword"], "def");

        // Found via real end-to-end testing against actual Mathlib: a dotted
        // query (the form a declaration is REFERENCED by, not written) must
        // still find the file-local name.
        let res3 = tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
            "query": "Foo.Bar.add_comm_synthetic",
        }).as_object().unwrap().clone())).await.unwrap());
        let hits3 = res3["hits"].as_array().unwrap();
        assert!(hits3.iter().any(|h| h["declaration_name"] == "add_comm_synthetic"), "{:?}", hits3);
    }

    /// Self-review finding: a modifier (`protected`/`private noncomputable`)
    /// or attribute (`@[simp]`) preceding a declaration keyword on the SAME
    /// line used to make it entirely invisible — confirmed against the real
    /// Mathlib checkout to affect ~80% of files. Each case here must still be
    /// found, reported under the REAL keyword (not the modifier/attribute),
    /// with the original (unstripped) line as its signature_snippet.
    #[tokio::test]
    async fn test_mathlib_search_declarations_sees_past_modifiers_and_attributes() {
        let synthetic = SyntheticMathlib::new();
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let handler = ChatDbMcp {
            conn: Arc::new(Mutex::new(conn)),
            gateway: Box::new(MockGateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: synthetic.root.clone(),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let cases = [
            ("protected_synthetic_decl", "theorem", "protected theorem protected_synthetic_decl"),
            ("attribute_prefixed_synthetic_decl", "theorem", "@[simp] theorem attribute_prefixed_synthetic_decl"),
            ("stacked_modifier_synthetic_decl", "def", "private noncomputable def stacked_modifier_synthetic_decl"),
        ];
        for (name, expected_keyword, expected_snippet_prefix) in cases {
            let res = tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
                "query": name,
            }).as_object().unwrap().clone())).await.unwrap());
            let hits = res["hits"].as_array().unwrap();
            assert_eq!(hits.len(), 1, "{} not found: {:?}", name, hits);
            assert_eq!(hits[0]["declaration_name"], name);
            assert_eq!(hits[0]["keyword"], expected_keyword, "{} must be reported under its real keyword, not the modifier/attribute", name);
            assert!(hits[0]["signature_snippet"].as_str().unwrap().starts_with(expected_snippet_prefix),
                "{}: snippet should keep the original modifier/attribute visible: {:?}", name, hits[0]["signature_snippet"]);
        }
    }

    /// Self-review finding: a dotted query that strips to an EMPTY segment
    /// (e.g. a trailing dot) used to match every declaration name instead of
    /// falling back to a safe (typically empty-result) search.
    #[tokio::test]
    async fn test_mathlib_search_declarations_trailing_dot_query_does_not_match_everything() {
        let synthetic = SyntheticMathlib::new();
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let handler = ChatDbMcp {
            conn: Arc::new(Mutex::new(conn)),
            gateway: Box::new(MockGateway),
            lean_available: false,
            lean_environment: None,
            lean_project_path: synthetic.root.clone(),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
            "query": "Nat.",
        }).as_object().unwrap().clone())).await.unwrap());
        let hits = res["hits"].as_array().unwrap();
        assert_eq!(hits.len(), 0, "a trailing-dot query must not degrade into a match-everything scan: {:?}", hits);
    }

    #[tokio::test]
    async fn test_mathlib_search_declarations_rejects_empty_query() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let res = peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
            "query": "   ",
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err());
    }

    #[tokio::test]
    async fn test_mathlib_search_local_artifacts_finds_verified_module_declarations() {
        // NOTE: attested_module_step (used elsewhere) spins up its OWN
        // isolated in-memory handler internally and returns only the JSON
        // result — it shares no state with any outer client/peer. This test
        // needs the verified module to land in the SAME database it searches
        // afterward, so it drives problem_create -> episode_create ->
        // attempt_claim -> episode_step directly against one shared peer.
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "local artifact search fixture", "root_formal_statement": "myUniqueSearchTarget 2 = 4",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "librarian-local-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();
        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {
                "type": "submit_module",
                "module_items": [
                    {"item_kind": "def", "name": "myUniqueSearchTarget", "type_signature": "Nat → Nat", "body": "fun n => n * n"}
                ],
                "root_theorem": {"name": "root", "statement": "myUniqueSearchTarget 2 = 4", "proof_term": "rfl"}
            },
            "cost_micros": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["outcome"], "kernel_verified", "{:?}", step);

        let res = tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_local_artifacts").with_arguments(serde_json::json!({
            "query": "myUniqueSearchTarget",
        }).as_object().unwrap().clone())).await.unwrap());
        let hits = res["hits"].as_array().unwrap();
        assert_eq!(hits.len(), 1, "{:?}", hits);
        assert_eq!(hits[0]["declaration_name"], "myUniqueSearchTarget");
        assert_eq!(hits[0]["confidence"], "usage_example");
    }

    #[tokio::test]
    async fn test_formalization_plan_attach_librarian_result_maps_confidence_and_accumulates_candidates() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan F",
        }).as_object().unwrap().clone())).await.unwrap());
        let plan_id = plan["plan_id"].as_str().unwrap().to_string();
        let item = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
            "plan_id": plan_id, "kind": "missing_lemma", "description": "need a sum-of-squares identity",
        }).as_object().unwrap().clone())).await.unwrap());
        let item_id = item["plan_item_id"].as_str().unwrap().to_string();

        let attached1 = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_attach_librarian_result").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "declaration_name": "Finset.sum_sq_le_sq_mul_sq", "confidence": "nearby_name",
            "import_module": "Mathlib.Analysis.MeanInequalities",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(attached1["mathlib_coverage_status"], "partial");
        assert_eq!(attached1["mathlib_candidate_names"].as_array().unwrap().len(), 1);

        let attached2 = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_attach_librarian_result").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "declaration_name": "Finset.sq_sum_le_card_mul_sum_sq", "confidence": "exact_match",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(attached2["mathlib_coverage_status"], "found", "a later exact_match must update coverage_status");
        assert_eq!(attached2["mathlib_candidate_names"].as_array().unwrap().len(), 2, "candidates must accumulate, not overwrite");

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_observe").with_arguments(serde_json::json!({
            "plan_id": plan_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let observed_item = &observed["items"][0];
        assert_eq!(observed_item["mathlib_coverage_status"], "found");
        assert_eq!(observed_item["lookup_result"]["source"], "librarian");
        assert_eq!(observed_item["lookup_result"]["declaration_name"], "Finset.sq_sum_le_card_mul_sum_sq");
    }

    #[tokio::test]
    async fn test_formalization_plan_attach_librarian_result_rejects_non_open_item() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp { conn: conn_arc.clone(), gateway: Box::new(MockGateway), lean_available: false, lean_environment: None, lean_project_path: PathBuf::from("dummy") };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let request_id = req["id"].as_str().unwrap().to_string();
        let revision = req["episode_revision"].as_i64().unwrap();
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": request_id,
            "idempotency_key": "librarian-reject-1", "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        let attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();
        let claim_token = claim["claim_token"].as_str().unwrap().to_string();
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": attempt_id,
            "expected_revision": revision, "claim_token": claim_token,
            "action": {"type": "decompose", "sub_lemmas": ["a helper lemma"]},
            "cost_micros": 10,
        }).as_object().unwrap().clone())).await.unwrap());
        let obligation_id: String = { let c = conn_arc.lock().await; c.query_row(
            "SELECT id FROM episode_obligations WHERE episode_id = ?1 AND created_by = 'decomposition' ORDER BY created_at DESC LIMIT 1",
            [&episode_id], |row| row.get(0),
        ).unwrap() };

        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan G",
        }).as_object().unwrap().clone())).await.unwrap());
        let item = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
            "plan_id": plan["plan_id"], "kind": "missing_lemma", "description": "a helper lemma",
        }).as_object().unwrap().clone())).await.unwrap());
        let item_id = item["plan_item_id"].as_str().unwrap().to_string();
        tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_promote_item_to_obligation").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "episode_id": episode_id, "obligation_id": obligation_id,
        }).as_object().unwrap().clone())).await.unwrap());

        let res = peer.call_tool(CallToolRequestParams::new("formalization_plan_attach_librarian_result").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "declaration_name": "whatever", "confidence": "exact_match",
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "attaching a librarian result to an already-promoted item must be rejected");
    }

    /// Issue #25's core regression test: a librarian suggestion — search
    /// results or an attached result — must never change proof/fidelity/
    /// certification status. Snapshots every column of episodes and
    /// episode_obligations before and after exercising every librarian tool,
    /// asserting byte-identical.
    #[tokio::test]
    async fn test_librarian_suggestion_cannot_change_proof_status() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp { conn: conn_arc.clone(), gateway: Box::new(MockGateway), lean_available: false, lean_environment: None, lean_project_path: PathBuf::from("dummy") };
        let client = connected_client(handler).await;
        let peer = client.peer();

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let _episode_id = ep["episode_id"].as_str().unwrap().to_string(); // exists only so the snapshot below has a non-empty episodes table row
        let plan = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "title": "Plan H",
        }).as_object().unwrap().clone())).await.unwrap());
        let item = tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_add_item").with_arguments(serde_json::json!({
            "plan_id": plan["plan_id"], "kind": "missing_lemma", "description": "x",
        }).as_object().unwrap().clone())).await.unwrap());
        let item_id = item["plan_item_id"].as_str().unwrap().to_string();

        let snapshot = |conn: &Connection| -> (String, String) {
            let episodes: Vec<String> = conn.prepare("SELECT * FROM episodes ORDER BY id").unwrap()
                .query_map([], |row| { let n = row.as_ref().column_count(); Ok((0..n).map(|i| format!("{:?}", row.get_ref(i).unwrap())).collect::<Vec<_>>().join(",")) }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            let obligations: Vec<String> = conn.prepare("SELECT * FROM episode_obligations ORDER BY id").unwrap()
                .query_map([], |row| { let n = row.as_ref().column_count(); Ok((0..n).map(|i| format!("{:?}", row.get_ref(i).unwrap())).collect::<Vec<_>>().join(",")) }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            (episodes.join("|"), obligations.join("|"))
        };
        let before = { let c = conn_arc.lock().await; snapshot(&c) };

        tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_declarations").with_arguments(serde_json::json!({
            "query": "add_comm",
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("mathlib_search_local_artifacts").with_arguments(serde_json::json!({
            "query": "root",
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("formalization_plan_attach_librarian_result").with_arguments(serde_json::json!({
            "plan_item_id": item_id, "declaration_name": "Nat.add_comm", "confidence": "exact_match",
        }).as_object().unwrap().clone())).await.unwrap());

        let after = { let c = conn_arc.lock().await; snapshot(&c) };
        assert_eq!(before, after, "no librarian tool call may change episodes or episode_obligations in any way");
    }
}
