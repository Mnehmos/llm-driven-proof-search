// environment_describe's tool_classification field is one large nested
// serde_json::json! literal (issue #34's audit data) that exceeds the
// default macro recursion limit.
#![recursion_limit = "512"]

use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;
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
use chatdb_proof_core::orchestrator::{lifecycle, attempts, step, trajectories, dataset};
use chatdb_proof_core::lean::{LeanGateway, RealLeanGateway};
use chatdb_proof_core::models::action::{TypedAction, ActionRequest, ActionRole, StepDisposition, LeanModuleItem, ModuleTheorem};
use chatdb_proof_core::lean::module::assemble_module;
use chatdb_proof_core::models::episode::{EpisodeOutcome, TerminationReason, TruncationReason};
use chatdb_proof_core::models::reward::{RewardComponent, RewardComponentId, RewardPolicy};
use chatdb_proof_core::hashing::canonical_hash;
use chatdb_proof_core::putnambench::to_pi_form;

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

/// Issue #35's dedicated read-me-first tool — no args, matching
/// EnvironmentDescribeArgs, since its whole point is to be the first,
/// zero-friction call any agent host makes before creating an episode.
#[derive(JsonSchema, Deserialize)]
pub struct ReadmeFirstArgs {}

// -- Run envelopes (issues #34 core concept + #38 cost surfaces) ----------
//
// Purely descriptive metadata layered over episodes: which host/model/mode
// produced a set of episodes, and host-side cost ChatDB itself cannot
// observe. Reuses `episodes.run_id` -- a column already present in the
// schema from the original pre-SubmitModule spec but never read or written
// by any code anywhere (confirmed via search before reusing it) -- as the
// link to a run_envelopes row, rather than adding a redundant new column.
// Deliberately NOT a DB-level foreign key: `run_id` predates this feature as
// a free-text column, and retrofitting a FK constraint onto it would need
// the full create-copy-drop-rename migration this codebase reserves for
// CHECK-constraint changes (see schema_v1.rs's migrate_* functions) for a
// benefit (referential integrity on a field nothing else ever wrote) that
// doesn't justify that cost — validated at the application layer instead
// (run_envelope_attach_episode checks both ids exist before writing).

#[derive(JsonSchema, Deserialize)]
pub enum RunEnvelopeMode {
    #[serde(rename = "development")] Development,
    #[serde(rename = "evaluation")] Evaluation,
    #[serde(rename = "benchmark")] Benchmark,
    #[serde(rename = "private_audit")] PrivateAudit,
    #[serde(rename = "public_report")] PublicReport,
}

#[derive(JsonSchema, Deserialize)]
pub enum HostCostConfidence {
    #[serde(rename = "exact_provider_receipt")] ExactProviderReceipt,
    #[serde(rename = "exact_local_meter")] ExactLocalMeter,
    #[serde(rename = "estimated")] Estimated,
    #[serde(rename = "attested")] Attested,
    #[serde(rename = "unknown")] Unknown,
}

#[derive(JsonSchema, Deserialize)]
pub struct RunEnvelopeCreateArgs {
    pub mode: RunEnvelopeMode,
    /// Free text naming the calling agent host, e.g. "Claude Code", "Codex".
    #[serde(default)]
    pub host_name: Option<String>,
    #[serde(default)]
    pub host_model: Option<String>,
    /// e.g. "PutnamBench" for a benchmark-mode run. Free text, not validated
    /// against any registry.
    #[serde(default)]
    pub benchmark_suite_name: Option<String>,
    #[serde(default)]
    pub host_side_cost_micros: Option<i64>,
    /// Defaults to "unknown" — the honest default when the caller hasn't
    /// measured or attested any host-side cost yet.
    #[serde(default)]
    pub host_cost_confidence: Option<HostCostConfidence>,
    #[serde(default)]
    pub notes: Option<String>,
}

/// Self-review note: an omitted field and an explicit JSON `null` are
/// indistinguishable here (both deserialize to `None` and are treated as
/// "leave unchanged") — there's currently no way to intentionally reset a
/// field back to NULL/unknown once set. Same limitation as
/// FormalizationPlanUpdateArgs's identical pattern; accepted for the same
/// reason: no acceptance criterion calls for a reset path, and adding one
/// would need a three-state (unset/reset/set) representation for no
/// currently-needed benefit.
#[derive(JsonSchema, Deserialize)]
pub struct RunEnvelopeUpdateArgs {
    pub run_envelope_id: String,
    #[serde(default)]
    pub host_side_cost_micros: Option<i64>,
    #[serde(default)]
    pub host_cost_confidence: Option<HostCostConfidence>,
    #[serde(default)]
    pub notes: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct RunEnvelopeAttachEpisodeArgs {
    pub run_envelope_id: String,
    pub episode_id: String,
    /// Required (true) to attach an episode built from an
    /// unsafe_dev_attestation ("attested", never independently reviewed)
    /// problem to a `private_audit`-mode run envelope. Has NO effect for
    /// `benchmark`/`evaluation`/`public_report` modes — those always reject
    /// an attested-problem episode outright, no override possible. That flag
    /// means development playtest; it must never leak into a measured
    /// benchmark/evaluation/public claim (issue #38's mode-enforcement policy).
    #[serde(default)]
    pub allow_dev_attested: bool,
}

#[derive(JsonSchema, Deserialize)]
pub struct RunEnvelopeObserveArgs {
    pub run_envelope_id: String,
}

// -- PutnamBench benchmark schema (issues #29, #30) ------------------------
//
// benchmark_suite_create/benchmark_problem_register are MANUAL/structured
// registration only — no Lean-file parsing. The real importer (issue #29:
// automatically extracting theorem name/imports/statement from a real
// PutnamBench checkout) is a separate, not-yet-built piece; these tools are
// what it will call once it exists, and are independently useful for
// hand-registering a problem in the meantime.

#[derive(JsonSchema, Deserialize)]
pub struct BenchmarkSuiteCreateArgs {
    pub name: String,
    #[serde(default)]
    pub upstream_url: Option<String>,
    #[serde(default)]
    pub upstream_commit: Option<String>,
    #[serde(default = "default_benchmark_language")]
    pub language: String,
    /// An honest, self-declared trust assertion (issue #38's fidelity-basis
    /// policy): set true ONLY for a suite you can vouch is a real,
    /// externally-curated benchmark corpus (e.g. PutnamBench) whose own
    /// registered root_formal_statement is itself sufficient fidelity
    /// evidence — a statement-hash match against such a suite is accepted
    /// by benchmark_result_record as fidelity basis for a kernel_verified/
    /// certified claim WITHOUT requiring a separate problem_submit_fidelity_review.
    /// ChatDB never independently verifies this claim, exactly like
    /// unsafe_dev_attestation/host_cost_confidence elsewhere — defaults to
    /// false so an arbitrary custom suite can never silently gain this
    /// treatment.
    #[serde(default)]
    pub trusted_canonical_source: bool,
}
fn default_benchmark_language() -> String { "Lean4".to_string() }

#[derive(JsonSchema, Deserialize)]
pub struct BenchmarkProblemRegisterArgs {
    pub suite_id: String,
    /// The problem's own identifier in the upstream suite (e.g. PutnamBench's
    /// own problem numbering), NOT a ChatDB-generated id.
    pub upstream_problem_id: String,
    pub theorem_name: String,
    #[serde(default)]
    pub source_file_path: Option<String>,
    /// The exact, unmodified formal statement from the upstream suite. The
    /// server computes root_statement_hash from this (never accepted from
    /// the client) — same principle as problem_create's own root statement
    /// hash.
    pub root_formal_statement: String,
    #[serde(default)]
    pub import_manifest: Vec<String>,
    #[serde(default)]
    pub context_hash: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub enum BenchmarkSolveMode {
    #[serde(rename = "solve_only")] SolveOnly,
    #[serde(rename = "submit_module_allowed")] SubmitModuleAllowed,
    #[serde(rename = "submit_module_plus_draft_planning")] SubmitModulePlusDraftPlanning,
    #[serde(rename = "submit_module_plus_librarian")] SubmitModulePlusLibrarian,
}

#[derive(JsonSchema, Deserialize)]
pub struct BenchmarkRunCreateArgs {
    pub suite_id: String,
    /// Required (issue #34): "a benchmark run should not start unless a
    /// run envelope exists." Call run_envelope_create first.
    pub run_envelope_id: String,
    #[serde(default)]
    pub chatdb_commit: Option<String>,
    pub solve_mode: BenchmarkSolveMode,
    #[serde(default)]
    pub allowed_tools: Vec<String>,
    pub attempt_budget: i64,
    #[serde(default)]
    pub wall_clock_budget_ms: Option<i64>,
    #[serde(default)]
    pub lean_timeout_ms: Option<i64>,
}

#[derive(JsonSchema, Deserialize)]
pub enum BenchmarkResultStatus {
    #[serde(rename = "kernel_verified")] KernelVerified,
    #[serde(rename = "certified")] Certified,
    #[serde(rename = "failed")] Failed,
    #[serde(rename = "timeout")] Timeout,
    #[serde(rename = "infra_error")] InfraError,
    #[serde(rename = "formalization_gap")] FormalizationGap,
    #[serde(rename = "skipped")] Skipped,
}

#[derive(JsonSchema, Deserialize)]
pub struct BenchmarkResultRecordArgs {
    pub run_id: String,
    pub benchmark_problem_id: String,
    #[serde(default)]
    pub problem_version_id: Option<String>,
    /// When given, cross-checked against that episode's ACTUAL recorded
    /// outcome (issue #36) — a result claiming "kernel_verified"/"certified"
    /// must match the referenced episode's real outcome exactly, and any
    /// referenced episode must have actually concluded (outcome set). A
    /// benchmark result cannot claim an outcome the ledger doesn't back.
    #[serde(default)]
    pub episode_id: Option<String>,
    pub status: BenchmarkResultStatus,
    #[serde(default)]
    pub outcome: Option<String>,
    #[serde(default)]
    pub pass_at: Option<i64>,
    /// Required (no default) — a benchmark result without a reported attempt
    /// count is exactly the kind of unmeasured claim this schema exists to
    /// prevent.
    pub attempts_used: i64,
    #[serde(default)]
    pub time_to_first_success_ms: Option<i64>,
    #[serde(default)]
    pub cost_micros: Option<i64>,
    #[serde(default)]
    pub final_diagnostic_category: Option<String>,
    #[serde(default)]
    pub proof_artifact_hash: Option<String>,
    #[serde(default)]
    pub trajectory_export_hash: Option<String>,
    #[serde(default)]
    pub replay_status: Option<String>,
    /// Silences the mode-enforcement rejection for an unsafe_dev_attestation
    /// ("attested") problem claim when this run's envelope mode is
    /// `private_audit` — but does NOT by itself make such a claim succeed
    /// for an UNTRUSTED suite: the separate, pre-existing fidelity-basis
    /// policy still independently rejects an "attested" (not "verified")
    /// problem's kernel_verified/certified claim against an untrusted suite
    /// regardless of this flag, in every mode including private_audit — an
    /// adversarial review of this exact flag caught that its original doc
    /// comment overclaimed here. In practice this flag only changes which of
    /// the two rejection messages you see for an untrusted suite; it has a
    /// real effect only for a TRUSTED suite in private_audit mode (where the
    /// fidelity-basis policy already accepts the claim via
    /// canonical_statement_hash_match regardless of mode, so this flag's
    /// mode-enforcement check is the only thing that could otherwise block
    /// it). Making this flag genuinely bypass the fidelity-basis rejection
    /// for an untrusted suite would need a real design decision (e.g. a
    /// fifth benchmark_fidelity_basis value for an explicitly-supervised
    /// private-audit override) — left undecided rather than guessed at.
    #[serde(default)]
    pub allow_dev_attested: bool,
}

#[derive(JsonSchema, Deserialize)]
pub struct BenchmarkRunObserveArgs {
    pub run_id: String,
}

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
    /// Required (true) when this episode's problem is linked to a tracked
    /// benchmark suite (e.g. PutnamBench). Every event's raw `payload_json` —
    /// including a `solve` action's `proof_term` or a `submit_module`
    /// action's `module_items` — is exactly the completed-proof-body content
    /// issue #33's contamination policy gates in `proof_export`; without this
    /// flag, trajectory_export would otherwise be an ungated side channel
    /// around that same policy. See docs/benchmarks/putnambench.md.
    #[serde(default)]
    pub allow_putnambench_proof_export: bool,
}

#[derive(JsonSchema, Deserialize)]
pub struct EpisodeReplayArgs {
    pub episode_id: String,
}

#[derive(JsonSchema, Deserialize, PartialEq, Eq, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum ExportMode {
    /// Full human-readable dossier: proof tree, assembled Lean source, attempt
    /// history, integrity line. Includes the completed proof body. (default)
    Markdown,
    /// Bare assembled Lean source only, ready to paste into a Mathlib project.
    /// Includes the completed proof body.
    Lean,
    /// Redacted report safe for public disclosure: status, hashes, toolchain,
    /// integrity, and — if this episode's problem is linked to a tracked
    /// benchmark suite — suite/problem identification. NEVER includes the
    /// completed proof body, proof tree detail, or attempt content, regardless
    /// of `allow_putnambench_proof_export`.
    PublicSummary,
    /// Everything `markdown` has (full proof source, every attempt including
    /// failures, verifier diagnostics), explicitly labeled as a private audit
    /// artifact not meant for public disclosure.
    AuditArchive,
    /// Structured per-step (state, action, reward, next_state, terminated,
    /// truncated, metadata) records suitable for SFT/RL/DPO training pipelines,
    /// as a JSON array. Secrets (api_key, auth_token, credentials,
    /// private_endpoint) are scrubbed; proof/tactic content is not.
    TrainingExport,
    /// Human-readable mathematical report: everything `audit_archive` has, plus
    /// a written narrative section (proof strategy, key lemmas, unresolved
    /// gaps) rather than only tables.
    PaperDossier,
    /// Same tier of content as `audit_archive`, packaged for private
    /// communication with a benchmark suite's own maintainers — includes suite/
    /// problem identification and an explicit non-public-disclosure notice.
    MaintainerSubmission,
}

impl ExportMode {
    /// Whether this mode's rendered output can contain the completed proof
    /// body (assembled Lean source, per-step proof/tactic terms, or verified
    /// module source) — the thing issue #33's contamination policy gates.
    fn exposes_proof_body(self) -> bool {
        matches!(self, ExportMode::Markdown | ExportMode::Lean | ExportMode::AuditArchive
            | ExportMode::TrainingExport | ExportMode::PaperDossier | ExportMode::MaintainerSubmission)
    }
}

#[derive(JsonSchema, Deserialize)]
pub struct ProofExportArgs {
    pub episode_id: String,
    #[serde(default)]
    pub format: Option<ExportMode>,
    /// Required (true) when this episode's problem is linked to a tracked
    /// benchmark suite (e.g. PutnamBench) AND `format` is a mode that exposes
    /// the completed proof body. Upstream benchmark maintainers ask that
    /// completed formal proofs not be published without first engaging with
    /// them, to avoid contaminating the public benchmark corpus — see
    /// docs/benchmarks/putnambench.md. Has no effect for `public_summary`,
    /// which never exposes a proof body regardless of this flag.
    #[serde(default)]
    pub allow_putnambench_proof_export: bool,
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

// -- Level 4 research substrate (issues #9, #11, #13) ----------------------
//
// Research dossiers, citations, assumptions, and verification layers are
// explicit trust-boundary metadata. They can reference Lean-backed artifacts,
// but they never create proof authority themselves and never write to episode
// outcome, obligations, canonical lemmas, budgets, fidelity reviews, or
// benchmark result tables.

#[derive(JsonSchema, Deserialize)]
pub struct ResearchDossierCreateArgs {
    pub title: String,
    #[serde(default)]
    pub description: Option<String>,
    #[serde(default)]
    pub problem_version_id: Option<String>,
    #[serde(default)]
    pub episode_id: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct ResearchDossierObserveArgs {
    pub dossier_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct ResearchNodeAddArgs {
    pub dossier_id: String,
    #[serde(default)]
    pub section_id: Option<String>,
    #[serde(default)]
    pub section_title: Option<String>,
    pub node_type: String,
    pub title: String,
    #[serde(default)]
    pub statement: Option<String>,
    #[serde(default)]
    pub content: Option<String>,
    #[serde(default)]
    pub trust_status: Option<String>,
    #[serde(default)]
    pub linked_obligation_id: Option<String>,
    #[serde(default)]
    pub linked_verified_lemma_id: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct ExternalReferenceAddArgs {
    pub dossier_id: String,
    pub title: String,
    #[serde(default)]
    pub authors: Option<String>,
    #[serde(default)]
    pub venue: Option<String>,
    #[serde(default)]
    pub year: Option<String>,
    #[serde(default)]
    pub url: Option<String>,
    #[serde(default)]
    pub doi: Option<String>,
    #[serde(default)]
    pub raw_citation: Option<String>,
    #[serde(default)]
    pub theorem_label: Option<String>,
    #[serde(default)]
    pub theorem_statement: Option<String>,
    #[serde(default)]
    pub claim_status: Option<String>,
    #[serde(default)]
    pub mathlib_name: Option<String>,
    #[serde(default)]
    pub proved_episode_id: Option<String>,
    #[serde(default)]
    pub proved_lemma_id: Option<String>,
    #[serde(default)]
    pub notes: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct AssumptionBoundaryAddArgs {
    pub dossier_id: String,
    #[serde(default)]
    pub node_id: Option<String>,
    pub label: String,
    pub statement: String,
    pub assumption_status: String,
    #[serde(default)]
    pub rationale: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct CitationReviewAddArgs {
    pub dossier_id: String,
    pub external_theorem_claim_id: String,
    pub reviewer_id: String,
    pub decision: String,
    #[serde(default)]
    pub notes: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct VerificationLayerSetArgs {
    pub dossier_id: String,
    pub target_kind: String,
    pub target_id: String,
    pub layer_kind: String,
    pub status: String,
    #[serde(default)]
    pub summary: Option<String>,
    #[serde(default)]
    pub evidence_json: Option<String>,
}

// -- Candidate construction artifacts (issue #8) ----------------------------
//
// Candidate constructions are proposed mathematical objects -- graph
// families, colorings, point configurations, counterexamples, and so on --
// that can exist before a research dossier is written up, before a Lean
// theorem exists, before an episode exists, and before issue #26's empirical
// math lab exists to generate/test/rank/falsify them. They are research
// artifacts: useful for search and planning, never proof certificates.
// Empirical support, human review, citation, and "a formal statement exists"
// are all explicitly distinct from kernel verification.

#[derive(JsonSchema, Deserialize)]
pub struct CandidateConstructionAddArgs {
    #[serde(default)]
    pub dossier_id: Option<String>,
    #[serde(default)]
    pub related_node_id: Option<String>,
    #[serde(default)]
    pub verification_layer_id: Option<String>,
    pub construction_type: String,
    pub informal_description: String,
    #[serde(default)]
    pub parameters_json: Option<String>,
    #[serde(default)]
    pub claimed_properties_json: Option<String>,
    #[serde(default)]
    pub known_failures_json: Option<String>,
    #[serde(default)]
    pub empirical_checks_json: Option<String>,
    #[serde(default)]
    pub status: Option<String>,
    #[serde(default)]
    pub trust_status: Option<String>,
    pub created_by: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct CandidateConstructionObserveArgs {
    pub candidate_construction_id: String,
    pub description: String,
    pub result: String,
    #[serde(default)]
    pub details_json: Option<String>,
    #[serde(default)]
    pub observed_by: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct CandidateConstructionUpdateStatusArgs {
    pub candidate_construction_id: String,
    #[serde(default)]
    pub status: Option<String>,
    #[serde(default)]
    pub trust_status: Option<String>,
    #[serde(default)]
    pub claimed_properties_json: Option<String>,
    #[serde(default)]
    pub known_failures_json: Option<String>,
}

#[derive(JsonSchema, Deserialize)]
pub struct CandidateConstructionLinkNodeArgs {
    pub candidate_construction_id: String,
    pub node_id: String,
}

#[derive(JsonSchema, Deserialize)]
pub struct CandidateConstructionLinkVerificationLayerArgs {
    pub candidate_construction_id: String,
    pub verification_layer_id: String,
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

fn reserve_episode_budget_for_model_call(
    tx: &Transaction,
    episode_id: &str,
    reserved_cost_micros: i64,
) -> Result<(), McpError> {
    if reserved_cost_micros < 0 {
        return Err(mcp_invalid_params("invalid_cost: reserved_cost_micros must be >= 0"));
    }
    let updated = tx.execute(
        "UPDATE episodes
         SET cost_budget_micros = cost_budget_micros - ?1
         WHERE id = ?2
           AND (cost_budget_micros IS NULL OR cost_budget_micros >= ?1)",
        (reserved_cost_micros, episode_id),
    ).map_err(rs)?;
    if updated == 0 {
        let remaining: Option<i64> = tx.query_row(
            "SELECT cost_budget_micros FROM episodes WHERE id = ?1",
            [episode_id],
            |row| row.get(0),
        ).optional().map_err(rs)?.flatten();
        if let Some(remaining) = remaining {
            return Err(mcp_invalid_params(format!(
                "budget_denied: reserved_cost_micros {} exceeds remaining budget {}",
                reserved_cost_micros, remaining
            )));
        }
        return Err(mcp_invalid_params(format!("unknown episode_id: {}", episode_id)));
    }
    Ok(())
}

fn refund_episode_budget(tx: &Transaction, episode_id: &str, amount_micros: i64) -> Result<(), McpError> {
    if amount_micros < 0 {
        return Err(mcp_invalid_params("invalid_cost: refund amount must be >= 0"));
    }
    tx.execute(
        "UPDATE episodes SET cost_budget_micros = cost_budget_micros + ?1 WHERE id = ?2",
        (amount_micros, episode_id),
    ).map_err(rs)?;
    Ok(())
}

fn settle_model_call_lease(
    tx: &Transaction,
    lease_id: &str,
    actual_cost_micros: i64,
    status: &str,
) -> Result<(), McpError> {
    if actual_cost_micros < 0 {
        return Err(mcp_invalid_params("invalid_cost: actual_cost_micros must be >= 0"));
    }
    if !matches!(status, "settled" | "voided") {
        return Err(mcp_invalid_params("status must be 'settled' or 'voided'"));
    }

    let lease: Option<(String, String, i64)> = tx.query_row(
        "SELECT episode_id, status, reserved_cost_micros FROM model_call_leases WHERE id = ?1",
        [lease_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
    ).optional().map_err(rs)?;

    let Some((episode_id, lease_status, reserved_cost_micros)) = lease else {
        return Err(mcp_invalid_params(format!("unknown lease_id: {}", lease_id)));
    };
    if lease_status != "reserved" {
        return Err(mcp_invalid_params(format!("lease {} is already {}", lease_id, lease_status)));
    }
    if reserved_cost_micros < 0 {
        return Err(mcp_invalid_params("invalid_cost: reserved_cost_micros must be >= 0"));
    }

    if status == "settled" {
        let delta = actual_cost_micros - reserved_cost_micros;
        if delta > 0 {
            reserve_episode_budget_for_model_call(tx, &episode_id, delta)?;
        } else if delta < 0 {
            refund_episode_budget(tx, &episode_id, -delta)?;
        }

        tx.execute(
            "UPDATE model_call_leases
             SET status = 'settled', actual_cost_micros = ?1, settled_at = ?2
             WHERE id = ?3",
            (actual_cost_micros, Utc::now().to_rfc3339(), lease_id),
        ).map_err(rs)?;
    } else {
        refund_episode_budget(tx, &episode_id, reserved_cost_micros)?;
        tx.execute(
            "UPDATE model_call_leases
             SET status = 'voided', actual_cost_micros = NULL, settled_at = ?1
             WHERE id = ?2",
            (Utc::now().to_rfc3339(), lease_id),
        ).map_err(rs)?;
    }

    Ok(())
}

fn settle_reserved_model_call_leases_for_attempt(
    tx: &Transaction,
    episode_id: &str,
    action_attempt_id: &str,
    actual_cost_micros: i64,
) -> Result<(), McpError> {
    let mut stmt = tx.prepare(
        "SELECT id FROM model_call_leases
         WHERE episode_id = ?1 AND action_attempt_id = ?2 AND status = 'reserved'
         ORDER BY created_at ASC, id ASC",
    ).map_err(rs)?;
    let lease_ids: Vec<String> = stmt.query_map((episode_id, action_attempt_id), |row| row.get(0))
        .map_err(rs)?
        .collect::<rusqlite::Result<Vec<_>>>()
        .map_err(rs)?;
    drop(stmt);

    for lease_id in lease_ids {
        settle_model_call_lease(tx, &lease_id, actual_cost_micros, "settled")?;
    }
    Ok(())
}

fn validate_one_of(field: &str, value: &str, allowed: &[&str]) -> Result<(), McpError> {
    if allowed.contains(&value) {
        Ok(())
    } else {
        Err(mcp_invalid_params(format!(
            "{} must be one of: {}",
            field,
            allowed.join(", ")
        )))
    }
}

const RESEARCH_NODE_TYPES: &[&str] = &[
    "definition", "proposition", "lemma", "theorem", "remark", "reference", "open_gap",
];
const RESEARCH_TRUST_STATUSES: &[&str] = &[
    "open_gap",
    "proved_in_episode",
    "imported_from_mathlib",
    "external_citation_unreviewed",
    "external_citation_human_reviewed",
    "unformalized_assumption",
    "rejected_unsafe_assumption",
];
const ASSUMPTION_STATUSES: &[&str] = &["unformalized_assumption", "rejected_unsafe_assumption"];
const CITATION_REVIEW_DECISIONS: &[&str] = &["human_reviewed", "rejected", "needs_formalization"];
const VERIFICATION_TARGET_KINDS: &[&str] = &[
    "dossier", "node", "assumption", "external_theorem_claim", "problem_version", "episode",
];
const VERIFICATION_LAYER_KINDS: &[&str] = &[
    "construction_search",
    "arithmetic_construction",
    "geometric_criterion",
    "packing_or_size_bound",
    "asymptotic_extraction",
    "formal_module",
    "statement_fidelity",
    "external_review",
    "exposition_review",
];
const VERIFICATION_LAYER_STATUSES: &[&str] = &[
    "not_started", "informal", "empirical", "cited", "human_reviewed", "kernel_verified", "failed", "blocked", "rejected",
];

fn require_row_exists(tx: &Transaction, table: &str, id: &str, label: &str) -> Result<(), McpError> {
    let sql = format!("SELECT 1 FROM {} WHERE id = ?1", table);
    let exists: Option<i64> = tx.query_row(&sql, [id], |row| row.get(0)).optional().map_err(rs)?;
    if exists.is_some() {
        Ok(())
    } else {
        Err(mcp_invalid_params(format!("unknown {}: {}", label, id)))
    }
}

fn require_row_in_dossier(tx: &Transaction, table: &str, id: &str, dossier_id: &str, label: &str) -> Result<(), McpError> {
    let sql = format!("SELECT 1 FROM {} WHERE id = ?1 AND dossier_id = ?2", table);
    let exists: Option<i64> = tx.query_row(&sql, (id, dossier_id), |row| row.get(0)).optional().map_err(rs)?;
    if exists.is_some() {
        Ok(())
    } else {
        Err(mcp_invalid_params(format!("unknown {} for dossier: {}", label, id)))
    }
}

fn next_order(tx: &Transaction, table: &str, order_col: &str, dossier_id: &str) -> Result<i64, McpError> {
    let sql = format!("SELECT COALESCE(MAX({}), -1) + 1 FROM {} WHERE dossier_id = ?1", order_col, table);
    tx.query_row(&sql, [dossier_id], |row| row.get(0)).map_err(rs)
}

fn verify_dossier_links(
    tx: &Transaction,
    problem_version_id: &Option<String>,
    episode_id: &Option<String>,
) -> Result<(), McpError> {
    if let Some(problem_version_id) = problem_version_id {
        require_row_exists(tx, "problem_versions", problem_version_id, "problem_version_id")?;
    }
    if let Some(episode_id) = episode_id {
        let episode_pv: Option<String> = tx.query_row(
            "SELECT problem_version_id FROM episodes WHERE id = ?1",
            [episode_id],
            |row| row.get(0),
        ).optional().map_err(rs)?;
        let Some(episode_pv) = episode_pv else {
            return Err(mcp_invalid_params(format!("unknown episode_id: {}", episode_id)));
        };
        if let Some(problem_version_id) = problem_version_id {
            if &episode_pv != problem_version_id {
                return Err(mcp_invalid_params("episode_id does not belong to problem_version_id"));
            }
        }
    }
    Ok(())
}

fn ensure_target_belongs_to_dossier(tx: &Transaction, dossier_id: &str, target_kind: &str, target_id: &str) -> Result<(), McpError> {
    match target_kind {
        "dossier" => {
            if target_id != dossier_id {
                return Err(mcp_invalid_params("target_id must equal dossier_id when target_kind='dossier'"));
            }
            require_row_exists(tx, "research_dossiers", dossier_id, "dossier_id")
        }
        "node" => {
            let row: Option<i64> = tx.query_row(
                "SELECT 1 FROM research_nodes WHERE id = ?1 AND dossier_id = ?2",
                (target_id, dossier_id),
                |row| row.get(0),
            ).optional().map_err(rs)?;
            row.map(|_| ()).ok_or_else(|| mcp_invalid_params(format!("unknown research node for dossier: {}", target_id)))
        }
        "assumption" => {
            let row: Option<i64> = tx.query_row(
                "SELECT 1 FROM assumption_boundaries WHERE id = ?1 AND dossier_id = ?2",
                (target_id, dossier_id),
                |row| row.get(0),
            ).optional().map_err(rs)?;
            row.map(|_| ()).ok_or_else(|| mcp_invalid_params(format!("unknown assumption for dossier: {}", target_id)))
        }
        "external_theorem_claim" => {
            let row: Option<i64> = tx.query_row(
                "SELECT 1 FROM external_theorem_claims WHERE id = ?1 AND dossier_id = ?2",
                (target_id, dossier_id),
                |row| row.get(0),
            ).optional().map_err(rs)?;
            row.map(|_| ()).ok_or_else(|| mcp_invalid_params(format!("unknown external theorem claim for dossier: {}", target_id)))
        }
        "problem_version" => {
            require_row_exists(tx, "problem_versions", target_id, "problem_version_id")
        }
        "episode" => {
            require_row_exists(tx, "episodes", target_id, "episode_id")
        }
        _ => Err(mcp_invalid_params("unknown verification target kind")),
    }
}

fn enforce_kernel_verified_research_boundary(
    tx: &Transaction,
    dossier_id: &str,
    target_kind: &str,
    target_id: &str,
    status: &str,
) -> Result<(), McpError> {
    if status != "kernel_verified" {
        return Ok(());
    }
    match target_kind {
        "node" => {
            let trust_status: String = tx.query_row(
                "SELECT trust_status FROM research_nodes WHERE id = ?1 AND dossier_id = ?2",
                (target_id, dossier_id),
                |row| row.get(0),
            ).map_err(rs)?;
            if trust_status != "proved_in_episode" {
                return Err(mcp_invalid_params("kernel_verified verification layers require a node whose trust_status is proved_in_episode"));
            }
        }
        "external_theorem_claim" => {
            let (claim_status, proved_lemma_id): (String, Option<String>) = tx.query_row(
                "SELECT claim_status, proved_lemma_id FROM external_theorem_claims WHERE id = ?1 AND dossier_id = ?2",
                (target_id, dossier_id),
                |row| Ok((row.get(0)?, row.get(1)?)),
            ).map_err(rs)?;
            if claim_status != "proved_in_episode" || proved_lemma_id.is_none() {
                return Err(mcp_invalid_params("external citations/reviews/assumptions cannot be labeled kernel_verified without a linked proved episode lemma"));
            }
        }
        "assumption" | "dossier" => {
            return Err(mcp_invalid_params("assumptions and whole dossiers cannot be labeled kernel_verified by a verification layer"));
        }
        "episode" => {
            let outcome: Option<String> = tx.query_row(
                "SELECT outcome FROM episodes WHERE id = ?1",
                [target_id],
                |row| row.get(0),
            ).map_err(rs)?;
            if !matches!(outcome.as_deref(), Some("kernel_verified" | "certified")) {
                return Err(mcp_invalid_params("kernel_verified verification layers on episodes require an episode outcome of kernel_verified or certified"));
            }
        }
        "problem_version" => {
            let has_kernel_artifact: Option<i64> = tx.query_row(
                "SELECT 1 FROM canonical_verified_lemmas WHERE problem_version_id = ?1 LIMIT 1",
                [target_id],
                |row| row.get(0),
            ).optional().map_err(rs)?;
            if has_kernel_artifact.is_none() {
                return Err(mcp_invalid_params("kernel_verified verification layers on problem_versions require a canonical verified lemma"));
            }
        }
        _ => return Err(mcp_invalid_params("unknown verification target kind")),
    }
    Ok(())
}

const CANDIDATE_CONSTRUCTION_TYPES: &[&str] = &[
    "graph_family",
    "point_configuration",
    "coloring",
    "field_tower",
    "lattice",
    "counterexample",
    "asymptotic_family",
    "algebraic_object",
    "combinatorial_design",
    "other",
];
const CANDIDATE_CONSTRUCTION_STATUSES: &[&str] = &[
    "proposed",
    "under_review",
    "refined",
    "empirically_supported",
    "falsified",
    "rejected",
    "linked_to_formal_claim",
];
const CANDIDATE_CONSTRUCTION_TRUST_STATUSES: &[&str] = &[
    "informal",
    "empirical_evidence",
    "cited",
    "human_reviewed",
    "formalized_statement_exists",
    "kernel_verified_claim_linked",
];
const CANDIDATE_CONSTRUCTION_OBSERVATION_RESULTS: &[&str] = &["supports", "refutes", "inconclusive"];

const CANDIDATE_CONSTRUCTION_SELECT: &str = "SELECT cc.id, cc.dossier_id, cc.related_node_id, cc.verification_layer_id, \
    cc.construction_type, cc.informal_description, cc.parameters_json, cc.claimed_properties_json, \
    cc.known_failures_json, cc.empirical_checks_json, cc.status, cc.trust_status, cc.created_by, \
    cc.created_at, cc.updated_at, vl.status \
    FROM candidate_constructions cc LEFT JOIN verification_layers vl ON vl.id = cc.verification_layer_id";

/// A candidate construction never mutates proof outcome, so its
/// trust_status='kernel_verified_claim_linked' is the only claim of kernel
/// evidence this table can carry -- and it is accepted only when
/// verification_layer_id names a verification_layers row whose OWN status is
/// already 'kernel_verified' (itself gated by
/// enforce_kernel_verified_research_boundary at the point that layer was
/// set). This mirrors the research_nodes/proved_in_episode pattern: linkage
/// to real evidence, never creation of it.
fn enforce_kernel_verified_construction_boundary(
    tx: &Transaction,
    verification_layer_id: &Option<String>,
    trust_status: &str,
) -> Result<(), McpError> {
    if trust_status != "kernel_verified_claim_linked" {
        return Ok(());
    }
    let Some(verification_layer_id) = verification_layer_id else {
        return Err(mcp_invalid_params("trust_status='kernel_verified_claim_linked' requires verification_layer_id"));
    };
    let layer_status: Option<String> = tx.query_row(
        "SELECT status FROM verification_layers WHERE id = ?1",
        [verification_layer_id],
        |row| row.get(0),
    ).optional().map_err(rs)?;
    match layer_status.as_deref() {
        Some("kernel_verified") => Ok(()),
        Some(_) => Err(mcp_invalid_params("trust_status='kernel_verified_claim_linked' requires a verification_layer_id whose own status is kernel_verified")),
        None => Err(mcp_invalid_params(format!("unknown verification_layer_id: {}", verification_layer_id))),
    }
}

fn parse_json_or_wrap(raw: &str) -> serde_json::Value {
    serde_json::from_str::<serde_json::Value>(raw).unwrap_or_else(|_| serde_json::json!({"raw": raw}))
}

fn map_candidate_construction_row(row: &rusqlite::Row) -> rusqlite::Result<serde_json::Value> {
    let parameters_json: String = row.get(6)?;
    let claimed_properties_json: String = row.get(7)?;
    let known_failures_json: String = row.get(8)?;
    let empirical_checks_json: String = row.get(9)?;
    let trust_status: String = row.get(11)?;
    let verification_layer_status: Option<String> = row.get(15)?;
    let has_kernel_evidence = trust_status == "kernel_verified_claim_linked"
        && verification_layer_status.as_deref() == Some("kernel_verified");
    Ok(serde_json::json!({
        "candidate_construction_id": row.get::<_, String>(0)?,
        "dossier_id": row.get::<_, Option<String>>(1)?,
        "related_node_id": row.get::<_, Option<String>>(2)?,
        "verification_layer_id": row.get::<_, Option<String>>(3)?,
        "construction_type": row.get::<_, String>(4)?,
        "informal_description": row.get::<_, String>(5)?,
        "parameters": parse_json_or_wrap(&parameters_json),
        "claimed_properties": parse_json_or_wrap(&claimed_properties_json),
        "known_failures": parse_json_or_wrap(&known_failures_json),
        "empirical_checks": parse_json_or_wrap(&empirical_checks_json),
        "status": row.get::<_, String>(10)?,
        "trust_status": trust_status,
        "created_by": row.get::<_, String>(12)?,
        "created_at": row.get::<_, String>(13)?,
        "updated_at": row.get::<_, String>(14)?,
        "verification_layer_status": verification_layer_status,
        "has_kernel_evidence": has_kernel_evidence,
    }))
}

fn candidate_construction_json(conn: &Connection, candidate_construction_id: &str) -> Result<serde_json::Value, McpError> {
    let sql = format!("{} WHERE cc.id = ?1", CANDIDATE_CONSTRUCTION_SELECT);
    let result = conn
        .query_row(&sql, [candidate_construction_id], map_candidate_construction_row)
        .optional()
        .map_err(rs)?;
    result.ok_or_else(|| mcp_invalid_params(format!("unknown candidate_construction_id: {}", candidate_construction_id)))
}

fn research_dossier_observe_json(conn: &Connection, dossier_id: &str) -> Result<serde_json::Value, McpError> {
    let dossier: Option<(String, Option<String>, Option<String>, Option<String>, String, String, String)> = conn.query_row(
        "SELECT title, description, problem_version_id, episode_id, status, created_at, updated_at
         FROM research_dossiers WHERE id = ?1",
        [dossier_id],
        |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?, row.get(6)?)),
    ).optional().map_err(rs)?;
    let Some((title, description, problem_version_id, episode_id, status, created_at, updated_at)) = dossier else {
        return Err(mcp_invalid_params(format!("unknown dossier_id: {}", dossier_id)));
    };

    let mut stmt = conn.prepare(
        "SELECT id, section_order, title, created_at FROM research_sections
         WHERE dossier_id = ?1 ORDER BY section_order ASC",
    ).map_err(rs)?;
    let sections = stmt.query_map([dossier_id], |row| {
        Ok(serde_json::json!({
            "section_id": row.get::<_, String>(0)?,
            "section_order": row.get::<_, i64>(1)?,
            "title": row.get::<_, String>(2)?,
            "created_at": row.get::<_, String>(3)?,
        }))
    }).map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT id, section_id, node_order, node_type, title, statement, content, trust_status,
                linked_obligation_id, linked_verified_lemma_id, created_at, updated_at
         FROM research_nodes WHERE dossier_id = ?1 ORDER BY node_order ASC",
    ).map_err(rs)?;
    let nodes = stmt.query_map([dossier_id], |row| {
        Ok(serde_json::json!({
            "node_id": row.get::<_, String>(0)?,
            "section_id": row.get::<_, Option<String>>(1)?,
            "node_order": row.get::<_, i64>(2)?,
            "node_type": row.get::<_, String>(3)?,
            "title": row.get::<_, String>(4)?,
            "statement": row.get::<_, Option<String>>(5)?,
            "content": row.get::<_, Option<String>>(6)?,
            "trust_status": row.get::<_, String>(7)?,
            "linked_obligation_id": row.get::<_, Option<String>>(8)?,
            "linked_verified_lemma_id": row.get::<_, Option<String>>(9)?,
            "created_at": row.get::<_, String>(10)?,
            "updated_at": row.get::<_, String>(11)?,
        }))
    }).map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT id, title, authors, venue, year, url, doi, raw_citation, created_at
         FROM external_references WHERE dossier_id = ?1 ORDER BY created_at ASC, id ASC",
    ).map_err(rs)?;
    let references = stmt.query_map([dossier_id], |row| {
        Ok(serde_json::json!({
            "reference_id": row.get::<_, String>(0)?,
            "title": row.get::<_, String>(1)?,
            "authors": row.get::<_, Option<String>>(2)?,
            "venue": row.get::<_, Option<String>>(3)?,
            "year": row.get::<_, Option<String>>(4)?,
            "url": row.get::<_, Option<String>>(5)?,
            "doi": row.get::<_, Option<String>>(6)?,
            "raw_citation": row.get::<_, Option<String>>(7)?,
            "created_at": row.get::<_, String>(8)?,
        }))
    }).map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT id, reference_id, node_id, label, statement, claim_status, mathlib_name,
                proved_episode_id, proved_lemma_id, notes, created_at, updated_at
         FROM external_theorem_claims WHERE dossier_id = ?1 ORDER BY created_at ASC, id ASC",
    ).map_err(rs)?;
    let claims = stmt.query_map([dossier_id], |row| {
        Ok(serde_json::json!({
            "external_theorem_claim_id": row.get::<_, String>(0)?,
            "reference_id": row.get::<_, Option<String>>(1)?,
            "node_id": row.get::<_, Option<String>>(2)?,
            "label": row.get::<_, String>(3)?,
            "statement": row.get::<_, String>(4)?,
            "claim_status": row.get::<_, String>(5)?,
            "mathlib_name": row.get::<_, Option<String>>(6)?,
            "proved_episode_id": row.get::<_, Option<String>>(7)?,
            "proved_lemma_id": row.get::<_, Option<String>>(8)?,
            "notes": row.get::<_, Option<String>>(9)?,
            "created_at": row.get::<_, String>(10)?,
            "updated_at": row.get::<_, String>(11)?,
        }))
    }).map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT id, node_id, label, statement, assumption_status, rationale, created_at, updated_at
         FROM assumption_boundaries WHERE dossier_id = ?1 ORDER BY created_at ASC, id ASC",
    ).map_err(rs)?;
    let assumptions = stmt.query_map([dossier_id], |row| {
        Ok(serde_json::json!({
            "assumption_boundary_id": row.get::<_, String>(0)?,
            "node_id": row.get::<_, Option<String>>(1)?,
            "label": row.get::<_, String>(2)?,
            "statement": row.get::<_, String>(3)?,
            "assumption_status": row.get::<_, String>(4)?,
            "rationale": row.get::<_, Option<String>>(5)?,
            "created_at": row.get::<_, String>(6)?,
            "updated_at": row.get::<_, String>(7)?,
        }))
    }).map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT id, external_theorem_claim_id, reviewer_id, decision, review_status, notes, created_at
         FROM citation_reviews WHERE dossier_id = ?1 ORDER BY created_at ASC, id ASC",
    ).map_err(rs)?;
    let citation_reviews = stmt.query_map([dossier_id], |row| {
        Ok(serde_json::json!({
            "citation_review_id": row.get::<_, String>(0)?,
            "external_theorem_claim_id": row.get::<_, String>(1)?,
            "reviewer_id": row.get::<_, String>(2)?,
            "decision": row.get::<_, String>(3)?,
            "review_status": row.get::<_, String>(4)?,
            "notes": row.get::<_, Option<String>>(5)?,
            "created_at": row.get::<_, String>(6)?,
        }))
    }).map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        "SELECT id, target_kind, target_id, layer_kind, status, summary, evidence_json, created_at, updated_at
         FROM verification_layers WHERE dossier_id = ?1 ORDER BY target_kind ASC, target_id ASC, layer_kind ASC",
    ).map_err(rs)?;
    let verification_layers = stmt.query_map([dossier_id], |row| {
        let evidence_json: String = row.get(6)?;
        let evidence: serde_json::Value = serde_json::from_str(&evidence_json).unwrap_or_else(|_| serde_json::json!({"raw": evidence_json}));
        Ok(serde_json::json!({
            "verification_layer_id": row.get::<_, String>(0)?,
            "target_kind": row.get::<_, String>(1)?,
            "target_id": row.get::<_, String>(2)?,
            "layer_kind": row.get::<_, String>(3)?,
            "status": row.get::<_, String>(4)?,
            "summary": row.get::<_, Option<String>>(5)?,
            "evidence": evidence,
            "created_at": row.get::<_, String>(7)?,
            "updated_at": row.get::<_, String>(8)?,
        }))
    }).map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;
    drop(stmt);

    let mut stmt = conn.prepare(
        &format!("{} WHERE cc.dossier_id = ?1 ORDER BY cc.created_at ASC, cc.id ASC", CANDIDATE_CONSTRUCTION_SELECT),
    ).map_err(rs)?;
    let candidate_constructions = stmt.query_map([dossier_id], map_candidate_construction_row)
        .map_err(rs)?.collect::<rusqlite::Result<Vec<_>>>().map_err(rs)?;

    let collect_by_status = |items: &[serde_json::Value], key: &str, status: &str| -> Vec<serde_json::Value> {
        items.iter()
            .filter(|item| item.get(key).and_then(|v| v.as_str()) == Some(status))
            .cloned()
            .collect()
    };
    let trust_boundary = serde_json::json!({
        "lean_verified": {
            "nodes": collect_by_status(&nodes, "trust_status", "proved_in_episode"),
            "external_theorem_claims": collect_by_status(&claims, "claim_status", "proved_in_episode"),
        },
        "mathlib_imported": collect_by_status(&claims, "claim_status", "imported_from_mathlib"),
        "externally_cited": collect_by_status(&claims, "claim_status", "external_citation_unreviewed"),
        "human_reviewed_citations": collect_by_status(&claims, "claim_status", "external_citation_human_reviewed"),
        "unformalized_assumptions": collect_by_status(&assumptions, "assumption_status", "unformalized_assumption"),
        "rejected_assumptions": collect_by_status(&assumptions, "assumption_status", "rejected_unsafe_assumption"),
        "open_gaps": collect_by_status(&nodes, "trust_status", "open_gap"),
        "policy": "Research dossier state is not proof authority. Only Lean-backed episode/canonical lemma rows are kernel evidence; citations, reviews, empirical layers, assumptions, and candidate constructions stay explicitly labeled."
    });

    Ok(serde_json::json!({
        "dossier_id": dossier_id,
        "title": title,
        "description": description,
        "problem_version_id": problem_version_id,
        "episode_id": episode_id,
        "status": status,
        "created_at": created_at,
        "updated_at": updated_at,
        "sections": sections,
        "nodes": nodes,
        "external_references": references,
        "external_theorem_claims": claims,
        "assumption_boundaries": assumptions,
        "citation_reviews": citation_reviews,
        "verification_layers": verification_layers,
        "candidate_constructions": candidate_constructions,
        "trust_boundary": trust_boundary,
    }))
}

/// Issue #38's mode-enforcement policy: unsafe_dev_attestation ("attested"
/// fidelity_status) means development playtest, never a measured claim.
/// Blocked outright (no override possible) for benchmark/evaluation/
/// public_report run-envelope modes; allowed for private_audit only with an
/// explicit allow_dev_attested=true; always allowed for development (or any
/// other mode, since only these three are "measured" in the sense this
/// policy cares about) and for any fidelity_status other than "attested"
/// (a "verified" problem is fine in any mode; episode_create's own gate
/// already rejects "unreviewed"/"rejected" before an episode can exist at all).
fn enforce_dev_attestation_mode_policy(fidelity_status: &str, mode: &str, allow_dev_attested: bool) -> Result<(), McpError> {
    if fidelity_status != "attested" {
        return Ok(());
    }
    match mode {
        "benchmark" | "evaluation" | "public_report" => Err(mcp_invalid_params(
            "attested/dev-bypass problems are not valid for benchmark/evaluation/public_report runs"
        )),
        "private_audit" if !allow_dev_attested => Err(mcp_invalid_params(
            "attested/dev-bypass problems require allow_dev_attested=true for private_audit runs"
        )),
        _ => Ok(()),
    }
}

/// Issue #38's TRUSTED CANONICAL HASH EXEMPTION, formalized as its own
/// named, explicit, tested policy — not an ad hoc PutnamBench workaround.
///
/// The rule: `unsafe_dev_attestation` is forbidden in benchmark/evaluation/
/// public_report runs UNLESS the problem belongs to a benchmark suite
/// marked `trusted_canonical_source` AND the resulting
/// `benchmark_fidelity_basis` will be `canonical_statement_hash_match`
/// (trusted hash alignment against that suite's own registered canonical/
/// prover-ready formal statement — the cross-check `benchmark_result_record`
/// already performs, unconditionally, before a fidelity basis is ever
/// computed at all: a hash MISMATCH is rejected outright earlier in the
/// same handler, so reaching this exemption check at all already implies
/// the hash matched).
///
/// `suite_trusted` alone is a sound, complete proxy for "this claim's basis
/// will be `canonical_statement_hash_match`": `benchmark_result_record`'s
/// fidelity-basis logic assigns that value whenever the suite is trusted,
/// unconditionally (never falling through to `problem_fidelity_verified`
/// for a trusted suite even if the problem also happens to be
/// independently reviewed) — so the two conditions are equivalent at this
/// call site by construction, not by coincidence.
///
/// Why this exemption exists at all: a literal, exception-free mode block
/// would reject `putnam_runner.rs` — the real, already-shipped, real-
/// toolchain-verified automated PutnamBench pass@k runner, which runs in
/// `mode: "benchmark"` and imports every problem via
/// `unsafe_dev_attestation: true` (there is no per-problem human fidelity
/// review step for an automated ~600-problem import). A trusted suite's
/// own canonical statement-hash match is independently sufficient fidelity
/// evidence for issue #38's mode-enforcement policy's own underlying
/// concern ("don't let uncertified dev-bypass content leak into a measured
/// claim") — the claim being certified there is "this hash matches the
/// suite's own canonical statement," not "a human reviewed this," and that
/// evidence doesn't depend on which mode the run happens to be.
fn trusted_canonical_hash_exemption_applies(suite_trusted: bool) -> bool {
    suite_trusted
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
        Err(step::StepError::InvalidCost { cost_micros }) => (
            StepDisposition::InvalidResponse, false,
            Some(format!("invalid_cost: cost_micros must be >= 0 and fit in i64 (got {})", cost_micros)),
        ),
        Err(step::StepError::BudgetExceeded { requested_cost_micros, remaining_cost_micros }) => (
            StepDisposition::Error, false,
            Some(format!(
                "budget_denied: cost_micros {} exceeds remaining budget {}",
                requested_cost_micros, remaining_cost_micros
            )),
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

struct BenchmarkLink {
    suite_name: String,
    upstream_problem_id: Option<String>,
}

/// If this episode's problem_version's root_formal_statement matches (via
/// root_statement_hash, the same server-computed comparison #30 uses to bind
/// benchmark_results to episodes) a registered benchmark_problem, returns that
/// suite's name and (when unambiguous) the upstream problem id. `None` means
/// this episode has no known link to any tracked benchmark suite.
///
/// `root_statement_hash` has no uniqueness constraint on `benchmark_problems`
/// — the identical statement text could in principle be registered under more
/// than one suite (or more than once within a suite). Rather than silently
/// picking an arbitrary match (nondeterministic, and could misattribute the
/// WRONG suite name), an ambiguous match still gates — the safe default for a
/// contamination policy is to over-restrict, never to under-restrict — but
/// reports the ambiguity honestly instead of a specific, possibly-wrong name.
fn benchmark_suite_name_for_episode(conn: &Connection, episode_id: &str) -> Result<Option<BenchmarkLink>, McpError> {
    let pv_hash: Option<String> = conn.query_row(
        "SELECT pv.root_statement_hash FROM episodes e JOIN problem_versions pv ON pv.id = e.problem_version_id WHERE e.id = ?1",
        [episode_id], |row| row.get(0),
    ).optional().map_err(rs)?;
    let Some(pv_hash) = pv_hash else { return Ok(None) };
    let mut stmt = conn.prepare(
        "SELECT DISTINCT s.name, p.upstream_problem_id FROM benchmark_problems p JOIN benchmark_suites s ON s.id = p.suite_id \
         WHERE p.root_statement_hash = ?1 ORDER BY s.name ASC, p.upstream_problem_id ASC"
    ).map_err(rs)?;
    let rows: Vec<(String, String)> = stmt.query_map([&pv_hash], |row| Ok((row.get(0)?, row.get(1)?)))
        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
    if rows.is_empty() {
        return Ok(None);
    }
    let distinct_suites: std::collections::BTreeSet<&str> = rows.iter().map(|(s, _)| s.as_str()).collect();
    if distinct_suites.len() > 1 {
        return Ok(Some(BenchmarkLink {
            suite_name: format!("ambiguous — this statement matches {} distinct benchmark suites", distinct_suites.len()),
            upstream_problem_id: None,
        }));
    }
    // Exactly one suite name, but possibly more than one problem row within it
    // sharing this hash — in that case the suite is unambiguous but the
    // specific problem id is not, so omit it rather than guess.
    Ok(Some(BenchmarkLink {
        suite_name: rows[0].0.clone(),
        upstream_problem_id: if rows.len() == 1 { Some(rows[0].1.clone()) } else { None },
    }))
}

fn render_proof_export(conn: &Connection, episode_id: &str, mode: ExportMode) -> Result<String, McpError> {
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

    if mode == ExportMode::Lean {
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

    if mode == ExportMode::PublicSummary {
        // Redacted by construction: never touches lean_src, winning_proof,
        // attempts[].detail, rendered_modules, drafts, or plan content — only
        // status, counts, hashes, and identification. This is the mode #33
        // requires for any disclosure that might reach a benchmark's public
        // corpus, so it must be safe to call unconditionally (no gate).
        let link = benchmark_suite_name_for_episode(conn, episode_id)?;
        let headline = match outcome.as_deref() {
            Some("certified") => "CERTIFIED",
            Some("kernel_verified") => "KERNEL_VERIFIED",
            Some("refuted") => "REFUTED",
            Some("gave_up") => "GAVE_UP",
            Some(other) => other,
            None => "IN_PROGRESS",
        };
        let mut counts: std::collections::BTreeMap<&str, i64> = std::collections::BTreeMap::new();
        for o in &obligations {
            *counts.entry(o.status.as_str()).or_insert(0) += 1;
        }
        let res = serde_json::json!({
            "mode": "public_summary",
            "episode_id": episode_id,
            "root_formal_statement": root_statement,
            "outcome": headline,
            "fidelity_status": fidelity_status,
            "benchmark_suite": link.as_ref().map(|l| l.suite_name.clone()),
            "benchmark_upstream_problem_id": link.as_ref().and_then(|l| l.upstream_problem_id.clone()),
            "obligation_counts_by_status": counts,
            "step_count": step_count,
            "created_at": created_at,
            "completed_at": completed_at,
            "environment_hash": env_hash,
            "import_manifest_hash": manifest_hash,
            "trajectory_event_count": event_count,
            "trajectory_first_hash": first_hash,
            "trajectory_last_hash": last_hash,
        });
        return Ok(serde_json::to_string_pretty(&res).unwrap());
    }

    if mode == ExportMode::TrainingExport {
        let ep_uuid = Uuid::parse_str(episode_id).map_err(|e| mcp_invalid_params(format!("invalid episode_id: {}", e)))?;
        let records = dataset::export_rl(conn, ep_uuid).map_err(mcp_internal_error)?;
        let mut values: Vec<serde_json::Value> = records.iter().map(|r| serde_json::to_value(r).unwrap()).collect();
        for v in values.iter_mut() {
            trajectories::scrub_value(v);
        }
        return Ok(serde_json::to_string_pretty(&values).unwrap());
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
    match mode {
        ExportMode::AuditArchive => md.push_str(
            "> 🔒 **AUDIT ARCHIVE — private.** Includes the full proof source and every attempt, \
             including failures. Not for public disclosure — see docs/benchmarks/putnambench.md if \
             this problem is linked to a tracked benchmark suite.\n\n"
        ),
        ExportMode::MaintainerSubmission => {
            let link = benchmark_suite_name_for_episode(conn, episode_id)?;
            md.push_str(&format!(
                "> 🔒 **MAINTAINER SUBMISSION — private.** Packaged for direct, private communication \
                 with a benchmark suite's own maintainers. Includes the full proof source and every \
                 attempt. Do not post this publicly. Suite: {}{}\n\n",
                link.as_ref().map(|l| l.suite_name.as_str()).unwrap_or("(not linked to a tracked benchmark suite)"),
                link.as_ref().and_then(|l| l.upstream_problem_id.as_deref())
                    .map(|id| format!(" (upstream problem id: {})", id)).unwrap_or_default(),
            ));
        }
        ExportMode::PaperDossier => md.push_str(
            "> 📄 **PAPER DOSSIER — private.** Includes the full proof source. Not for public \
             disclosure without maintainer coordination if this problem is linked to a tracked \
             benchmark suite — see docs/benchmarks/putnambench.md.\n\n"
        ),
        _ => {}
    }
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

    if mode == ExportMode::PaperDossier {
        // A deterministic, templated narrative built from the same structured
        // facts already computed above — not a model-generated summary (this
        // function has no model access) — but still prose, not only tables, per
        // #37's acceptance criterion.
        let successful_attempts = attempts.iter().filter(|a| a.verdict.starts_with('✅')).count();
        let failed_attempts = attempts.len().saturating_sub(successful_attempts);
        let unresolved: Vec<&ExportObligation> = obligations.iter().filter(|o| o.status != "proved").collect();
        md.push_str("\n## Narrative\n\n");
        md.push_str(&format!(
            "This is an attempt at: *{}*, formalized as `{}`. ",
            source_text.trim(), root_statement,
        ));
        md.push_str(&match outcome.as_deref() {
            Some("certified") => "The proof search concluded with the root goal kernel-verified, and the formal statement's fidelity to the source problem has been independently reviewed and confirmed. ".to_string(),
            Some("kernel_verified") => format!(
                "The proof search concluded with the root goal kernel-verified, but the formal statement's fidelity to the source problem is {} — this proof establishes the formal claim, not (yet, or not at all) the informal one. ",
                if fidelity_status == "rejected" { "REJECTED" } else { "not yet independently reviewed" },
            ),
            Some("refuted") => "The proof search concluded that the root goal, as formalized, does not hold. ".to_string(),
            Some("gave_up") => "The proof search was abandoned before reaching a verified or refuted conclusion. ".to_string(),
            None => "The proof search is still in progress. ".to_string(),
            Some(_) => String::new(),
        });
        md.push_str(&format!(
            "Across {} obligation(s) and {} recorded attempt(s) ({} accepted by the kernel, {} rejected or otherwise unsuccessful), ",
            obligations.len(), attempts.len(), successful_attempts, failed_attempts,
        ));
        if unresolved.is_empty() && !obligations.is_empty() {
            md.push_str("every obligation reached a proved state — no gaps remain in this proof tree. ");
        } else if !unresolved.is_empty() {
            md.push_str(&format!(
                "{} obligation(s) remain unresolved: {}. ",
                unresolved.len(),
                unresolved.iter().map(|o| format!("`{}` ({})", o.theorem_name, o.status)).collect::<Vec<_>>().join(", "),
            ));
        }
        if !lessons.is_empty() {
            md.push_str(&format!(
                "{} proof-pattern lesson(s) from prior attempts were consulted during this search (see the Lessons applied section above). ",
                lessons.len(),
            ));
        }
        md.push_str(&format!(
            "The trajectory is hash-chained end to end ({} events) and independently re-verifiable via `episode_replay`.\n",
            event_count,
        ));
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
            .with_server_info(Implementation::new("chatdb-mcp", "0.3.23"))
    }

    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, McpError> {
        let tools = vec![
            make_tool::<ReadmeFirstArgs>("readme_first", "CALL THIS FIRST, before creating any episode. Explains what ChatDB is (an environment, not a prover), the trust boundary (tracked MCP actions and Lean verifier results are evidence; hidden model reasoning is not), the required proof-search loop, when to use Solve vs SubmitModule, why untracked/side-channel proof checks don't count as valid attempts, and the cost/benchmark-mode boundary"),
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
            make_tool::<ModelCallReserveArgs>("model_call_reserve", "Reserve a model-call budget lease and immediately debit bounded episode budget"),
            make_tool::<ModelCallSettleArgs>("model_call_settle", "Settle or void a lease, applying only the reserved-vs-actual budget delta"),
            make_tool::<TrajectoryExportArgs>("trajectory_export", "Export trajectory with pagination (cursor + page_size). Raw event payload_json can expose a completed proof body (proof_term/module_items) — for a benchmark-linked episode this requires allow_putnambench_proof_export=true, same contamination policy as proof_export (issue #33)"),
            make_tool::<EpisodeReplayArgs>("episode_replay", "Re-execute typed actions through canonical reducer with Lean re-verification"),
            make_tool::<ProofExportArgs>("proof_export", "Render an episode as a proof dossier. format: \"markdown\" (default, full dossier) | \"lean\" (bare assembled source) | \"public_summary\" (redacted, safe for public/benchmark disclosure — never includes the proof body) | \"audit_archive\" (full dossier, explicitly labeled private) | \"training_export\" (structured JSON records for SFT/RL/DPO) | \"paper_dossier\" (full dossier plus a written narrative section) | \"maintainer_submission\" (full dossier packaged for a benchmark suite's own maintainers). Modes that expose the completed proof body require allow_putnambench_proof_export=true when the episode's problem is linked to a tracked benchmark suite — see docs/benchmarks/putnambench.md"),
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
            make_tool::<ResearchDossierCreateArgs>("research_dossier_create", "Create a Level 4 research dossier, optionally linked to a problem_version, an episode, or neither. Metadata only: never changes proof, fidelity, budget, or benchmark state"),
            make_tool::<ResearchDossierObserveArgs>("research_dossier_observe", "Read a research dossier with sections, nodes, citations, assumptions, verification layers, and explicit trust-boundary buckets"),
            make_tool::<ResearchNodeAddArgs>("research_node_add", "Add a typed research node (definition/proposition/lemma/theorem/remark/reference/open_gap) to a dossier. Trust status is explicit and never implies kernel verification unless linked to a real verified lemma"),
            make_tool::<ExternalReferenceAddArgs>("external_reference_add", "Add an external reference, optionally with one theorem claim. External citations are self-reported metadata and never become kernel verification"),
            make_tool::<AssumptionBoundaryAddArgs>("assumption_boundary_add", "Add an unformalized or rejected unsafe assumption boundary to a dossier. Assumptions are visible metadata, not proof authority"),
            make_tool::<CitationReviewAddArgs>("citation_review_add", "Record a human citation review for an external theorem claim. Human review remains distinct from Lean kernel verification"),
            make_tool::<VerificationLayerSetArgs>("verification_layer_set", "Set an independent verification layer for a dossier target. Blocked/failed layers do not fail the dossier; cited/reviewed/assumed artifacts cannot be mislabeled kernel_verified"),
            make_tool::<CandidateConstructionAddArgs>("candidate_construction_add", "Propose a candidate mathematical construction (graph_family/point_configuration/coloring/field_tower/lattice/counterexample/asymptotic_family/algebraic_object/combinatorial_design/other). Can exist before a dossier, node, Lean theorem, or episode. A research artifact, not a proof certificate"),
            make_tool::<CandidateConstructionObserveArgs>("candidate_construction_observe", "Record one empirical check (supports/refutes/inconclusive) against a candidate construction, appended to its empirical_checks history. Never changes proof status, and 'supports' never implies proved"),
            make_tool::<CandidateConstructionUpdateStatusArgs>("candidate_construction_update_status", "Update a candidate construction's status and/or trust_status (and optionally its claimed_properties/known_failures). trust_status='kernel_verified_claim_linked' is rejected unless verification_layer_id names a verification_layers row whose own status is already kernel_verified"),
            make_tool::<CandidateConstructionLinkNodeArgs>("candidate_construction_link_node", "Attach a candidate construction to a research node. Adopts the node's dossier if the construction has none yet; otherwise the node must already belong to the construction's dossier"),
            make_tool::<CandidateConstructionLinkVerificationLayerArgs>("candidate_construction_link_verification_layer", "Attach a candidate construction to an existing verification layer. Adopts the layer's dossier if the construction has none yet; otherwise the layer must already belong to the construction's dossier"),
            make_tool::<MathlibSearchDeclarationsArgs>("mathlib_search_declarations", "Search the REAL pinned Mathlib source tree (issue #25 librarian) for declaration names containing a substring — beyond exact-name lookup, for when the exact name isn't known. A dotted query like \"Nat.factorization\" is matched on its last segment, since results are reported by file-local name only. Returns declaration name, keyword, derived import module, file path, and a signature snippet, with confidence exact_match/nearby_name. Advisory only: a hit can never mark anything proved. Unavailable (empty results, mathlib_available=false) if lean-checker isn't set up"),
            make_tool::<MathlibSearchLocalArtifactsArgs>("mathlib_search_local_artifacts", "Search THIS ChatDB instance's own previously-verified theorem/def names for a substring match — a local usage_example precedent, not a Mathlib-library result"),
            make_tool::<FormalizationPlanAttachLibrarianResultArgs>("formalization_plan_attach_librarian_result", "Attach a mathlib_search_declarations/mathlib_search_local_artifacts result to a formalization plan item, updating its Mathlib coverage status. A hint attachment, not a re-check — never changes proof status"),
            make_tool::<RunEnvelopeCreateArgs>("run_envelope_create", "Create a run envelope (issues #34/#38): who/what produced a set of episodes — host, model, mode (development/evaluation/benchmark/private_audit/public_report), and host-side cost accounting ChatDB itself cannot observe. Purely descriptive metadata; never affects proof status"),
            make_tool::<RunEnvelopeUpdateArgs>("run_envelope_update", "Update a run envelope's host-side cost fields or notes after the fact"),
            make_tool::<RunEnvelopeAttachEpisodeArgs>("run_envelope_attach_episode", "Tag an existing episode with a run envelope. Metadata only — never changes the episode's outcome/state"),
            make_tool::<RunEnvelopeObserveArgs>("run_envelope_observe", "Read back a run envelope and every episode tagged with it"),
            make_tool::<BenchmarkSuiteCreateArgs>("benchmark_suite_create", "Register a benchmark suite (e.g. PutnamBench) — manual/structured registration, not automated parsing. Issue #29/#30"),
            make_tool::<BenchmarkProblemRegisterArgs>("benchmark_problem_register", "Register one benchmark problem within a suite. root_statement_hash is server-computed from root_formal_statement, never accepted from the client. The server also derives a prover_ready_statement automatically (never client-supplied) when root_formal_statement is a `theorem NAME (binders) : type` declaration — Lean 4's own named-binder-to-Pi-type desugaring — for suites (e.g. PutnamBench) whose faithful catalog text isn't itself a valid problem_create/SubmitModule statement. benchmark_result_record's episode cross-check uses this hash when present, root_statement_hash otherwise"),
            make_tool::<BenchmarkRunCreateArgs>("benchmark_run_create", "Create a benchmark run against a suite. Requires an existing run_envelope_id (call run_envelope_create first — a run should not start unassociated with host/mode/cost tracking). lean_version/mathlib_commit are read from the server's OWN detected Lean environment, never accepted from the client — the only trustworthy source for what was actually used to verify results"),
            make_tool::<BenchmarkResultRecordArgs>("benchmark_result_record", "Record (or update) one problem's result within a run. When episode_id is given, cross-checked against that episode's ACTUAL recorded outcome AND that it proved the SAME statement as benchmark_problem_id (root_statement_hash match) — issue #36 — a result cannot claim kernel_verified/certified unless the referenced episode really reached it for this exact problem"),
            make_tool::<BenchmarkRunObserveArgs>("benchmark_run_observe", "Read back a run, every result recorded against it, and aggregate pass/attempt metrics. solved_rate is 'solved at all within attempt_budget'; pass_at_1_rate is strictly first-attempt success (using pass_at when given, else attempts_used==1) — the two are NOT the same metric. cost_summary separates real metrics (verifier_wall_time_ms/verifier_cpu_time_ms/mcp_action_count/mcp_handler_wall_time_ms/storage_bytes_written/storage_export_bytes/storage_export_wall_time_ms — all real, measured data, null only when genuinely no correlated activity exists yet) from monetary cost (*_cost_micros fields, null unless real money data or a rate card exists — mcp_side_cost_micros/storage_export_cost_micros stay null with no pricing profile decided for either surface). cost_completeness is 'total_cost_known' only when every material cost surface is exact (currently unreachable: mcp_side/storage_export have real metrics but no pricing), 'reported_total_not_exact' when some real monetary signal exists (exact/attested/estimated) but not a complete exact total, else 'total_cost_incomplete'"),
        ];
        Ok(ListToolsResult::with_all_items(tools))
    }

    async fn call_tool(
        &self,
        request: CallToolRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<CallToolResult, McpError> {
        // Issue #38's MCP handler wall-time instrumentation: real wall-clock
        // time for THIS call, logged for every tool regardless of success or
        // failure (an honest total of real handler time spent, not just
        // successful calls). Correlation IDs are duck-typed out of the
        // call's own args before they're consumed below — episode_id/run_id/
        // run_envelope_id are common field names across many, but not all,
        // tool schemas; whichever are present (if any) let
        // benchmark_run_observe aggregate this call's time into a specific
        // episode/benchmark run/run envelope later, with no per-tool special
        // casing needed here.
        let call_start = Instant::now();
        let tool_name = request.name.to_string();
        let (corr_episode_id, corr_run_id, corr_run_envelope_id) = match &request.arguments {
            Some(m) => (
                m.get("episode_id").and_then(|v| v.as_str()).map(|s| s.to_string()),
                m.get("run_id").and_then(|v| v.as_str()).map(|s| s.to_string()),
                m.get("run_envelope_id").and_then(|v| v.as_str()).map(|s| s.to_string()),
            ),
            None => (None, None, None),
        };

        let args_map = request.arguments.unwrap_or_default();
        let args_val = serde_json::Value::Object(args_map);

        // Issue #38's MCP handler timing must capture EVERY call, including
        // ones that end in a validation/policy rejection — but the vast
        // majority of arms below use `?`/`return Err(...)`, which target the
        // nearest enclosing FUNCTION, not just this match: without this
        // `async move { ... }.await` wrapper, every such early return would
        // bypass the metrics-logging code after this match entirely,
        // silently undercounting mcp_handler_wall_time_ms for any run with
        // even one rejected call (a real bug an adversarial review caught).
        // Wrapping the match in its own async block gives `?`/`return` a
        // closer boundary to target — THIS block's own Result — instead of
        // escaping all the way out of call_tool, with zero changes needed
        // to any of the arms themselves.
        let result: Result<CallToolResult, McpError> = async move {
            match request.name.as_ref() {
            "readme_first" => {
                let res = serde_json::json!({
                    "what_this_is": "ChatDB is a verifier-backed RL ENVIRONMENT, not a prover. It contains no provider SDKs, no API keys, no model routing, no inference calls. The external agent host (you, or whatever is calling this tool) IS the policy — you choose what to try. ChatDB assembles Lean source under a strict trust boundary, the real Lean 4 kernel verifies it, and the ledger records what happened. If you have not read anything else in this environment, read this response before calling problem_create or episode_create.",
                    "trust_boundary": "Tracked MCP actions and Lean kernel verdicts are evidence. Your own hidden reasoning, a prior session's transcript, a paper's claim, or a candidate proof you evaluated some OTHER way is NOT evidence — it is a candidate, until this pinned verifier checks it through episode_step. Do not report an obligation as proved, or a problem as solved, based on anything other than an outcome this environment actually recorded (kernel_verified or certified).",
                    "the_loop": "problem_create -> problem_submit_fidelity_review (or unsafe_dev_attestation=true for dev/benchmark use, which caps the result at kernel_verified, never certified) -> episode_create -> episode_observe -> attempt_claim -> episode_step(action, expected_revision = action_request.episode_revision) -> repeat episode_observe/attempt_claim/episode_step until the episode's outcome is set. Call episode_observe before acting (it tells you the current obligation and action_request) and attempt_claim before every episode_step (it hands you the action_attempt_id + claim_token that step requires).",
                    "proof_attempts": {
                        "rule": "Every candidate proof attempt that should count as real proof-search activity MUST go through episode_step, not a side channel.",
                        "solve": "Use the Solve action for a single self-contained tactic/term proof of the current obligation.",
                        "submit_module": "Use SubmitModule for helper definitions, helper theorems, structural or well-founded recursion, and mutually recursive definitions (via MutualGroup) — a small local Lean development, not just one theorem body. See environment_describe's submit_module_boundary for the exact trust rules.",
                        "decompose": "Use Decompose to split the current obligation into child sub-lemma obligations when the root goal is too large to attack directly.",
                        "why_this_matters": "A proof attempt checked some OTHER way (e.g. a bare `lake env lean` invocation outside this episode, or an internal LeanGateway call bypassed around episode_step) and then only submitted as a final winning SubmitModule/Solve loses every failed attempt, every Lean diagnostic, every repair step — the data this environment exists to preserve. Untracked checks do not count as valid benchmark or training attempts, and a run built that way should be reported as incomplete, not as a clean success."
                    },
                    "lookup_and_planning_tools": "Use lean_declaration_lookup, mathlib_search_declarations, mathlib_search_local_artifacts, proof_pattern_search, draft_create/draft_extract_moves, and formalization_plan_* tools rather than an external side channel for the same job during a tracked run — that keeps the reasoning trail inside the environment's own ledger, replayable and auditable later.",
                    "cost_boundary": "cost_micros (episode_step), model_call_reserve/model_call_settle, and the episode budget ledger are enforcement/accounting mechanisms for this environment's MCP-visible budget, not proof-soundness claims. episode_step.cost_micros is reserved before a step executes; model_call_reserve immediately reserves bounded episode budget; model_call_settle adjusts only the reserved-vs-actual delta or refunds a voided reservation. They are NOT the total cost of running you (the external host/model). Host-side reasoning cost (tokens spent thinking, editing, or calling other tools before or around an MCP call) is invisible to ChatDB entirely unless you report it through model_call_reserve/model_call_settle. Never present MCP-visible cost_micros as if it were the complete cost of a run.",
                    "benchmark_mode": "Development/exploratory use and a frozen benchmark run (e.g. PutnamBench) are different modes with different rules. In benchmark mode: every candidate attempt must flow through episode_step (see proof_attempts above) so the run counts as valid evidence, not just a trophy case; and public reports of benchmark results follow a redaction policy — a public summary must not contain completed proof source by default, only aggregate status/hashes/replay information. Check the benchmark documentation (docs/benchmarks/) for the exact export mode to use before publishing any benchmark result.",
                    "forbidden_or_discouraged": [
                        "Do not infer that a declaration is absent from the pinned Mathlib from one 'unknown_declaration' result — call lean_declaration_lookup(deep_check=true) first.",
                        "Do not treat a prior model's or paper's proof as verified — it is a candidate until THIS pinned verifier checks it via episode_step.",
                        "Do not submit a proof attempt that was actually checked outside this episode's tracked flow and present it as if it were tracked.",
                        "Do not present MCP-visible cost accounting as the total cost of the run."
                    ]
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "environment_describe" => {
                let action_schema = schemars::schema_for!(TypedAction);
                let res = serde_json::json!({
                    "environment_version": "0.3.23",
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
                    ],
                    "tool_classification": {
                        "note": "Issue #34's tool-surface audit checklist (side_effect, trust_level, cost_surface, benchmark_safety, replayability, source_code_impact, artifact_risk, required_run_mode) applied to every one of ChatDB's MCP tools, across three passes (v0.3.16, v0.3.17, this one). classified_tool_count == total_tool_count now, but 'classified' means 'analyzed once' — this is a snapshot, not a promise the analysis stays current as the codebase changes; several entries record open design questions rather than closed answers (see unresolved_design_question fields), and the benchmark-mode source-mutation guardrail from #34's acceptance criteria remains separately unaddressed (moot today: no MCP tool edits source files).",
                        "classified_tool_count": 54,
                        "total_tool_count": 54,
                        "tools": {
                            "episode_step": {
                                "side_effect": "mutating — writes action_attempts, episodes, episode_obligations, and (issue #38) action_attempts.lean_result_json",
                                "trust_level": "mixed: the action payload (proof_term/module_items) is untrusted_input — client-authored and adversarial by default — but the recorded outcome is verifier_backed, since the real Lean kernel, not the client, decides kernel_verified/kernel_fail",
                                "cost_surface": "verifier_side (real wall_time_ms/lean_cpu_time_ms now persisted and aggregated into benchmark_run_observe's cost_summary) + mcp_side (request-handling overhead, still unmeasured)",
                                "benchmark_safety": "contamination_risk at the source: a solve action's raw proof_term for a benchmark-linked problem is exactly the content proof_export's and trajectory_export's redaction gates exist to keep out of public exports. episode_step itself never exports anything — it's the origin of the content those two gates must catch, not a gate itself",
                                "replayability": "replayable_with_hashes — episode_replay re-executes the same typed actions through the same reducer plus real Lean re-verification",
                                "source_code_impact": "no_source_change — no MCP tool edits ChatDB's own source files; assembled Lean text is ephemeral verifier input, never a repo mutation",
                                "artifact_risk": "proof_body",
                                "required_run_mode": "any — enforcement belongs at export time, not attempt time"
                            },
                            "proof_export": {
                                "side_effect": "read_only — renders a document from already-recorded state, writes nothing (confirmed by reading the handler: no INSERT/UPDATE anywhere in this path)",
                                "trust_level": "verifier_backed — every field it can render was already recorded by episode_step/attempt_finalize",
                                "cost_surface": "none directly; storage_side if the caller persists the exported document, which is outside ChatDB's own accounting",
                                "benchmark_safety": "THE gate for this concern: public_summary is always safe_public_output; markdown/lean/audit_archive/training_export/paper_dossier/maintainer_submission are private_artifact by default and become contamination_risk only if allow_putnambench_proof_export=true is set for a benchmark-linked episode (issue #33)",
                                "replayability": "deterministic given the same recorded episode state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "proof_body (gated modes) or public_summary (ungated mode) depending on format",
                                "required_run_mode": "private_audit for proof-body-exposing formats on a benchmark-linked episode; any otherwise"
                            },
                            "trajectory_export": {
                                "side_effect": "read_only",
                                "trust_level": "verifier_backed — hash-chained (event_hash/previous_event_hash) recorded events, not client-reconstructable",
                                "cost_surface": "none",
                                "benchmark_safety": "contamination_risk — REAL GAP FOUND AND FIXED in this same audit pass: raw payload_json can carry a solve action's proof_term or a submit_module's module_items, the same completed-proof-body content proof_export's #33 redaction gate exists for, but this tool had no equivalent gate at all until now. It now requires allow_putnambench_proof_export=true for a benchmark-linked episode, mirroring proof_export exactly",
                                "replayability": "replayable_with_hashes — this IS the hash chain episode_replay verifies against",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "proof_body (now gated) for a benchmark-linked episode; diagnostic_only otherwise",
                                "required_run_mode": "private_audit for a benchmark-linked episode; any otherwise"
                            },
                            "episode_replay": {
                                "side_effect": "read_only — re-executes the reducer in-memory against recorded events, writes nothing new",
                                "trust_level": "verifier_backed — re-runs the SAME real Lean verification the original attempt used, doesn't trust the stored outcome blindly",
                                "cost_surface": "verifier_side — a real second Lean invocation per replayed verification step, currently uncounted in cost_summary.verifier_wall_time_ms/verifier_cpu_time_ms (which only sum the ORIGINAL attempt_finalize writes, not replay re-verifications)",
                                "benchmark_safety": "safe_public_output — returns only audit_passed/events_replayed/replay_status, never proof content",
                                "replayability": "deterministic given a pinned Lean/Mathlib toolchain; a toolchain upgrade could change the outcome, which is itself the point (detecting drift)",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "diagnostic_only",
                                "required_run_mode": "any"
                            },
                            "benchmark_result_record": {
                                "side_effect": "mutating — upserts benchmark_results, now including benchmark_fidelity_basis (v0.3.21)",
                                "trust_level": "verifier_backed cross-check, not bare client assertion: since issue #36, a kernel_verified/certified claim is rejected outright without a real episode_id, and since issue #30 the episode's actual recorded outcome and root_statement_hash (via COALESCE(prover_ready_statement_hash, root_statement_hash)) must both match what's claimed. Since v0.3.21 (issue #38's fidelity-basis policy, resolving the design question this entry used to record), a kernel_verified/certified claim is ALSO rejected outright unless EITHER the suite is trusted_canonical_source=true (a real, externally-curated corpus like PutnamBench, whose own canonical statement-hash match is accepted as sufficient fidelity evidence — basis='canonical_statement_hash_match') OR the backing problem_version's fidelity_status is independently 'verified' (basis='problem_fidelity_verified'). An arbitrary untrusted/custom suite backed only by an unsafe_dev_attestation ('attested') problem is no longer sufficient",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output — records status/metrics/attempts_used/benchmark_fidelity_basis, never a proof body",
                                "replayability": "replayable_with_hashes via the referenced episode_id",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "aggregate_metric",
                                "required_run_mode": "benchmark",
                                "note": "benchmark_fidelity_basis is deliberately distinct from problem_versions.fidelity_status: the latter asks whether the formal statement faithfully represents the INFORMAL source problem (independent human/reviewer judgment); the former asks what evidence backs THIS benchmark claim specifically, which for a trusted suite can be satisfied by hash-matching alone without ever requiring that separate review. Public/report-facing consumers should describe basis='canonical_statement_hash_match' as e.g. 'matched the suite's own canonical formal statement', never as 'statement-fidelity certified by ChatDB' — ChatDB performed a hash comparison, not an independent fidelity review, in that case. Since v0.3.22 (mode-enforcement policy), an UNTRUSTED suite's kernel_verified/certified claim backed by an 'attested' problem is rejected with the specific 'attested/dev-bypass problems are not valid for benchmark/evaluation/public_report runs' message when the run's envelope mode is benchmark/evaluation/public_report — checked before the fidelity-basis logic, though for an untrusted suite the fidelity-basis check would reject it in EVERY mode anyway, so this mostly changes rejection wording, not outcome, in this specific handler (the real new restriction lives in run_envelope_attach_episode). Deliberately SKIPPED when the suite is trusted_canonical_source, to avoid contradicting that flag's own purpose and breaking putnam_runner.rs's real, already-shipped workflow (mode='benchmark' + unsafe_dev_attestation import, with no per-problem review step) — a real conflict found and resolved this way, not guessed at silently."
                            },
                            "benchmark_run_observe": {
                                "side_effect": "read_only — aggregates existing benchmark_results/action_attempts rows, writes nothing",
                                "trust_level": "verifier_backed — every number reported is derived from already-recorded, already-cross-checked state, not recomputed trust",
                                "cost_surface": "mcp_side (the query/aggregation work itself, unmeasured) while its OUTPUT surfaces host_side/verifier_side cost data for other surfaces",
                                "benchmark_safety": "safe_public_output — per-problem status and aggregate metrics, never proof bodies; this is a materially different exposure than proof_export/trajectory_export precisely because it never touches payload_json/proof content",
                                "replayability": "deterministic given the same DB state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "aggregate_metric",
                                "required_run_mode": "any (meaningful mainly in benchmark mode, but nothing depends on the caller's declared mode)"
                            },
                            "benchmark_run_create": {
                                "side_effect": "mutating — inserts a benchmark_runs row",
                                "trust_level": "mcp_generated for lean_version/mathlib_commit specifically — read from the SERVER's own detected toolchain, never accepted from the client, so a run can't misreport what verifier it actually used",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output — creates a container, no proof content",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "benchmark",
                                "note": "since issue #34's first bounded slice (v0.3.13), run_envelope_id is REQUIRED, not optional — a benchmark run cannot exist unassociated with host/mode/cost tracking"
                            },
                            "run_envelope_create": {
                                "side_effect": "append_only — inserts a run_envelopes row",
                                "trust_level": "human_attested for host_name/host_model/mode (self-declared by the caller) with an explicit, honest confidence tier (host_cost_confidence: exact_provider_receipt/exact_local_meter/estimated/attested/unknown) rather than pretending self-declaration is verifier-grade",
                                "cost_surface": "host_side — this tool IS the host-side cost declaration surface",
                                "benchmark_safety": "safe_public_output — metadata only",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any — creates the envelope FOR whichever mode is declared"
                            },
                            "problem_create": {
                                "side_effect": "mutating — inserts a problem_versions row",
                                "trust_level": "untrusted_input by design — root_formal_statement is entirely client-authored, and fidelity_status starts 'unreviewed' until either a real problem_submit_fidelity_review or the honestly-named unsafe_dev_attestation=true (capped at kernel_verified, never certified)",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output at creation time; the statement itself becomes contamination-relevant only once an episode proves it and that proof is later exported",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "development is the honest expectation for unsafe_dev_attestation=true (the name says so); since v0.3.22 this is now actively enforced downstream at the point an episode built from such a problem is USED in a measured run, not at problem_create itself (which has no run/mode context to check against) — see run_envelope_attach_episode and benchmark_result_record's mode-enforcement policy"
                            },
                            "episode_create": {
                                "side_effect": "mutating — inserts an episodes row and its first action_request",
                                "trust_level": "verifier_backed gate — requires the problem_version's fidelity_status to already be 'verified' or 'attested'; rejects 'unreviewed'/'rejected' outright",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output — no proof content yet, just episode scaffolding",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "attempt_claim": {
                                "side_effect": "mutating — inserts/updates an action_attempts row with a claim_token, idempotent on idempotency_key",
                                "trust_level": "mcp_generated — the claim_token itself is server-issued and is what makes episode_step's compare-and-swap safe against concurrent/duplicate submission",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output — no proof content, just a claim handshake",
                                "replayability": "deterministic (idempotent replay of the same idempotency_key returns the same claim)",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "draft_create": {
                                "side_effect": "append_only — inserts a drafts row",
                                "trust_level": "untrusted_input, explicitly — issue #23's whole point is preserving informal planning content WITHOUT letting it masquerade as evidence; a draft can never mark anything proved",
                                "cost_surface": "none",
                                "benchmark_safety": "private_artifact by default framing (informal reasoning, not a public metric), though not currently export-gated the way proof_export/trajectory_export are — lower risk since it never contains a completed formal proof, but worth noting it's a different exposure category, not a proven-safe one",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none (advisory scaffolding only)",
                                "required_run_mode": "any"
                            },
                            "proof_pattern_create": {
                                "side_effect": "append_only — inserts a proof_patterns row, rejects a duplicate pattern_key rather than overwriting",
                                "trust_level": "untrusted_input — a pattern is a free-text failure_signature/recommended_repair pair the caller asserts, never independently checked against real proof state",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — a lesson, not a proof or a problem-specific artifact",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none — purely advisory, can never mark anything proved or change fidelity/certification status",
                                "required_run_mode": "any"
                            },
                            "model_call_reserve": {
                                "side_effect": "mutating — conditionally reserves bounded episode budget immediately, then inserts a model_call_leases row only if that reservation succeeds; NULL episode budget is unbounded",
                                "trust_level": "untrusted_input — declared_model/runner_id/max_input_tokens/max_output_tokens are entirely client-asserted, not independently verified by ChatDB",
                                "cost_surface": "host_side — reserves budget for what will become a HOST-reported model-call cost, distinct from run_envelopes.host_side_cost_micros (one aggregate figure per run) and from verifier_side cost (real, ChatDB-measured Lean timing). Settled actual model-call costs are folded into benchmark_run_observe's cost_summary as model_call_reported_cost_micros, always at 'attested' confidence, never merged into an exact total",
                                "benchmark_safety": "safe_public_output — a budget reservation, no proof content",
                                "replayability": "deterministic given recorded state, but the reservation itself has no external effect to replay (no real model call happens through this tool — it only manages ChatDB's own ledger)",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any",
                                "note": "calling episode_step for the SAME (episode_id, action_attempt_id) this lease is reserved against auto-settles it, using that step's OWN cost_micros argument as actual_cost_micros. That implicit settlement now uses the same delta rule as model_call_settle: lower actual refunds the reserved difference, higher actual requires remaining budget for only the delta, and the step preparation rolls back if the delta cannot be covered."
                            },
                            "model_call_settle": {
                                "side_effect": "mutating — settles or voids an open lease. status='settled' adjusts the episode budget only by actual_cost_micros - reserved_cost_micros (refunds if lower, conditionally debits only the delta if higher); status='voided' refunds the reserved amount and leaves actual_cost_micros NULL. Already-settled/voided leases are rejected clearly rather than charged twice. Note: this is not the ONLY way a lease reaches 'settled' — see model_call_reserve's note on episode_step's own auto-settle behavior for the same (episode_id, action_attempt_id) pair",
                                "trust_level": "untrusted_input — actual_cost_micros is exactly as self-reported as the reservation was; nothing here upgrades it to verifier_backed or measured",
                                "cost_surface": "host_side — now (v0.3.20) aggregated into benchmark_run_observe's cost_summary as model_call_reported_cost_micros, always at 'attested' confidence",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic given recorded state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "run_envelope_update": {
                                "side_effect": "mutating — overwrites host_side_cost_micros/host_cost_confidence/notes on an existing run_envelopes row IN PLACE",
                                "trust_level": "human_attested, same as run_envelope_create — self-declared, with an explicit confidence tier rather than pretending certainty",
                                "cost_surface": "host_side — this is the correction/refinement path for that same declaration",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "NOT replayable in the audit sense: there is no history/versioning of prior values — an update overwrites host_side_cost_micros/host_cost_confidence with no log of what it was before or when it changed. A benchmark_run_observe call made before vs after an update would report genuinely different numbers with no record that a correction happened. Worth a deliberate decision (an append-only revision log?) if run envelopes are ever updated after a report has already been shared, rather than assumed away",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "run_envelope_attach_episode": {
                                "side_effect": "mutating — sets episodes.run_id only; confirmed by reading the handler that it never touches outcome/state/current_revision or any other proof-status column",
                                "trust_level": "mcp_generated linkage between two things that separately already exist (a real run_envelope, a real episode) — the tool itself asserts nothing new about either",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output — a tagging operation, no proof content moves",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "since v0.3.22 (issue #38's mode-enforcement policy, resolving the gap this entry used to note), unconditionally rejects attaching an 'attested' (unsafe_dev_attestation) episode to a benchmark/evaluation/public_report-mode envelope — no override possible, no suite-trust exception here (unlike benchmark_result_record, this tool has no suite concept to reason about at all). 'development' is always allowed; 'private_audit' requires the new allow_dev_attested=true argument"
                            },
                            "run_envelope_observe": {
                                "side_effect": "read_only — reads run_envelopes plus every episodes row with matching run_id, writes nothing",
                                "trust_level": "mixed, transparently: mode/host_name/host_model/notes are human_attested (as declared at creation/update); host_cost_confidence is reported alongside the cost figure specifically so a reader can judge how much to trust it, rather than presenting one undifferentiated number",
                                "cost_surface": "none directly; surfaces host_side cost data for other surfaces",
                                "benchmark_safety": "safe_public_output — episode_id/outcome/state only, never proof content",
                                "replayability": "deterministic given current DB state (see run_envelope_update's replayability note on why 'current state' isn't the same as 'full history')",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "formalization_plan_create": {
                                "side_effect": "mutating — inserts a formalization_plans row and, when seeding from draft moves, formalization_plan_items rows plus UPDATEs on draft_moves.promoted_plan_item_id, all in one transaction (validates every seed move before writing any row, so a bad move in the batch never leaves a partially-seeded plan behind)",
                                "trust_level": "untrusted_input — a plan is advisory scaffolding the caller proposes; nothing here is proof-checked",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — planning metadata, not a proof artifact",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none — advisory scaffolding, explicitly not a proof authority",
                                "required_run_mode": "any"
                            },
                            "formalization_plan_observe": {
                                "side_effect": "read_only",
                                "trust_level": "untrusted_input pass-through — reads back exactly what was asserted at creation/update, no verification layer",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "formalization_plan_update": {
                                "side_effect": "mutating — overwrites a plan's title/status/risk_flags_json IN PLACE (partial update: an omitted field keeps its current value rather than being cleared)",
                                "trust_level": "untrusted_input — status transitions (draft/active/completed/abandoned) are caller-asserted, not derived from any verified state",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "NOT replayable in the audit sense — like run_envelope_update, this overwrites in place with no history of prior title/status/risk_flags values",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "formalization_plan_add_item": {
                                "side_effect": "mutating — inserts a formalization_plan_items row",
                                "trust_level": "untrusted_input",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "formalization_plan_attach_lookup": {
                                "side_effect": "mutating — updates one item's mathlib_coverage_status/lookup_result_json; rejects a non-'open' item (already promoted/dropped) rather than silently overwriting settled state",
                                "trust_level": "mcp_generated hint attachment, not a re-check — this tool records what lean_declaration_lookup already reported, it doesn't re-verify anything itself",
                                "cost_surface": "none directly (the real cost was already paid by the lean_declaration_lookup call being attached)",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none — never changes proof status, only planning metadata",
                                "required_run_mode": "any"
                            },
                            "formalization_plan_promote_item_to_obligation": {
                                "side_effect": "mutating — sets one item's status/promoted_obligation_id; a partial UNIQUE index on promoted_obligation_id (schema_v1.rs) stops two plan items from claiming the same real obligation, enforced at the DB layer rather than only this handler's logic",
                                "trust_level": "verifier_backed linkage, not creation: the tool independently confirms the obligation_id already exists in episode_obligations AND belongs to the given episode_id before recording the link — it never creates the obligation itself, so it can never bypass the episode's real budget/CAS accounting",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "formalization_plan_attach_librarian_result": {
                                "side_effect": "mutating — updates mathlib_coverage_status/mathlib_candidate_names_json (accumulated/deduped, not overwritten)/lookup_result_json (latest wins) on one item",
                                "trust_level": "untrusted_input for confidence tier itself (exact_match/nearby_name/type_match/usage_example/unknown is the caller's own assessment of ITS search result), but the underlying search is over ChatDB's own real data (mathlib_search_declarations/mathlib_search_local_artifacts), not fabricated from nothing",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "research_dossier_create": {
                                "side_effect": "mutating — inserts one research_dossiers row, optionally linked to a problem_version and/or episode after verify_dossier_links confirms both exist and (if both given) the episode actually belongs to that problem_version",
                                "trust_level": "mcp_generated metadata container only — a dossier is a research bookkeeping record, never proof authority, and can exist before any problem_version or episode does",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "research_dossier_observe": {
                                "side_effect": "read_only — joins research_dossiers with its sections/nodes/references/claims/assumptions/citation_reviews/verification_layers and buckets them by explicit trust_boundary status",
                                "trust_level": "read_only projection; the trust_boundary buckets it computes (lean_verified vs mathlib_imported vs externally_cited vs human_reviewed_citations vs unformalized/rejected assumptions vs open_gaps) are derived directly from the underlying rows' own status columns, not re-inferred",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "research_node_add": {
                                "side_effect": "mutating — inserts one research_nodes row (and, if section_title is given with no section_id, a new research_sections row) into an existing dossier",
                                "trust_level": "untrusted_input for statement/content text; trust_status is caller-declared but constrained by a DB CHECK — 'proved_in_episode' is rejected unless linked_verified_lemma_id names a real episode_verified_lemmas row, so a node can claim proof lineage only by pointing at kernel evidence that already exists",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — narrative/definition text, not this instance's own proof_term output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none — a node's trust_status is visible metadata, never a proof status mutation",
                                "required_run_mode": "any"
                            },
                            "external_reference_add": {
                                "side_effect": "mutating — inserts one external_references row and, if theorem_statement is given, one external_theorem_claims row",
                                "trust_level": "untrusted_input — self-reported citation metadata; claim_status='proved_in_episode' requires proved_lemma_id to name a real episode_verified_lemmas row and 'imported_from_mathlib' requires a mathlib_name, but the citation text itself (title/authors/venue/statement) is never independently checked by this tool",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "assumption_boundary_add": {
                                "side_effect": "mutating — inserts one assumption_boundaries row, optionally attached to a research node already in the same dossier",
                                "trust_level": "untrusted_input — an assumption boundary records that something is being assumed (or was rejected as an unsafe assumption), which is the opposite of a proof; it is never treated as evidence",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "citation_review_add": {
                                "side_effect": "mutating — inserts one citation_reviews row and updates the target external_theorem_claims.claim_status (only from an unreviewed/reviewed/rejected state, never overwriting a proved_in_episode or imported_from_mathlib claim)",
                                "trust_level": "human-attested, not verifier_backed — reviewer_id is a free-text identifier supplied by the caller, not an authenticated principal; a 'human_reviewed' decision means a person looked at the citation, not that Lean checked it",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "verification_layer_set": {
                                "side_effect": "mutating — upserts one verification_layers row keyed on (dossier_id, target_kind, target_id, layer_kind); blocked/failed layers are recorded as-is and never cascade into failing the dossier or any other row",
                                "trust_level": "mixed by design — most statuses (informal/empirical/cited/human_reviewed/failed/blocked/rejected) are untrusted_input the caller self-reports, but 'kernel_verified' is guarded by enforce_kernel_verified_research_boundary: it is accepted only for a node whose trust_status is already proved_in_episode, an external_theorem_claim already proved_in_episode with a linked lemma, an episode with a kernel_verified/certified outcome, or a problem_version with a real canonical_verified_lemmas row — assumptions and whole dossiers can never be marked kernel_verified through this tool",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none — this tool can attach kernel_verified only where kernel evidence already exists elsewhere; it cannot manufacture that evidence",
                                "required_run_mode": "any"
                            },
                            "candidate_construction_add": {
                                "side_effect": "mutating — inserts one candidate_constructions row, optionally linked to a dossier, research node, and/or verification layer that must already exist (and, if a dossier is also given, must already belong to that dossier)",
                                "trust_level": "untrusted_input — a candidate construction is a proposed mathematical object (informal_description/parameters/claimed_properties), never proof authority; trust_status='kernel_verified_claim_linked' is rejected by enforce_kernel_verified_construction_boundary unless verification_layer_id names a verification_layers row whose own status is already 'kernel_verified'",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "candidate_construction_observe": {
                                "side_effect": "mutating — appends one entry (description/result/details/observed_by/observed_at) to a candidate construction's empirical_checks_json array; never touches status or trust_status",
                                "trust_level": "untrusted_input — a caller-reported empirical check result (supports/refutes/inconclusive); recording 'supports' is evidence bookkeeping, not a proof and not a status transition on its own",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "candidate_construction_update_status": {
                                "side_effect": "mutating — updates status/trust_status/claimed_properties_json/known_failures_json on one existing candidate_constructions row; a falsified/rejected construction is updated in place and stays visible, never deleted",
                                "trust_level": "untrusted_input for status and for trust_status values other than 'kernel_verified_claim_linked'; that one value is guarded by enforce_kernel_verified_construction_boundary against the construction's EXISTING verification_layer_id (set at creation or via candidate_construction_link_verification_layer), so empirically_supported/human_reviewed/formalized_statement_exists constructions can never be silently promoted to kernel evidence through this tool",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "candidate_construction_link_node": {
                                "side_effect": "mutating — sets related_node_id on one candidate_constructions row; if the construction had no dossier_id yet, adopts the node's dossier_id (a research_nodes row always belongs to exactly one dossier) rather than leaving the construction orphaned from the node's context",
                                "trust_level": "verifier_backed linkage only in the sense that both rows are confirmed to exist and (if the construction already had a dossier) to share it — linking a node never itself changes the node's or the construction's trust_status",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "candidate_construction_link_verification_layer": {
                                "side_effect": "mutating — sets verification_layer_id on one candidate_constructions row; if the construction had no dossier_id yet, adopts the layer's dossier_id",
                                "trust_level": "verifier_backed linkage only — confirms both rows exist and (if the construction already had a dossier) share it; if the construction's trust_status is already 'kernel_verified_claim_linked' this re-runs enforce_kernel_verified_construction_boundary against the newly linked layer, so re-linking can never quietly leave a kernel_verified_claim_linked construction pointed at a non-kernel_verified layer",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "mathlib_search_declarations": {
                                "side_effect": "read_only — a filesystem scan of the local Mathlib checkout, no DB write",
                                "trust_level": "mcp_generated from real Mathlib source text, but explicitly file-local-name matching only (documented namespace-resolution limitation) — a hit is a real declaration name found in real source, not a guarantee it resolves under any particular problem's import manifest",
                                "cost_surface": "none tracked (filesystem-bound, not verifier-bound; the DB mutex is deliberately NOT held during this scan, matching the codebase's convention for slow operations)",
                                "benchmark_safety": "safe_public_output — Mathlib's own public source, not ChatDB proof content",
                                "replayability": "deterministic given the same pinned Mathlib checkout; a checkout upgrade could change results",
                                "source_code_impact": "no_source_change — reads Mathlib's checked-out source, never ChatDB's own",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "mathlib_search_local_artifacts": {
                                "side_effect": "read_only — queries episode_verified_lemmas/episode_verified_module_items, no write",
                                "trust_level": "verifier_backed — every name returned already passed the real Lean kernel in some prior episode on THIS instance; explicitly labeled confidence: 'usage_example', i.e. local precedent, not a Mathlib-library result",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — declaration names only, not full proof bodies",
                                "replayability": "deterministic given current DB state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "readme_first": {
                                "side_effect": "read_only — a static informational response, no DB access at all",
                                "trust_level": "mcp_generated — fixed documentation text ChatDB itself asserts about its own rules, not client input",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic (constant across calls until the environment version changes)",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "environment_describe": {
                                "side_effect": "read_only — reads self.lean_available/self.lean_environment (in-memory state set once at startup) plus static schema/documentation text; no DB access",
                                "trust_level": "mcp_generated — this IS the tool whose own tool_classification field this audit populates",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic given the same running server version",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "problem_submit_fidelity_review": {
                                "side_effect": "mutating — inserts a problem_fidelity_reviews row, updates problem_versions.fidelity_status/state, and — a real, non-obvious effect worth flagging — can RETROACTIVELY upgrade an already-terminal episode's outcome from kernel_verified to certified (and the problem's state to COMPLETE) for every episode on this problem_version with outcome='kernel_verified', when the review lands 'verified' after the fact",
                                "trust_level": "human_attested for the review decision itself (approver_id/method/evidence_json are asserted by whoever calls this), but the anti-staleness check is verifier_backed in spirit: source_problem_hash/root_statement_hash/rendering_hash are independently recomputed server-side and the review is rejected outright if they don't match the problem's CURRENT text — a review can only ever authorize the exact text it reviewed, never a stale or substituted one",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output; the retroactive outcome upgrade is a real interaction worth noting for benchmark_result_record specifically — a benchmark_results row recorded when the episode's outcome was still 'kernel_verified' does NOT automatically update to 'certified' when a later fidelity review upgrades the underlying episode; the two can go quietly out of sync unless benchmark_result_record is called again after the review lands. Not a fabrication risk (nothing false is ever recorded), but a real staleness gap worth documenting rather than assuming away",
                                "replayability": "deterministic given recorded state, though the retroactive episode-outcome mutation means an episode's outcome is not fully write-once the way trajectory_events are — episode_replay verifies the ORIGINAL kernel verdict, not this later status promotion",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none directly (a review decision, not a proof body)",
                                "required_run_mode": "any"
                            },
                            "problem_list": {
                                "side_effect": "read_only",
                                "trust_level": "untrusted_input pass-through for root_formal_statement (whatever was asserted at problem_create), verifier_backed for state/fidelity_status (both server-controlled transitions)",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic given current DB state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "episode_reset": {
                                "side_effect": "mutating — creates a genuinely NEW episode row (parent_episode_id linkage) and its first action_request; explicitly nondestructive, never touches the original episode's own rows",
                                "trust_level": "mcp_generated — copies the original episode's config, asserts nothing new",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output — no proof content, just scaffolding for a fresh attempt",
                                "replayability": "deterministic; the original episode remains independently replayable/auditable since episode_reset never mutates it",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "episode_observe": {
                                "side_effect": "mutating, despite looking like a pure read: it recovers expired attempt claims and expired action requests (attempt_recover_expired/request_recover_expired), and — if the only pending request just lapsed — mints a FRESH action_request via lifecycle::advance before returning. A caller expecting 'observe' to be side-effect-free would be wrong; two calls in a row can legitimately return different action_request ids",
                                "trust_level": "mcp_generated — the recovery/advance logic is ChatDB's own bookkeeping, not client-asserted",
                                "cost_surface": "none directly",
                                "benchmark_safety": "safe_public_output — surfaces the current action_request/observation, never proof content beyond what episode_step already recorded",
                                "replayability": "NOT purely deterministic call-to-call in the trivial sense (see side_effect) — but the underlying episode state it reads and the recovery rules it applies are themselves deterministic and replayable",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "episode_status": {
                                "side_effect": "read_only",
                                "trust_level": "verifier_backed for outcome/termination_reason/truncation_reason (server-controlled terminal fields); mcp_generated for step_count/current_revision/invalid_action_count (ChatDB's own bookkeeping counters)",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic given current DB state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "episode_close": {
                                "side_effect": "mutating — force-terminates a non-terminal episode (state='terminated', outcome='gave_up', termination_reason='human_cancelled'); idempotent no-op ('already_closed') for an episode that's already terminated/truncated rather than erroring or double-recording a termination event",
                                "trust_level": "mcp_generated — the caller supplies only a free-text reason (stored, never interpreted); the outcome/termination_reason values are fixed by this handler, not client-suppliable",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — forces a gave_up outcome, can never produce a false kernel_verified/certified claim",
                                "replayability": "replayable_with_hashes — records a real episode_terminated trajectory event like any other terminal transition",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "proof_pattern_search": {
                                "side_effect": "read_only — queries proof_patterns WHERE status='active'",
                                "trust_level": "untrusted_input pass-through — returns exactly what proof_pattern_create asserted, no re-verification",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — lessons, not problem-specific proof content",
                                "replayability": "deterministic given current DB state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "proof_pattern_record_application": {
                                "side_effect": "append_only — inserts a proof_pattern_applications row; confirmed by reading the handler that it deliberately never touches episodes/episode_obligations/action_attempts, so a pattern application can never itself change proof/fidelity/certification status",
                                "trust_level": "mcp_generated linkage between two things that separately already exist (a real pattern_id, a real episode_id) — independently checked to exist before the insert, though the role (failed_example/repair_example/suggested_hint) is the caller's own untrusted_input characterization of the relationship",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "draft_observe": {
                                "side_effect": "read_only",
                                "trust_level": "untrusted_input pass-through — reads back exactly what draft_create/draft_extract_moves asserted",
                                "cost_surface": "none",
                                "benchmark_safety": "private_artifact framing, same caveat as draft_create: informal reasoning content, not export-gated the way proof_export/trajectory_export are, though lower risk since it can't contain a completed formal proof",
                                "replayability": "deterministic given current DB state",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "draft_extract_moves": {
                                "side_effect": "mutating — inserts one or more draft_moves rows in a single transaction",
                                "trust_level": "untrusted_input — a move's kind/description is the caller's own characterization of the draft content, not independently checked",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — structured metadata about informal reasoning, not itself a proof artifact",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none — moves are not obligations until explicitly promoted, and promotion itself never creates an obligation, only links to one that already exists",
                                "required_run_mode": "any"
                            },
                            "benchmark_suite_create": {
                                "side_effect": "mutating — inserts a benchmark_suites row; rejects a duplicate name rather than silently creating a second suite with the same identity",
                                "trust_level": "human_attested — a suite's name/upstream_url/upstream_commit/language are exactly what the caller declares; ChatDB does not itself fetch or verify the upstream repository. trusted_canonical_source (v0.3.21, issue #38's fidelity-basis policy) is the SAME kind of honest self-declared trust assertion, not independently verified — it defaults to false so an arbitrary custom suite can never silently gain the 'hash-match alone is sufficient fidelity evidence' treatment meant only for a real, externally-curated corpus like PutnamBench",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — suite metadata, no proof content",
                                "replayability": "deterministic",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            },
                            "lean_declaration_lookup": {
                                "side_effect": "read_only — no DB write; the DB mutex is deliberately released BEFORE the real (potentially 15-40+ second) Lean invocation, matching this codebase's convention of not stalling other concurrent tool calls on a slow operation",
                                "trust_level": "verifier_backed — this is a REAL Lean toolchain query (self.gateway.lookup_declarations), not a heuristic guess; the result reflects what the pinned Lean/Mathlib environment actually resolves under the given import manifest",
                                "cost_surface": "verifier_side — a real Lean process invocation, currently uncounted anywhere in cost_summary.verifier_wall_time_ms/verifier_cpu_time_ms (which only sum attempt_finalize's episode_step writes, not this tool's independent lookups)",
                                "benchmark_safety": "safe_public_output — declaration name/status/diagnostics only, never a proof body",
                                "replayability": "deterministic given a pinned Lean/Mathlib toolchain and import manifest; explicitly scoped to only the queried problem's own manifest by default (deep_check=true trades speed for a conclusive full-Mathlib-umbrella verdict) — a fast negative result does not by itself prove the declaration is absent from the library, a documented epistemic caveat surfaced in environment_describe's own epistemic_rules",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "diagnostic_only",
                                "required_run_mode": "any"
                            },
                            "benchmark_problem_register": {
                                "side_effect": "mutating — inserts a benchmark_problems row; rejects a duplicate upstream_problem_id within the same suite",
                                "trust_level": "human_attested for root_formal_statement/theorem_name/import_manifest (exactly what the caller declares — ChatDB doesn't itself parse an upstream benchmark repo), but root_statement_hash and prover_ready_statement/prover_ready_statement_hash are ALWAYS server-derived (canonical_hash / to_pi_form), never accepted from the client — the same anti-fabrication principle as root_statement_hash elsewhere, since a client-supplied prover-ready text could otherwise register an easy proxy statement alongside a hard root statement and have benchmark_result_record's cross-check validate against the wrong one",
                                "cost_surface": "none",
                                "benchmark_safety": "safe_public_output — problem metadata (not yet an episode, not yet a proof)",
                                "replayability": "deterministic; to_pi_form fails closed (returns Err, leaving prover_ready_statement/hash NULL) for any statement that isn't a theorem-with-binders declaration, rather than guessing at a conversion",
                                "source_code_impact": "no_source_change",
                                "artifact_risk": "none",
                                "required_run_mode": "any"
                            }
                        }
                    }
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
                    return Err(mcp_invalid_params("invalid_cost: cost_micros must be >= 0"));
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
                            settle_reserved_model_call_leases_for_attempt(
                                &tx1,
                                &args.episode_id,
                                &args.action_attempt_id,
                                args.cost_micros,
                            )?;
                            let post = run_step_post_processing(
                                &tx1, ep_uuid, &args.episode_id, attempt_uuid, &args.action,
                                Ok(outcome), &target_obligation_id, &state_hash_before,
                            )?;
                            tx1.commit().map_err(rs)?;
                            Prepared::Resolved(post)
                        }
                        Ok(step::PrepOutcome::NeedsGateway { request, ctx }) => {
                            settle_reserved_model_call_leases_for_attempt(
                                &tx1,
                                &args.episode_id,
                                &args.action_attempt_id,
                                args.cost_micros,
                            )?;
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
                    return Err(mcp_invalid_params("invalid_cost: reserved_cost_micros must be >= 0"));
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

                reserve_episode_budget_for_model_call(&tx, &args.episode_id, args.reserved_cost_micros)?;

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
                    return Err(mcp_invalid_params("invalid_cost: actual_cost_micros must be >= 0"));
                }
                if !matches!(args.status.as_str(), "settled" | "voided") {
                    return Err(mcp_invalid_params("status must be 'settled' or 'voided'"));
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;

                settle_model_call_lease(&tx, &args.lease_id, args.actual_cost_micros, &args.status)?;

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

                // Issue #33's contamination policy again, closing a real gap found
                // during #34's tool-classification audit: trajectory_export's raw
                // payload_json carries the exact same completed-proof-body content
                // (proof_term, module_items) that proof_export's redaction gate
                // exists to keep out of public exports for benchmark-linked
                // episodes — this tool had no equivalent gate at all.
                if !args.allow_putnambench_proof_export {
                    if let Some(link) = benchmark_suite_name_for_episode(&conn, &args.episode_id)? {
                        return Err(mcp_invalid_params(format!(
                            "episode {} is linked to benchmark suite '{}' — trajectory_export's raw payload_json \
                             can expose the completed proof body (proof_term/module_items), so it requires \
                             allow_putnambench_proof_export=true (see docs/benchmarks/putnambench.md). \
                             Use proof_export with format=\"public_summary\" for a disclosure-safe report instead.",
                            args.episode_id, link.suite_name
                        )));
                    }
                }

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
                let mode = args.format.unwrap_or(ExportMode::Markdown);
                let conn = self.conn.lock().await;

                // Issue #33's contamination policy: a mode that can expose the
                // completed proof body requires an explicit opt-in when this
                // episode's problem is linked to a tracked benchmark suite —
                // upstream maintainers (e.g. PutnamBench) ask that formal proofs
                // not be published without first engaging with them.
                if mode.exposes_proof_body() && !args.allow_putnambench_proof_export {
                    if let Some(link) = benchmark_suite_name_for_episode(&conn, &args.episode_id)? {
                        return Err(mcp_invalid_params(format!(
                            "episode {} is linked to benchmark suite '{}' — exporting a completed proof body \
                             requires allow_putnambench_proof_export=true (see docs/benchmarks/putnambench.md). \
                             Use format=\"public_summary\" for a disclosure-safe report instead.",
                            args.episode_id, link.suite_name
                        )));
                    }
                }

                let doc = render_proof_export(&conn, &args.episode_id, mode)?;
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
            "research_dossier_create" => {
                let args: ResearchDossierCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.title.trim().is_empty() {
                    return Err(mcp_invalid_params("title must be non-empty"));
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                verify_dossier_links(&tx, &args.problem_version_id, &args.episode_id)?;

                let dossier_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "INSERT INTO research_dossiers (
                        id, title, description, problem_version_id, episode_id, status, created_at, updated_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, 'draft', ?6, ?6)",
                    (
                        &dossier_id,
                        args.title.trim(),
                        args.description.as_deref(),
                        args.problem_version_id.as_deref(),
                        args.episode_id.as_deref(),
                        &now,
                    ),
                ).map_err(rs)?;
                let observed = research_dossier_observe_json(&tx, &dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&observed).unwrap())]))
            }
            "research_dossier_observe" => {
                let args: ResearchDossierObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                let conn = self.conn.lock().await;
                let observed = research_dossier_observe_json(&conn, &args.dossier_id)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&observed).unwrap())]))
            }
            "research_node_add" => {
                let args: ResearchNodeAddArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                validate_one_of("node_type", &args.node_type, RESEARCH_NODE_TYPES)?;
                if args.title.trim().is_empty() {
                    return Err(mcp_invalid_params("title must be non-empty"));
                }
                let trust_status = args.trust_status.clone().unwrap_or_else(|| {
                    if args.node_type == "open_gap" { "open_gap".to_string() } else { "external_citation_unreviewed".to_string() }
                });
                validate_one_of("trust_status", &trust_status, RESEARCH_TRUST_STATUSES)?;
                if trust_status == "proved_in_episode" && args.linked_verified_lemma_id.is_none() {
                    return Err(mcp_invalid_params("trust_status='proved_in_episode' requires linked_verified_lemma_id"));
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                require_row_exists(&tx, "research_dossiers", &args.dossier_id, "dossier_id")?;

                let section_id = if let Some(section_id) = args.section_id.clone() {
                    let exists: Option<i64> = tx.query_row(
                        "SELECT 1 FROM research_sections WHERE id = ?1 AND dossier_id = ?2",
                        (&section_id, &args.dossier_id),
                        |row| row.get(0),
                    ).optional().map_err(rs)?;
                    if exists.is_none() {
                        return Err(mcp_invalid_params(format!("unknown section_id for dossier: {}", section_id)));
                    }
                    Some(section_id)
                } else if let Some(section_title) = args.section_title.as_ref().filter(|s| !s.trim().is_empty()) {
                    let section_id = Uuid::new_v4().to_string();
                    let section_order = next_order(&tx, "research_sections", "section_order", &args.dossier_id)?;
                    tx.execute(
                        "INSERT INTO research_sections (id, dossier_id, section_order, title, created_at)
                         VALUES (?1, ?2, ?3, ?4, ?5)",
                        (&section_id, &args.dossier_id, section_order, section_title.trim(), Utc::now().to_rfc3339()),
                    ).map_err(rs)?;
                    Some(section_id)
                } else {
                    None
                };

                if let Some(obligation_id) = &args.linked_obligation_id {
                    require_row_exists(&tx, "episode_obligations", obligation_id, "linked_obligation_id")?;
                }
                if let Some(lemma_id) = &args.linked_verified_lemma_id {
                    require_row_exists(&tx, "episode_verified_lemmas", lemma_id, "linked_verified_lemma_id")?;
                }

                let node_id = Uuid::new_v4().to_string();
                let node_order = next_order(&tx, "research_nodes", "node_order", &args.dossier_id)?;
                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "INSERT INTO research_nodes (
                        id, dossier_id, section_id, node_order, node_type, title, statement, content,
                        trust_status, linked_obligation_id, linked_verified_lemma_id, created_at, updated_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?12)",
                    (
                        &node_id,
                        &args.dossier_id,
                        section_id.as_deref(),
                        node_order,
                        &args.node_type,
                        args.title.trim(),
                        args.statement.as_deref(),
                        args.content.as_deref(),
                        &trust_status,
                        args.linked_obligation_id.as_deref(),
                        args.linked_verified_lemma_id.as_deref(),
                        &now,
                    ),
                ).map_err(rs)?;
                let observed = research_dossier_observe_json(&tx, &args.dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "node_id": node_id,
                    "dossier": observed,
                })).unwrap())]))
            }
            "external_reference_add" => {
                let args: ExternalReferenceAddArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.title.trim().is_empty() {
                    return Err(mcp_invalid_params("title must be non-empty"));
                }

                let claim_status = args.claim_status.clone().unwrap_or_else(|| "external_citation_unreviewed".to_string());
                if args.theorem_statement.is_some() || args.theorem_label.is_some() {
                    validate_one_of("claim_status", &claim_status, RESEARCH_TRUST_STATUSES)?;
                    if claim_status == "proved_in_episode" && args.proved_lemma_id.is_none() {
                        return Err(mcp_invalid_params("claim_status='proved_in_episode' requires proved_lemma_id"));
                    }
                    if claim_status == "imported_from_mathlib" && args.mathlib_name.is_none() {
                        return Err(mcp_invalid_params("claim_status='imported_from_mathlib' requires mathlib_name"));
                    }
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                require_row_exists(&tx, "research_dossiers", &args.dossier_id, "dossier_id")?;
                if let Some(episode_id) = &args.proved_episode_id {
                    require_row_exists(&tx, "episodes", episode_id, "proved_episode_id")?;
                }
                if let Some(lemma_id) = &args.proved_lemma_id {
                    require_row_exists(&tx, "episode_verified_lemmas", lemma_id, "proved_lemma_id")?;
                }

                let reference_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "INSERT INTO external_references (
                        id, dossier_id, title, authors, venue, year, url, doi, raw_citation, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10)",
                    (
                        &reference_id,
                        &args.dossier_id,
                        args.title.trim(),
                        args.authors.as_deref(),
                        args.venue.as_deref(),
                        args.year.as_deref(),
                        args.url.as_deref(),
                        args.doi.as_deref(),
                        args.raw_citation.as_deref(),
                        &now,
                    ),
                ).map_err(rs)?;

                let mut claim_id = None;
                if let Some(statement) = args.theorem_statement.as_ref().filter(|s| !s.trim().is_empty()) {
                    let id = Uuid::new_v4().to_string();
                    let label = args.theorem_label.clone().unwrap_or_else(|| args.title.clone());
                    tx.execute(
                        "INSERT INTO external_theorem_claims (
                            id, dossier_id, reference_id, node_id, label, statement, claim_status,
                            mathlib_name, proved_episode_id, proved_lemma_id, notes, created_at, updated_at
                        ) VALUES (?1, ?2, ?3, NULL, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?11)",
                        (
                            &id,
                            &args.dossier_id,
                            &reference_id,
                            label.trim(),
                            statement.trim(),
                            &claim_status,
                            args.mathlib_name.as_deref(),
                            args.proved_episode_id.as_deref(),
                            args.proved_lemma_id.as_deref(),
                            args.notes.as_deref(),
                            &now,
                        ),
                    ).map_err(rs)?;
                    claim_id = Some(id);
                }
                let observed = research_dossier_observe_json(&tx, &args.dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "reference_id": reference_id,
                    "external_theorem_claim_id": claim_id,
                    "dossier": observed,
                })).unwrap())]))
            }
            "assumption_boundary_add" => {
                let args: AssumptionBoundaryAddArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                validate_one_of("assumption_status", &args.assumption_status, ASSUMPTION_STATUSES)?;
                if args.label.trim().is_empty() || args.statement.trim().is_empty() {
                    return Err(mcp_invalid_params("label and statement must be non-empty"));
                }
                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                require_row_exists(&tx, "research_dossiers", &args.dossier_id, "dossier_id")?;
                if let Some(node_id) = &args.node_id {
                    ensure_target_belongs_to_dossier(&tx, &args.dossier_id, "node", node_id)?;
                }

                let assumption_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "INSERT INTO assumption_boundaries (
                        id, dossier_id, node_id, label, statement, assumption_status, rationale, created_at, updated_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?8)",
                    (
                        &assumption_id,
                        &args.dossier_id,
                        args.node_id.as_deref(),
                        args.label.trim(),
                        args.statement.trim(),
                        &args.assumption_status,
                        args.rationale.as_deref(),
                        &now,
                    ),
                ).map_err(rs)?;
                let observed = research_dossier_observe_json(&tx, &args.dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "assumption_boundary_id": assumption_id,
                    "dossier": observed,
                })).unwrap())]))
            }
            "citation_review_add" => {
                let args: CitationReviewAddArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                validate_one_of("decision", &args.decision, CITATION_REVIEW_DECISIONS)?;
                if args.reviewer_id.trim().is_empty() {
                    return Err(mcp_invalid_params("reviewer_id must be non-empty"));
                }
                let review_status = match args.decision.as_str() {
                    "human_reviewed" => "external_citation_human_reviewed",
                    "rejected" => "rejected_unsafe_assumption",
                    "needs_formalization" => "external_citation_unreviewed",
                    _ => unreachable!(),
                };

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                let claim_exists: Option<i64> = tx.query_row(
                    "SELECT 1 FROM external_theorem_claims WHERE id = ?1 AND dossier_id = ?2",
                    (&args.external_theorem_claim_id, &args.dossier_id),
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                if claim_exists.is_none() {
                    return Err(mcp_invalid_params(format!("unknown external_theorem_claim_id for dossier: {}", args.external_theorem_claim_id)));
                }

                let review_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "INSERT INTO citation_reviews (
                        id, dossier_id, external_theorem_claim_id, reviewer_id, decision, review_status, notes, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)",
                    (
                        &review_id,
                        &args.dossier_id,
                        &args.external_theorem_claim_id,
                        args.reviewer_id.trim(),
                        &args.decision,
                        review_status,
                        args.notes.as_deref(),
                        &now,
                    ),
                ).map_err(rs)?;
                tx.execute(
                    "UPDATE external_theorem_claims
                     SET claim_status = ?1, updated_at = ?2
                     WHERE id = ?3 AND dossier_id = ?4 AND claim_status IN ('external_citation_unreviewed', 'external_citation_human_reviewed', 'rejected_unsafe_assumption')",
                    (review_status, &now, &args.external_theorem_claim_id, &args.dossier_id),
                ).map_err(rs)?;
                let observed = research_dossier_observe_json(&tx, &args.dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "citation_review_id": review_id,
                    "review_status": review_status,
                    "dossier": observed,
                })).unwrap())]))
            }
            "verification_layer_set" => {
                let args: VerificationLayerSetArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                validate_one_of("target_kind", &args.target_kind, VERIFICATION_TARGET_KINDS)?;
                validate_one_of("layer_kind", &args.layer_kind, VERIFICATION_LAYER_KINDS)?;
                validate_one_of("status", &args.status, VERIFICATION_LAYER_STATUSES)?;
                let evidence_json = args.evidence_json.clone().unwrap_or_else(|| "{}".to_string());
                serde_json::from_str::<serde_json::Value>(&evidence_json)
                    .map_err(|e| mcp_invalid_params(format!("evidence_json must be valid JSON: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                require_row_exists(&tx, "research_dossiers", &args.dossier_id, "dossier_id")?;
                ensure_target_belongs_to_dossier(&tx, &args.dossier_id, &args.target_kind, &args.target_id)?;
                enforce_kernel_verified_research_boundary(&tx, &args.dossier_id, &args.target_kind, &args.target_id, &args.status)?;

                let existing_id: Option<String> = tx.query_row(
                    "SELECT id FROM verification_layers
                     WHERE dossier_id = ?1 AND target_kind = ?2 AND target_id = ?3 AND layer_kind = ?4",
                    (&args.dossier_id, &args.target_kind, &args.target_id, &args.layer_kind),
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                let now = Utc::now().to_rfc3339();
                let layer_id = existing_id.unwrap_or_else(|| Uuid::new_v4().to_string());
                tx.execute(
                    "INSERT INTO verification_layers (
                        id, dossier_id, target_kind, target_id, layer_kind, status, summary, evidence_json, created_at, updated_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?9)
                     ON CONFLICT(dossier_id, target_kind, target_id, layer_kind)
                     DO UPDATE SET status = excluded.status, summary = excluded.summary,
                                   evidence_json = excluded.evidence_json, updated_at = excluded.updated_at",
                    (
                        &layer_id,
                        &args.dossier_id,
                        &args.target_kind,
                        &args.target_id,
                        &args.layer_kind,
                        &args.status,
                        args.summary.as_deref(),
                        &evidence_json,
                        &now,
                    ),
                ).map_err(rs)?;
                let observed = research_dossier_observe_json(&tx, &args.dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "verification_layer_id": layer_id,
                    "dossier": observed,
                })).unwrap())]))
            }
            "candidate_construction_add" => {
                let args: CandidateConstructionAddArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                validate_one_of("construction_type", &args.construction_type, CANDIDATE_CONSTRUCTION_TYPES)?;
                if args.informal_description.trim().is_empty() {
                    return Err(mcp_invalid_params("informal_description must be non-empty"));
                }
                if args.created_by.trim().is_empty() {
                    return Err(mcp_invalid_params("created_by must be non-empty"));
                }
                let status = args.status.clone().unwrap_or_else(|| "proposed".to_string());
                validate_one_of("status", &status, CANDIDATE_CONSTRUCTION_STATUSES)?;
                let trust_status = args.trust_status.clone().unwrap_or_else(|| "informal".to_string());
                validate_one_of("trust_status", &trust_status, CANDIDATE_CONSTRUCTION_TRUST_STATUSES)?;
                let parameters_json = args.parameters_json.clone().unwrap_or_else(|| "{}".to_string());
                serde_json::from_str::<serde_json::Value>(&parameters_json)
                    .map_err(|e| mcp_invalid_params(format!("parameters_json must be valid JSON: {}", e)))?;
                let claimed_properties_json = args.claimed_properties_json.clone().unwrap_or_else(|| "[]".to_string());
                serde_json::from_str::<serde_json::Value>(&claimed_properties_json)
                    .map_err(|e| mcp_invalid_params(format!("claimed_properties_json must be valid JSON: {}", e)))?;
                let known_failures_json = args.known_failures_json.clone().unwrap_or_else(|| "[]".to_string());
                serde_json::from_str::<serde_json::Value>(&known_failures_json)
                    .map_err(|e| mcp_invalid_params(format!("known_failures_json must be valid JSON: {}", e)))?;
                let empirical_checks_json = args.empirical_checks_json.clone().unwrap_or_else(|| "[]".to_string());
                serde_json::from_str::<serde_json::Value>(&empirical_checks_json)
                    .map_err(|e| mcp_invalid_params(format!("empirical_checks_json must be valid JSON: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                if let Some(dossier_id) = &args.dossier_id {
                    require_row_exists(&tx, "research_dossiers", dossier_id, "dossier_id")?;
                }
                if let Some(node_id) = &args.related_node_id {
                    match &args.dossier_id {
                        Some(dossier_id) => require_row_in_dossier(&tx, "research_nodes", node_id, dossier_id, "related_node_id")?,
                        None => require_row_exists(&tx, "research_nodes", node_id, "related_node_id")?,
                    }
                }
                if let Some(layer_id) = &args.verification_layer_id {
                    match &args.dossier_id {
                        Some(dossier_id) => require_row_in_dossier(&tx, "verification_layers", layer_id, dossier_id, "verification_layer_id")?,
                        None => require_row_exists(&tx, "verification_layers", layer_id, "verification_layer_id")?,
                    }
                }
                enforce_kernel_verified_construction_boundary(&tx, &args.verification_layer_id, &trust_status)?;

                let candidate_construction_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "INSERT INTO candidate_constructions (
                        id, dossier_id, related_node_id, verification_layer_id, construction_type, informal_description,
                        parameters_json, claimed_properties_json, known_failures_json, empirical_checks_json,
                        status, trust_status, created_by, created_at, updated_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?14)",
                    (
                        &candidate_construction_id,
                        args.dossier_id.as_deref(),
                        args.related_node_id.as_deref(),
                        args.verification_layer_id.as_deref(),
                        &args.construction_type,
                        args.informal_description.trim(),
                        &parameters_json,
                        &claimed_properties_json,
                        &known_failures_json,
                        &empirical_checks_json,
                        &status,
                        &trust_status,
                        args.created_by.trim(),
                        &now,
                    ),
                ).map_err(rs)?;
                let candidate = candidate_construction_json(&tx, &candidate_construction_id)?;
                let dossier = match &args.dossier_id {
                    Some(dossier_id) => Some(research_dossier_observe_json(&tx, dossier_id)?),
                    None => None,
                };
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "candidate_construction_id": candidate_construction_id,
                    "candidate_construction": candidate,
                    "dossier": dossier,
                })).unwrap())]))
            }
            "candidate_construction_observe" => {
                let args: CandidateConstructionObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                validate_one_of("result", &args.result, CANDIDATE_CONSTRUCTION_OBSERVATION_RESULTS)?;
                if args.description.trim().is_empty() {
                    return Err(mcp_invalid_params("description must be non-empty"));
                }
                let details: serde_json::Value = match &args.details_json {
                    Some(raw) => serde_json::from_str(raw)
                        .map_err(|e| mcp_invalid_params(format!("details_json must be valid JSON: {}", e)))?,
                    None => serde_json::json!({}),
                };

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                let existing_checks_json: Option<String> = tx.query_row(
                    "SELECT empirical_checks_json FROM candidate_constructions WHERE id = ?1",
                    [&args.candidate_construction_id],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(existing_checks_json) = existing_checks_json else {
                    return Err(mcp_invalid_params(format!("unknown candidate_construction_id: {}", args.candidate_construction_id)));
                };
                let mut checks: Vec<serde_json::Value> = serde_json::from_str(&existing_checks_json).unwrap_or_default();
                let now = Utc::now().to_rfc3339();
                checks.push(serde_json::json!({
                    "description": args.description.trim(),
                    "result": args.result,
                    "details": details,
                    "observed_by": args.observed_by,
                    "observed_at": now,
                }));
                let updated_checks_json = serde_json::to_string(&checks).unwrap();
                tx.execute(
                    "UPDATE candidate_constructions SET empirical_checks_json = ?1, updated_at = ?2 WHERE id = ?3",
                    (&updated_checks_json, &now, &args.candidate_construction_id),
                ).map_err(rs)?;
                let candidate = candidate_construction_json(&tx, &args.candidate_construction_id)?;
                let dossier_id = candidate.get("dossier_id").and_then(|v| v.as_str()).map(|s| s.to_string());
                let dossier = match &dossier_id {
                    Some(dossier_id) => Some(research_dossier_observe_json(&tx, dossier_id)?),
                    None => None,
                };
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "candidate_construction_id": args.candidate_construction_id,
                    "candidate_construction": candidate,
                    "dossier": dossier,
                })).unwrap())]))
            }
            "candidate_construction_update_status" => {
                let args: CandidateConstructionUpdateStatusArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.status.is_none() && args.trust_status.is_none()
                    && args.claimed_properties_json.is_none() && args.known_failures_json.is_none() {
                    return Err(mcp_invalid_params("at least one of status, trust_status, claimed_properties_json, known_failures_json must be provided"));
                }
                if let Some(status) = &args.status {
                    validate_one_of("status", status, CANDIDATE_CONSTRUCTION_STATUSES)?;
                }
                if let Some(trust_status) = &args.trust_status {
                    validate_one_of("trust_status", trust_status, CANDIDATE_CONSTRUCTION_TRUST_STATUSES)?;
                }
                if let Some(claimed_properties_json) = &args.claimed_properties_json {
                    serde_json::from_str::<serde_json::Value>(claimed_properties_json)
                        .map_err(|e| mcp_invalid_params(format!("claimed_properties_json must be valid JSON: {}", e)))?;
                }
                if let Some(known_failures_json) = &args.known_failures_json {
                    serde_json::from_str::<serde_json::Value>(known_failures_json)
                        .map_err(|e| mcp_invalid_params(format!("known_failures_json must be valid JSON: {}", e)))?;
                }

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                let existing: Option<(Option<String>, String)> = tx.query_row(
                    "SELECT verification_layer_id, trust_status FROM candidate_constructions WHERE id = ?1",
                    [&args.candidate_construction_id],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                ).optional().map_err(rs)?;
                let Some((existing_verification_layer_id, existing_trust_status)) = existing else {
                    return Err(mcp_invalid_params(format!("unknown candidate_construction_id: {}", args.candidate_construction_id)));
                };
                let trust_status = args.trust_status.clone().unwrap_or(existing_trust_status);
                enforce_kernel_verified_construction_boundary(&tx, &existing_verification_layer_id, &trust_status)?;

                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "UPDATE candidate_constructions SET
                        status = COALESCE(?1, status),
                        trust_status = COALESCE(?2, trust_status),
                        claimed_properties_json = COALESCE(?3, claimed_properties_json),
                        known_failures_json = COALESCE(?4, known_failures_json),
                        updated_at = ?5
                     WHERE id = ?6",
                    (
                        args.status.as_deref(),
                        args.trust_status.as_deref(),
                        args.claimed_properties_json.as_deref(),
                        args.known_failures_json.as_deref(),
                        &now,
                        &args.candidate_construction_id,
                    ),
                ).map_err(rs)?;
                let candidate = candidate_construction_json(&tx, &args.candidate_construction_id)?;
                let dossier_id = candidate.get("dossier_id").and_then(|v| v.as_str()).map(|s| s.to_string());
                let dossier = match &dossier_id {
                    Some(dossier_id) => Some(research_dossier_observe_json(&tx, dossier_id)?),
                    None => None,
                };
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "candidate_construction_id": args.candidate_construction_id,
                    "candidate_construction": candidate,
                    "dossier": dossier,
                })).unwrap())]))
            }
            "candidate_construction_link_node" => {
                let args: CandidateConstructionLinkNodeArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                let existing_dossier_id: Option<Option<String>> = tx.query_row(
                    "SELECT dossier_id FROM candidate_constructions WHERE id = ?1",
                    [&args.candidate_construction_id],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(existing_dossier_id) = existing_dossier_id else {
                    return Err(mcp_invalid_params(format!("unknown candidate_construction_id: {}", args.candidate_construction_id)));
                };
                let node_dossier_id: Option<String> = tx.query_row(
                    "SELECT dossier_id FROM research_nodes WHERE id = ?1",
                    [&args.node_id],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(node_dossier_id) = node_dossier_id else {
                    return Err(mcp_invalid_params(format!("unknown node_id: {}", args.node_id)));
                };
                if let Some(dossier_id) = &existing_dossier_id {
                    if dossier_id != &node_dossier_id {
                        return Err(mcp_invalid_params("node_id belongs to a different dossier than this candidate construction"));
                    }
                }

                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "UPDATE candidate_constructions SET related_node_id = ?1, dossier_id = COALESCE(dossier_id, ?2), updated_at = ?3 WHERE id = ?4",
                    (&args.node_id, &node_dossier_id, &now, &args.candidate_construction_id),
                ).map_err(rs)?;
                let candidate = candidate_construction_json(&tx, &args.candidate_construction_id)?;
                let dossier = research_dossier_observe_json(&tx, &node_dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "candidate_construction_id": args.candidate_construction_id,
                    "candidate_construction": candidate,
                    "dossier": dossier,
                })).unwrap())]))
            }
            "candidate_construction_link_verification_layer" => {
                let args: CandidateConstructionLinkVerificationLayerArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let mut conn = self.conn.lock().await;
                let tx = conn.transaction().map_err(rs)?;
                let existing: Option<(Option<String>, String)> = tx.query_row(
                    "SELECT dossier_id, trust_status FROM candidate_constructions WHERE id = ?1",
                    [&args.candidate_construction_id],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                ).optional().map_err(rs)?;
                let Some((existing_dossier_id, trust_status)) = existing else {
                    return Err(mcp_invalid_params(format!("unknown candidate_construction_id: {}", args.candidate_construction_id)));
                };
                let layer_dossier_id: Option<String> = tx.query_row(
                    "SELECT dossier_id FROM verification_layers WHERE id = ?1",
                    [&args.verification_layer_id],
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(layer_dossier_id) = layer_dossier_id else {
                    return Err(mcp_invalid_params(format!("unknown verification_layer_id: {}", args.verification_layer_id)));
                };
                if let Some(dossier_id) = &existing_dossier_id {
                    if dossier_id != &layer_dossier_id {
                        return Err(mcp_invalid_params("verification_layer_id belongs to a different dossier than this candidate construction"));
                    }
                }
                enforce_kernel_verified_construction_boundary(&tx, &Some(args.verification_layer_id.clone()), &trust_status)?;

                let now = Utc::now().to_rfc3339();
                tx.execute(
                    "UPDATE candidate_constructions SET verification_layer_id = ?1, dossier_id = COALESCE(dossier_id, ?2), updated_at = ?3 WHERE id = ?4",
                    (&args.verification_layer_id, &layer_dossier_id, &now, &args.candidate_construction_id),
                ).map_err(rs)?;
                let candidate = candidate_construction_json(&tx, &args.candidate_construction_id)?;
                let dossier = research_dossier_observe_json(&tx, &layer_dossier_id)?;
                tx.commit().map_err(rs)?;
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&serde_json::json!({
                    "candidate_construction_id": args.candidate_construction_id,
                    "candidate_construction": candidate,
                    "dossier": dossier,
                })).unwrap())]))
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
            "run_envelope_create" => {
                let args: RunEnvelopeCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let mode_str = match args.mode {
                    RunEnvelopeMode::Development => "development",
                    RunEnvelopeMode::Evaluation => "evaluation",
                    RunEnvelopeMode::Benchmark => "benchmark",
                    RunEnvelopeMode::PrivateAudit => "private_audit",
                    RunEnvelopeMode::PublicReport => "public_report",
                };
                let confidence_str = match args.host_cost_confidence.unwrap_or(HostCostConfidence::Unknown) {
                    HostCostConfidence::ExactProviderReceipt => "exact_provider_receipt",
                    HostCostConfidence::ExactLocalMeter => "exact_local_meter",
                    HostCostConfidence::Estimated => "estimated",
                    HostCostConfidence::Attested => "attested",
                    HostCostConfidence::Unknown => "unknown",
                };

                let conn = self.conn.lock().await;
                let run_envelope_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO run_envelopes (
                        id, mode, host_name, host_model, benchmark_suite_name,
                        host_side_cost_micros, host_cost_confidence, notes, created_at, updated_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?9)",
                    (&run_envelope_id, mode_str, &args.host_name, &args.host_model, &args.benchmark_suite_name,
                     &args.host_side_cost_micros, confidence_str, &args.notes, &now),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "run_envelope_id": run_envelope_id,
                    "mode": mode_str,
                    "host_cost_confidence": confidence_str,
                    "created_at": now,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "run_envelope_update" => {
                let args: RunEnvelopeUpdateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let current: Option<(Option<i64>, String, Option<String>)> = conn.query_row(
                    "SELECT host_side_cost_micros, host_cost_confidence, notes FROM run_envelopes WHERE id = ?1",
                    [&args.run_envelope_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
                ).optional().map_err(rs)?;
                let Some((cur_cost, cur_confidence, cur_notes)) = current else {
                    return Err(mcp_invalid_params(format!("unknown run_envelope_id: {}", args.run_envelope_id)));
                };

                let new_cost = args.host_side_cost_micros.or(cur_cost);
                let new_confidence = match args.host_cost_confidence {
                    Some(HostCostConfidence::ExactProviderReceipt) => "exact_provider_receipt".to_string(),
                    Some(HostCostConfidence::ExactLocalMeter) => "exact_local_meter".to_string(),
                    Some(HostCostConfidence::Estimated) => "estimated".to_string(),
                    Some(HostCostConfidence::Attested) => "attested".to_string(),
                    Some(HostCostConfidence::Unknown) => "unknown".to_string(),
                    None => cur_confidence,
                };
                let new_notes = args.notes.or(cur_notes);
                let now = Utc::now().to_rfc3339();

                conn.execute(
                    "UPDATE run_envelopes SET host_side_cost_micros = ?1, host_cost_confidence = ?2, notes = ?3, updated_at = ?4 WHERE id = ?5",
                    (&new_cost, &new_confidence, &new_notes, &now, &args.run_envelope_id),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "run_envelope_id": args.run_envelope_id,
                    "host_side_cost_micros": new_cost,
                    "host_cost_confidence": new_confidence,
                    "updated_at": now,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "run_envelope_attach_episode" => {
                let args: RunEnvelopeAttachEpisodeArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let envelope_mode: Option<String> = conn.query_row(
                    "SELECT mode FROM run_envelopes WHERE id = ?1", [&args.run_envelope_id], |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(envelope_mode) = envelope_mode else {
                    return Err(mcp_invalid_params(format!("unknown run_envelope_id: {}", args.run_envelope_id)));
                };
                let episode_fidelity: Option<String> = conn.query_row(
                    "SELECT pv.fidelity_status FROM episodes e JOIN problem_versions pv ON e.problem_version_id = pv.id WHERE e.id = ?1",
                    [&args.episode_id], |row| row.get(0),
                ).optional().map_err(rs)?;
                let Some(episode_fidelity) = episode_fidelity else {
                    return Err(mcp_invalid_params(format!("unknown episode_id: {}", args.episode_id)));
                };
                enforce_dev_attestation_mode_policy(&episode_fidelity, &envelope_mode, args.allow_dev_attested)?;

                // Sets episodes.run_id only — never touches outcome/state/
                // current_revision or any other proof-status column.
                conn.execute(
                    "UPDATE episodes SET run_id = ?1 WHERE id = ?2",
                    (&args.run_envelope_id, &args.episode_id),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "run_envelope_id": args.run_envelope_id,
                    "episode_id": args.episode_id,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "run_envelope_observe" => {
                let args: RunEnvelopeObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let row: Option<(String, Option<String>, Option<String>, Option<String>, Option<i64>, String, Option<String>, String, String)> = conn.query_row(
                    "SELECT mode, host_name, host_model, benchmark_suite_name, host_side_cost_micros,
                            host_cost_confidence, notes, created_at, updated_at
                     FROM run_envelopes WHERE id = ?1",
                    [&args.run_envelope_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?, row.get(6)?, row.get(7)?, row.get(8)?)),
                ).optional().map_err(rs)?;
                let Some((mode, host_name, host_model, benchmark_suite_name, host_side_cost_micros, host_cost_confidence, notes, created_at, updated_at)) = row else {
                    return Err(mcp_invalid_params(format!("unknown run_envelope_id: {}", args.run_envelope_id)));
                };

                let mut estmt = conn.prepare(
                    "SELECT id, outcome, state FROM episodes WHERE run_id = ?1 ORDER BY created_at ASC"
                ).map_err(rs)?;
                let episodes: Vec<serde_json::Value> = estmt.query_map([&args.run_envelope_id], |row| {
                    Ok(serde_json::json!({
                        "episode_id": row.get::<_, String>(0)?,
                        "outcome": row.get::<_, Option<String>>(1)?,
                        "state": row.get::<_, String>(2)?,
                    }))
                }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;

                let res = serde_json::json!({
                    "run_envelope_id": args.run_envelope_id,
                    "mode": mode,
                    "host_name": host_name,
                    "host_model": host_model,
                    "benchmark_suite_name": benchmark_suite_name,
                    "host_side_cost_micros": host_side_cost_micros,
                    "host_cost_confidence": host_cost_confidence,
                    "notes": notes,
                    "created_at": created_at,
                    "updated_at": updated_at,
                    "episodes": episodes,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "benchmark_suite_create" => {
                let args: BenchmarkSuiteCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.name.trim().is_empty() {
                    return Err(mcp_invalid_params("name must be non-empty"));
                }

                let conn = self.conn.lock().await;
                let suite_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO benchmark_suites (id, name, upstream_url, upstream_commit, language, trusted_canonical_source, imported_at)
                     VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
                    (&suite_id, &args.name, &args.upstream_url, &args.upstream_commit, &args.language, args.trusted_canonical_source, &now),
                ).map_err(|e| if matches!(&e, rusqlite::Error::SqliteFailure(err, _) if err.extended_code == rusqlite::ffi::SQLITE_CONSTRAINT_UNIQUE) {
                    mcp_invalid_params(format!("a benchmark suite named {:?} already exists", args.name))
                } else {
                    rs(e)
                })?;

                let res = serde_json::json!({ "suite_id": suite_id, "name": args.name, "trusted_canonical_source": args.trusted_canonical_source, "created_at": now });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "benchmark_problem_register" => {
                let args: BenchmarkProblemRegisterArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.root_formal_statement.trim().is_empty() || args.theorem_name.trim().is_empty() {
                    return Err(mcp_invalid_params("theorem_name and root_formal_statement must be non-empty"));
                }

                let conn = self.conn.lock().await;
                let suite_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM benchmark_suites WHERE id = ?1", [&args.suite_id], |row| row.get(0),
                ).map_err(rs)?;
                if suite_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown suite_id: {}", args.suite_id)));
                }

                let root_statement_hash = canonical_hash(&args.root_formal_statement).map_err(mcp_internal_error)?;
                // prover_ready_statement is ALWAYS server-derived, never
                // accepted from the client — same principle as
                // root_statement_hash/lean_version/mathlib_commit elsewhere
                // in this schema. A client-supplied conversion would let a
                // caller register an arbitrary (e.g. trivially easy)
                // "prover-ready" text alongside a hard root_formal_statement
                // and have benchmark_result_record's cross-check validate
                // against the wrong one — exactly the fabrication issue #30
                // was built to prevent. to_pi_form is a general Lean 4
                // syntactic fact (named-binder declarations desugar to a
                // Pi-type identically regardless of benchmark suite), so
                // attempting it unconditionally is safe: it fails closed
                // (returns Err, leaving both columns NULL) for any
                // root_formal_statement that isn't a `theorem {theorem_name}
                // (binders) : type` declaration — including a suite whose
                // statements are already bare types needing no conversion.
                let prover_ready_statement = to_pi_form(&args.root_formal_statement, &args.theorem_name)
                    .ok().map(|form| form.root_theorem_statement);
                let prover_ready_statement_hash = prover_ready_statement.as_ref()
                    .map(|s| canonical_hash(s)).transpose().map_err(mcp_internal_error)?;
                let import_manifest_json = serde_json::to_string(&args.import_manifest).unwrap();
                let problem_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO benchmark_problems (
                        id, suite_id, upstream_problem_id, theorem_name, source_file_path,
                        root_formal_statement, root_statement_hash, import_manifest_json,
                        context_hash, prover_ready_statement, prover_ready_statement_hash, status, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, 'imported', ?12)",
                    (&problem_id, &args.suite_id, &args.upstream_problem_id, &args.theorem_name, &args.source_file_path,
                     &args.root_formal_statement, &root_statement_hash, &import_manifest_json, &args.context_hash,
                     &prover_ready_statement, &prover_ready_statement_hash, &now),
                ).map_err(|e| if matches!(&e, rusqlite::Error::SqliteFailure(err, _) if err.extended_code == rusqlite::ffi::SQLITE_CONSTRAINT_UNIQUE) {
                    mcp_invalid_params(format!("problem {:?} is already registered in this suite", args.upstream_problem_id))
                } else {
                    rs(e)
                })?;

                let res = serde_json::json!({
                    "benchmark_problem_id": problem_id,
                    "root_statement_hash": root_statement_hash,
                    "prover_ready_statement_hash": prover_ready_statement_hash,
                    "status": "imported",
                    "created_at": now,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "benchmark_run_create" => {
                let args: BenchmarkRunCreateArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;
                if args.attempt_budget <= 0 {
                    return Err(mcp_invalid_params("attempt_budget must be positive"));
                }

                let conn = self.conn.lock().await;
                let suite_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM benchmark_suites WHERE id = ?1", [&args.suite_id], |row| row.get(0),
                ).map_err(rs)?;
                if suite_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown suite_id: {}", args.suite_id)));
                }
                // Issue #34's required behavior: "A benchmark run should not
                // start unless a run envelope exists." Without one, a run's
                // host/model identity and cost accounting have no home at
                // all — required in the wire schema itself (run_envelope_id
                // is a plain String, not Option<String>), not just checked
                // here, so a client's own JSON schema tooling surfaces this
                // before the call is even made.
                let env_exists: i64 = conn.query_row(
                    "SELECT COUNT(*) FROM run_envelopes WHERE id = ?1", [&args.run_envelope_id], |row| row.get(0),
                ).map_err(rs)?;
                if env_exists == 0 {
                    return Err(mcp_invalid_params(format!("unknown run_envelope_id: {}", args.run_envelope_id)));
                }

                let solve_mode_str = match args.solve_mode {
                    BenchmarkSolveMode::SolveOnly => "solve_only",
                    BenchmarkSolveMode::SubmitModuleAllowed => "submit_module_allowed",
                    BenchmarkSolveMode::SubmitModulePlusDraftPlanning => "submit_module_plus_draft_planning",
                    BenchmarkSolveMode::SubmitModulePlusLibrarian => "submit_module_plus_librarian",
                };
                // lean_version/mathlib_commit are read from the server's OWN
                // detected environment, never accepted from the client — the
                // only trustworthy record of what actually checked any
                // resulting proofs (a client-supplied value could silently
                // misrepresent the toolchain a result was really verified
                // against).
                let (lean_version, mathlib_commit) = match &self.lean_environment {
                    Some(env) => (Some(env.descriptor.clone()), Some(env.mathlib_rev.clone())),
                    None => (None, None),
                };
                let allowed_tools_json = serde_json::to_string(&args.allowed_tools).unwrap();
                let run_id = Uuid::new_v4().to_string();
                let now = Utc::now().to_rfc3339();
                conn.execute(
                    "INSERT INTO benchmark_runs (
                        id, suite_id, run_envelope_id, chatdb_commit, lean_version, mathlib_commit,
                        solve_mode, allowed_tools_json, attempt_budget, wall_clock_budget_ms, lean_timeout_ms, created_at
                    ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12)",
                    (&run_id, &args.suite_id, &args.run_envelope_id, &args.chatdb_commit, &lean_version, &mathlib_commit,
                     solve_mode_str, &allowed_tools_json, args.attempt_budget, &args.wall_clock_budget_ms, &args.lean_timeout_ms, &now),
                ).map_err(rs)?;

                let res = serde_json::json!({
                    "run_id": run_id,
                    "solve_mode": solve_mode_str,
                    "lean_version": lean_version,
                    "mathlib_commit": mathlib_commit,
                    "created_at": now,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "benchmark_result_record" => {
                let args: BenchmarkResultRecordArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let run_row: Option<(String, Option<String>)> = conn.query_row(
                    "SELECT suite_id, run_envelope_id FROM benchmark_runs WHERE id = ?1", [&args.run_id],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                ).optional().map_err(rs)?;
                let Some((run_suite_id, run_envelope_id)) = run_row else {
                    return Err(mcp_invalid_params(format!("unknown run_id: {}", args.run_id)));
                };
                // Issue #38's mode-enforcement policy needs the run's own
                // envelope mode. run_envelope_id has been required since
                // issue #34's fix (v0.3.13), so this is always Some in
                // practice, but query defensively rather than assume.
                let run_envelope_mode: Option<String> = match &run_envelope_id {
                    Some(env_id) => conn.query_row(
                        "SELECT mode FROM run_envelopes WHERE id = ?1", [env_id], |row| row.get(0),
                    ).optional().map_err(rs)?,
                    None => None,
                };
                // COALESCE to prover_ready_statement_hash when present: a
                // benchmark suite's own faithful catalog text
                // (root_formal_statement) is not always the same string a
                // runner actually submits to problem_create/SubmitModule
                // (e.g. PutnamBench's named-binder declaration syntax vs.
                // the Pi-type form ChatDB's model requires) — comparing the
                // wrong hash would reject every legitimate result for such a
                // suite. See migrate_add_prover_ready_statement_columns.
                let problem_row: Option<(String, String)> = conn.query_row(
                    "SELECT suite_id, COALESCE(prover_ready_statement_hash, root_statement_hash) FROM benchmark_problems WHERE id = ?1",
                    [&args.benchmark_problem_id],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                ).optional().map_err(rs)?;
                let Some((problem_suite_id, problem_root_hash)) = problem_row else {
                    return Err(mcp_invalid_params(format!("unknown benchmark_problem_id: {}", args.benchmark_problem_id)));
                };
                if problem_suite_id != run_suite_id {
                    return Err(mcp_invalid_params(format!(
                        "benchmark_problem_id {} belongs to a different suite than run_id {}", args.benchmark_problem_id, args.run_id
                    )));
                }

                let status_str = match args.status {
                    BenchmarkResultStatus::KernelVerified => "kernel_verified",
                    BenchmarkResultStatus::Certified => "certified",
                    BenchmarkResultStatus::Failed => "failed",
                    BenchmarkResultStatus::Timeout => "timeout",
                    BenchmarkResultStatus::InfraError => "infra_error",
                    BenchmarkResultStatus::FormalizationGap => "formalization_gap",
                    BenchmarkResultStatus::Skipped => "skipped",
                };

                // Issue #36's core invariant, enforced concretely: "a proof
                // attempt that bypasses the ledger is not part of ChatDB
                // evidence." A claimed kernel_verified/certified status
                // MUST reference the episode that actually reached it — the
                // checks below (statement-match, outcome-match) only ran
                // when episode_id happened to be given; a caller claiming
                // kernel_verified/certified with NO episode_id at all
                // skipped every check entirely and was accepted with zero
                // backing evidence. Any other status (failed/timeout/
                // infra_error/formalization_gap/skipped) legitimately has
                // no episode to reference — those are unaffected.
                if matches!(status_str, "kernel_verified" | "certified") && args.episode_id.is_none() {
                    return Err(mcp_invalid_params(format!(
                        "status {:?} claims a verified proof but no episode_id was given — a kernel_verified/certified result must reference the episode that actually reached that outcome through the tracked episode_step path (issue #36: a proof attempt that bypasses the ledger is not part of ChatDB evidence)",
                        status_str
                    )));
                }
                // Issue #38's fidelity-basis policy: what evidence, if any,
                // backs a kernel_verified/certified claim's STATEMENT
                // fidelity — deliberately distinct from
                // problem_versions.fidelity_status (whether the formal
                // statement faithfully represents the INFORMAL problem). A
                // trusted, externally-curated suite's own canonical
                // statement-hash match is accepted on its own (PutnamBench:
                // the hash-match against the suite's own catalog text IS the
                // fidelity guarantee); an untrusted/custom suite requires a
                // real independent review (fidelity_status='verified')
                // instead — the hash-match check above only proves the
                // episode proved *some* problem_version with this exact
                // statement, not that anyone ever vouched the statement
                // itself is a faithful formalization.
                let benchmark_fidelity_basis: Option<&str> = if let Some(episode_id) = &args.episode_id {
                    let episode_row: Option<(String, Option<String>)> = conn.query_row(
                        "SELECT problem_version_id, outcome FROM episodes WHERE id = ?1", [episode_id],
                        |row| Ok((row.get(0)?, row.get(1)?)),
                    ).optional().map_err(rs)?;
                    let Some((episode_pv_id, episode_outcome)) = episode_row else {
                        return Err(mcp_invalid_params(format!("unknown episode_id: {}", episode_id)));
                    };
                    let Some(episode_outcome) = episode_outcome else {
                        return Err(mcp_invalid_params(format!(
                            "episode {} has not concluded yet (outcome is not set) — cannot record a benchmark result against an in-progress episode", episode_id
                        )));
                    };
                    // An episode reaching e.g. kernel_verified only proves *something*
                    // was verified — not that it was THIS benchmark problem's statement.
                    // Compare root_statement_hash (server-computed on both sides) rather
                    // than trusting the caller's episode/problem pairing.
                    if let Some(declared_pv) = &args.problem_version_id {
                        if *declared_pv != episode_pv_id {
                            return Err(mcp_invalid_params(format!(
                                "problem_version_id {} does not match episode {}'s actual problem_version_id {}",
                                declared_pv, episode_id, episode_pv_id
                            )));
                        }
                    }
                    let (episode_pv_hash, problem_fidelity_status): (String, String) = conn.query_row(
                        "SELECT root_statement_hash, fidelity_status FROM problem_versions WHERE id = ?1", [&episode_pv_id],
                        |row| Ok((row.get(0)?, row.get(1)?)),
                    ).map_err(rs)?;
                    if episode_pv_hash != problem_root_hash {
                        return Err(mcp_invalid_params(format!(
                            "episode {} proved a different statement (problem_version {}) than benchmark_problem_id {} — root_statement_hash mismatch",
                            episode_id, episode_pv_id, args.benchmark_problem_id
                        )));
                    }
                    if status_str == "kernel_verified" && episode_outcome != "kernel_verified" {
                        return Err(mcp_invalid_params(format!(
                            "status 'kernel_verified' claimed, but episode {} actually reached outcome '{}'", episode_id, episode_outcome
                        )));
                    }
                    if status_str == "certified" && episode_outcome != "certified" {
                        return Err(mcp_invalid_params(format!(
                            "status 'certified' claimed, but episode {} actually reached outcome '{}'", episode_id, episode_outcome
                        )));
                    }
                    if matches!(status_str, "kernel_verified" | "certified") {
                        let suite_trusted: bool = conn.query_row(
                            "SELECT trusted_canonical_source FROM benchmark_suites WHERE id = ?1", [&run_suite_id], |row| row.get(0),
                        ).map_err(rs)?;
                        // Issue #38's mode-enforcement policy, with the
                        // trusted-canonical-hash exemption formalized as its
                        // own named, documented policy function (not an
                        // inline, accidental PutnamBench-shaped special
                        // case) — see trusted_canonical_hash_exemption_applies's
                        // own doc comment for the exact rule and why it exists.
                        if !trusted_canonical_hash_exemption_applies(suite_trusted) {
                            if let Some(mode) = &run_envelope_mode {
                                enforce_dev_attestation_mode_policy(&problem_fidelity_status, mode, args.allow_dev_attested)?;
                            }
                        }
                        if suite_trusted {
                            Some("canonical_statement_hash_match")
                        } else if problem_fidelity_status == "verified" {
                            Some("problem_fidelity_verified")
                        } else {
                            return Err(mcp_invalid_params(format!(
                                "status {:?} claims a verified proof, and the statement hash matches benchmark_problem_id {}, but suite {} is not trusted_canonical_source AND problem_version {} has not been independently fidelity-reviewed (fidelity_status={:?}) — a benchmark result claiming kernel_verified/certified needs either a trusted suite's canonical statement match or a real problem_submit_fidelity_review (issue #38's fidelity-basis policy)",
                                status_str, args.benchmark_problem_id, run_suite_id, episode_pv_id, problem_fidelity_status
                            )));
                        }
                    } else {
                        // An episode_id was given, but for a non-proof-claiming
                        // status (failed/timeout/infra_error/formalization_gap/
                        // skipped) -- no proof claim, so no fidelity basis to report.
                        Some("none")
                    }
                } else {
                    // No episode_id -> no proof claim -> no fidelity basis to report.
                    Some("none")
                };

                let existing_id: Option<String> = conn.query_row(
                    "SELECT id FROM benchmark_results WHERE run_id = ?1 AND benchmark_problem_id = ?2",
                    (&args.run_id, &args.benchmark_problem_id),
                    |row| row.get(0),
                ).optional().map_err(rs)?;
                let now = Utc::now().to_rfc3339();
                let result_id = existing_id.clone().unwrap_or_else(|| Uuid::new_v4().to_string());
                if let Some(existing_id) = &existing_id {
                    conn.execute(
                        "UPDATE benchmark_results SET
                            problem_version_id = ?1, episode_id = ?2, status = ?3, outcome = ?4, pass_at = ?5,
                            attempts_used = ?6, time_to_first_success_ms = ?7, cost_micros = ?8,
                            final_diagnostic_category = ?9, proof_artifact_hash = ?10, trajectory_export_hash = ?11,
                            replay_status = ?12, benchmark_fidelity_basis = ?13, updated_at = ?14
                         WHERE id = ?15",
                        (&args.problem_version_id, &args.episode_id, status_str, &args.outcome, &args.pass_at,
                         args.attempts_used, &args.time_to_first_success_ms, &args.cost_micros,
                         &args.final_diagnostic_category, &args.proof_artifact_hash, &args.trajectory_export_hash,
                         &args.replay_status, &benchmark_fidelity_basis, &now, existing_id),
                    ).map_err(rs)?;
                } else {
                    conn.execute(
                        "INSERT INTO benchmark_results (
                            id, run_id, benchmark_problem_id, problem_version_id, episode_id, status, outcome,
                            pass_at, attempts_used, time_to_first_success_ms, cost_micros, final_diagnostic_category,
                            proof_artifact_hash, trajectory_export_hash, replay_status, benchmark_fidelity_basis, created_at, updated_at
                        ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9, ?10, ?11, ?12, ?13, ?14, ?15, ?16, ?17, ?17)",
                        rusqlite::params![&result_id, &args.run_id, &args.benchmark_problem_id, &args.problem_version_id, &args.episode_id,
                         status_str, &args.outcome, &args.pass_at, args.attempts_used, &args.time_to_first_success_ms,
                         &args.cost_micros, &args.final_diagnostic_category, &args.proof_artifact_hash,
                         &args.trajectory_export_hash, &args.replay_status, &benchmark_fidelity_basis, &now],
                    ).map_err(rs)?;
                }

                let res = serde_json::json!({
                    "result_id": result_id,
                    "run_id": args.run_id,
                    "benchmark_problem_id": args.benchmark_problem_id,
                    "benchmark_fidelity_basis": benchmark_fidelity_basis,
                    "status": status_str,
                    "updated": existing_id.is_some(),
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            "benchmark_run_observe" => {
                let args: BenchmarkRunObserveArgs = serde_json::from_value(args_val)
                    .map_err(|e| mcp_invalid_params(format!("Invalid params: {}", e)))?;

                let conn = self.conn.lock().await;
                let run_row: Option<(String, Option<String>, Option<String>, Option<String>, Option<String>, String, String, i64, Option<i64>, Option<i64>, String)> = conn.query_row(
                    "SELECT suite_id, run_envelope_id, chatdb_commit, lean_version, mathlib_commit, solve_mode,
                            allowed_tools_json, attempt_budget, wall_clock_budget_ms, lean_timeout_ms, created_at
                     FROM benchmark_runs WHERE id = ?1",
                    [&args.run_id],
                    |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?, row.get(4)?, row.get(5)?, row.get(6)?, row.get(7)?, row.get(8)?, row.get(9)?, row.get(10)?)),
                ).optional().map_err(rs)?;
                let Some((suite_id, run_envelope_id, chatdb_commit, lean_version, mathlib_commit, solve_mode, allowed_tools_json, attempt_budget, wall_clock_budget_ms, lean_timeout_ms, created_at)) = run_row else {
                    return Err(mcp_invalid_params(format!("unknown run_id: {}", args.run_id)));
                };

                let mut rstmt = conn.prepare(
                    "SELECT r.benchmark_problem_id, p.theorem_name, r.status, r.outcome, r.pass_at, r.attempts_used,
                            r.time_to_first_success_ms, r.cost_micros, r.final_diagnostic_category, r.replay_status,
                            r.benchmark_fidelity_basis, r.episode_id
                     FROM benchmark_results r JOIN benchmark_problems p ON p.id = r.benchmark_problem_id
                     WHERE r.run_id = ?1 ORDER BY p.upstream_problem_id ASC"
                ).map_err(rs)?;
                let rows: Vec<(serde_json::Value, Option<String>)> = rstmt.query_map([&args.run_id], |row| {
                    Ok((serde_json::json!({
                        "benchmark_problem_id": row.get::<_, String>(0)?,
                        "theorem_name": row.get::<_, String>(1)?,
                        "status": row.get::<_, String>(2)?,
                        "outcome": row.get::<_, Option<String>>(3)?,
                        "pass_at": row.get::<_, Option<i64>>(4)?,
                        "attempts_used": row.get::<_, i64>(5)?,
                        "time_to_first_success_ms": row.get::<_, Option<i64>>(6)?,
                        "cost_micros": row.get::<_, Option<i64>>(7)?,
                        "final_diagnostic_category": row.get::<_, Option<String>>(8)?,
                        "replay_status": row.get::<_, Option<String>>(9)?,
                        "benchmark_fidelity_basis": row.get::<_, Option<String>>(10)?,
                    }), row.get::<_, Option<String>>(11)?))
                }).map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                let results: Vec<serde_json::Value> = rows.iter().map(|(v, _)| v.clone()).collect();

                // Issue #38's cost policy (redesigned after real product
                // direction): verifier_wall_time_ms/verifier_cpu_time_ms sum
                // the real Lean invocation timing persisted on
                // action_attempts.lean_result_json (see
                // step.rs::attempt_finalize) across every attempt on every
                // episode this run's results reference. Each is tracked with
                // its own "found any data" flag since LeanModuleVerificationResult
                // (the SubmitModule path) has no cpu-time field at all — an
                // attempt can contribute wall time without contributing cpu
                // time. mcp_action_count is a real, always-available count
                // (0 is a genuine count, not a stand-in for "unmeasured").
                let mut verifier_wall_time_ms_total: i64 = 0;
                let mut verifier_wall_time_found = false;
                let mut verifier_cpu_time_ms_total: i64 = 0;
                let mut verifier_cpu_time_found = false;
                let mut mcp_action_count: i64 = 0;
                for episode_id in rows.iter().filter_map(|(_, ep)| ep.as_ref()) {
                    let mut jstmt = conn.prepare(
                        "SELECT lean_result_json FROM action_attempts WHERE episode_id = ?1"
                    ).map_err(rs)?;
                    let jsons: Vec<Option<String>> = jstmt.query_map([episode_id], |row| row.get(0))
                        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                    mcp_action_count += jsons.len() as i64;
                    for j in jsons.iter().flatten() {
                        if let Ok(parsed) = serde_json::from_str::<serde_json::Value>(j) {
                            if let Some(wall_ms) = parsed.get("wall_time_ms").and_then(|v| v.as_i64()) {
                                verifier_wall_time_ms_total += wall_ms;
                                verifier_wall_time_found = true;
                            }
                            if let Some(cpu_ms) = parsed.get("lean_cpu_time_ms").and_then(|v| v.as_i64()) {
                                verifier_cpu_time_ms_total += cpu_ms;
                                verifier_cpu_time_found = true;
                            }
                        }
                    }
                }
                let verifier_wall_time_ms: Option<i64> = if verifier_wall_time_found { Some(verifier_wall_time_ms_total) } else { None };
                let verifier_cpu_time_ms: Option<i64> = if verifier_cpu_time_found { Some(verifier_cpu_time_ms_total) } else { None };

                // model_call_reported_cost_micros: real per-attempt cost data
                // already stored in model_call_leases (issue #34's audit
                // finding), but ALWAYS self-reported by the runner/host, never
                // independently measured by ChatDB — so it is bucketed at
                // "attested" confidence, never merged into an exact total.
                let mut model_call_cost_total: i64 = 0;
                let mut model_call_cost_found = false;
                for episode_id in rows.iter().filter_map(|(_, ep)| ep.as_ref()) {
                    let mut mstmt = conn.prepare(
                        "SELECT actual_cost_micros FROM model_call_leases WHERE episode_id = ?1 AND status = 'settled' AND actual_cost_micros IS NOT NULL"
                    ).map_err(rs)?;
                    let amounts: Vec<i64> = mstmt.query_map([episode_id], |row| row.get(0))
                        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                    for a in amounts {
                        model_call_cost_total += a;
                        model_call_cost_found = true;
                    }
                }
                let model_call_reported_cost_micros: Option<i64> = if model_call_cost_found { Some(model_call_cost_total) } else { None };
                let model_call_cost_confidence: Option<&str> = if model_call_cost_found { Some("attested") } else { None };

                // storage_bytes_written: real byte length (Rust String::len(),
                // never SQLite's character-counting LENGTH()) of the
                // lean_result_json actually persisted per attempt (see
                // step.rs::attempt_finalize), summed across every attempt on
                // every episode this run's results reference — the same
                // per-episode iteration pattern as verifier_wall_time_ms above.
                let mut storage_bytes_total: i64 = 0;
                let mut storage_bytes_found = false;
                for episode_id in rows.iter().filter_map(|(_, ep)| ep.as_ref()) {
                    let mut bstmt = conn.prepare(
                        "SELECT lean_result_bytes FROM action_attempts WHERE episode_id = ?1 AND lean_result_bytes IS NOT NULL"
                    ).map_err(rs)?;
                    let amounts: Vec<i64> = bstmt.query_map([episode_id], |row| row.get(0))
                        .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                    for b in amounts {
                        storage_bytes_total += b;
                        storage_bytes_found = true;
                    }
                }
                let storage_bytes_written: Option<i64> = if storage_bytes_found { Some(storage_bytes_total) } else { None };

                // Issue #38's MCP-side/storage-export observability:
                // mcp_call_metrics (populated generically for every tool call
                // in call_tool's wrapper) is correlated to this run three
                // ways at once — by episode_id (any of this run's episodes),
                // by run_id (a call that referenced this benchmark run
                // directly, e.g. benchmark_result_record/benchmark_run_observe
                // itself), or by run_envelope_id (a call tied to this run's
                // own envelope, e.g. model_call_reserve/settle). A call
                // matching more than one of these criteria is only counted
                // once (DISTINCT id via UNION, not summed per-criterion).
                // storage_export_bytes/storage_export_wall_time_ms further
                // restrict to proof_export/trajectory_export specifically —
                // the actual "export" surface.
                let episode_ids: Vec<&String> = rows.iter().filter_map(|(_, ep)| ep.as_ref()).collect();
                let episode_placeholders = if episode_ids.is_empty() { "''".to_string() } else {
                    episode_ids.iter().map(|_| "?").collect::<Vec<_>>().join(",")
                };
                let correlation_sql = format!(
                    "episode_id IN ({episode_placeholders}) OR run_id = ? OR run_envelope_id = ?"
                );
                let mut mcp_params: Vec<&dyn rusqlite::ToSql> = Vec::new();
                for eid in &episode_ids { mcp_params.push(*eid as &dyn rusqlite::ToSql); }
                mcp_params.push(&args.run_id as &dyn rusqlite::ToSql);
                let run_envelope_id_param: &dyn rusqlite::ToSql = &run_envelope_id;
                mcp_params.push(run_envelope_id_param);

                let mut mcp_time_stmt = conn.prepare(
                    &format!("SELECT wall_time_ms FROM mcp_call_metrics WHERE {correlation_sql}")
                ).map_err(rs)?;
                let mcp_wall_times: Vec<i64> = mcp_time_stmt.query_map(mcp_params.as_slice(), |row| row.get(0))
                    .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                let mcp_handler_wall_time_ms: Option<i64> = if mcp_wall_times.is_empty() { None } else { Some(mcp_wall_times.iter().sum()) };

                let mut export_stmt = conn.prepare(
                    &format!("SELECT wall_time_ms, response_bytes FROM mcp_call_metrics WHERE tool_name IN ('proof_export', 'trajectory_export') AND ({correlation_sql})")
                ).map_err(rs)?;
                let export_rows: Vec<(i64, Option<i64>)> = export_stmt.query_map(mcp_params.as_slice(), |row| Ok((row.get(0)?, row.get(1)?)))
                    .map_err(rs)?.collect::<Result<Vec<_>, _>>().map_err(rs)?;
                let storage_export_wall_time_ms: Option<i64> = if export_rows.is_empty() { None } else { Some(export_rows.iter().map(|(w, _)| w).sum()) };
                let storage_export_bytes: Option<i64> = {
                    let found: Vec<i64> = export_rows.iter().filter_map(|(_, b)| *b).collect();
                    if found.is_empty() { None } else { Some(found.iter().sum()) }
                };

                let is_solved = |r: &serde_json::Value| matches!(r["status"].as_str(), Some("kernel_verified") | Some("certified"));
                let solved = results.iter().filter(|r| is_solved(r)).count();
                let total = results.len();
                let total_attempts: i64 = results.iter().filter_map(|r| r["attempts_used"].as_i64()).sum();
                // pass@1: solved AND the first attempt was the one that succeeded.
                // `pass_at` (attempt index of first success) is the authoritative
                // signal when the caller supplies it; fall back to attempts_used == 1
                // when it's absent, since attempts_used is a required field. Distinct
                // from `solved_count`/overall solve rate, which counts a problem solved
                // within the run's attempt_budget regardless of how many tries it took.
                let solved_on_first_attempt = results.iter().filter(|r| {
                    is_solved(r) && match r["pass_at"].as_i64() {
                        Some(p) => p == 1,
                        None => r["attempts_used"].as_i64() == Some(1),
                    }
                }).count();
                let metrics = serde_json::json!({
                    "problems_attempted": total,
                    "solved_count": solved,
                    "solved_rate": if total > 0 { solved as f64 / total as f64 } else { 0.0 },
                    "pass_at_1_rate": if total > 0 { solved_on_first_attempt as f64 / total as f64 } else { 0.0 },
                    "kernel_verified_count": results.iter().filter(|r| r["status"] == "kernel_verified").count(),
                    "certified_count": results.iter().filter(|r| r["status"] == "certified").count(),
                    "average_attempts_per_result": if total > 0 { total_attempts as f64 / total as f64 } else { 0.0 },
                });

                // Issue #38's cost policy, redesigned per explicit product
                // direction: metrics first (time/count/bytes are real,
                // reported honestly), monetary cost fields (*_cost_micros)
                // ONLY populated when real money data exists, and a
                // three-tier monetary rollup that never merges a
                // self-reported (attested) or estimated figure into an
                // "exact total" claim.
                let (host_side_cost_micros, host_cost_confidence): (Option<i64>, Option<String>) = match &run_envelope_id {
                    Some(env_id) => conn.query_row(
                        "SELECT host_side_cost_micros, host_cost_confidence FROM run_envelopes WHERE id = ?1",
                        [env_id], |row| Ok((row.get(0)?, row.get(1)?)),
                    ).optional().map_err(rs)?.unwrap_or((None, None)),
                    None => (None, None),
                };

                // Bucket every known monetary figure by its own confidence
                // tier. "unknown"-confidence host cost is deliberately
                // excluded from every bucket (its reliability is explicitly
                // unvouched-for) but still surfaced verbatim in
                // host_side_cost_micros for transparency.
                let mut known_exact_cost_micros: Option<i64> = None;
                let mut reported_attested_cost_micros: Option<i64> = None;
                let mut estimated_cost_micros: Option<i64> = None;
                if let Some(amount) = host_side_cost_micros {
                    match host_cost_confidence.as_deref() {
                        Some("exact_provider_receipt") | Some("exact_local_meter") => {
                            known_exact_cost_micros = Some(known_exact_cost_micros.unwrap_or(0) + amount);
                        }
                        Some("estimated") => {
                            estimated_cost_micros = Some(estimated_cost_micros.unwrap_or(0) + amount);
                        }
                        Some("attested") => {
                            reported_attested_cost_micros = Some(reported_attested_cost_micros.unwrap_or(0) + amount);
                        }
                        _ => {} // "unknown" or unset: real number, unvouched reliability — not bucketed.
                    }
                }
                if let Some(amount) = model_call_reported_cost_micros {
                    // model_call_reported_cost_micros is always "attested" tier today
                    // (no mechanism yet to attach a provider receipt to a lease).
                    reported_attested_cost_micros = Some(reported_attested_cost_micros.unwrap_or(0) + amount);
                }

                // mcp_side_cost_micros/storage_export_cost_micros have no meter
                // or rate card yet — always null, never fabricated as zero.
                // Their absence alone is enough to keep unknown_cost_present
                // true until real instrumentation lands for them.
                let mcp_side_cost_micros: Option<i64> = None;
                let storage_export_cost_micros: Option<i64> = None;
                let unknown_cost_present = mcp_side_cost_micros.is_none()
                    || storage_export_cost_micros.is_none()
                    || matches!(host_cost_confidence.as_deref(), None | Some("unknown"));

                // total_cost_known requires EVERY material cost surface to be
                // exact — currently unreachable in practice, since mcp_side/
                // storage_export costs have no instrumentation at all yet;
                // that's the honest, correct state until they do.
                // reported_total_not_exact: some real monetary signal exists
                // (exact, attested, or estimated) but the report can't yet
                // vouch for a complete exact total.
                // total_cost_incomplete: no monetary signal at all.
                let cost_completeness = if !unknown_cost_present && estimated_cost_micros.is_none() && reported_attested_cost_micros.is_none() && known_exact_cost_micros.is_some() {
                    "total_cost_known"
                } else if known_exact_cost_micros.is_some() || reported_attested_cost_micros.is_some() || estimated_cost_micros.is_some() {
                    "reported_total_not_exact"
                } else {
                    "total_cost_incomplete"
                };

                let cost_summary = serde_json::json!({
                    "host_side_cost_micros": host_side_cost_micros,
                    "host_cost_confidence": host_cost_confidence,
                    "model_call_reported_cost_micros": model_call_reported_cost_micros,
                    "model_call_cost_confidence": model_call_cost_confidence,
                    "verifier_wall_time_ms": verifier_wall_time_ms,
                    "verifier_cpu_time_ms": verifier_cpu_time_ms,
                    "mcp_action_count": mcp_action_count,
                    "mcp_handler_wall_time_ms": mcp_handler_wall_time_ms,
                    "mcp_side_cost_micros": mcp_side_cost_micros,
                    "storage_bytes_written": storage_bytes_written,
                    "storage_export_bytes": storage_export_bytes,
                    "storage_export_wall_time_ms": storage_export_wall_time_ms,
                    "storage_export_cost_micros": storage_export_cost_micros,
                    "known_exact_cost_micros": known_exact_cost_micros,
                    "reported_attested_cost_micros": reported_attested_cost_micros,
                    "estimated_cost_micros": estimated_cost_micros,
                    "unknown_cost_present": unknown_cost_present,
                    "cost_completeness": cost_completeness,
                    "not_yet_instrumented": "mcp_side_cost_micros/storage_export_cost_micros are not yet instrumented — never reported as zero; there is no pricing/rate-card decision yet for either surface. mcp_handler_wall_time_ms/storage_bytes_written/storage_export_bytes/storage_export_wall_time_ms are now real, measured metrics (v0.3.23) — null only when this run genuinely has no correlated mcp_call_metrics/action_attempts rows yet, never fabricated as zero. model_call_reported_cost_micros is real per-attempt data from model_call_leases but always self-reported (attested), never independently measured by ChatDB.",
                });

                let res = serde_json::json!({
                    "run_id": args.run_id,
                    "suite_id": suite_id,
                    "run_envelope_id": run_envelope_id,
                    "chatdb_commit": chatdb_commit,
                    "lean_version": lean_version,
                    "mathlib_commit": mathlib_commit,
                    "solve_mode": solve_mode,
                    "allowed_tools": serde_json::from_str::<serde_json::Value>(&allowed_tools_json).unwrap_or(serde_json::Value::Array(vec![])),
                    "attempt_budget": attempt_budget,
                    "wall_clock_budget_ms": wall_clock_budget_ms,
                    "lean_timeout_ms": lean_timeout_ms,
                    "created_at": created_at,
                    "results": results,
                    "metrics": metrics,
                    "cost_summary": cost_summary,
                });
                Ok(CallToolResult::success(vec![Content::text(serde_json::to_string(&res).unwrap())]))
            }
            _ => Err(McpError::new(ErrorCode::METHOD_NOT_FOUND, format!("Method not found: {}", request.name), None)),
            }
        }.await;

        // Persist this call's real wall-clock time (and, for a successful
        // call, the real byte length of its returned content) — best-effort:
        // a metrics-logging failure must never affect the actual tool
        // response the caller receives, so errors here are swallowed, never
        // propagated or allowed to overwrite `result`.
        let wall_time_ms = call_start.elapsed().as_millis() as i64;
        let (is_error, response_bytes): (bool, Option<i64>) = match &result {
            Ok(r) => (
                r.is_error.unwrap_or(false),
                r.content.first().and_then(|c| c.as_text()).map(|t| t.text.len() as i64),
            ),
            Err(_) => (true, None),
        };
        {
            let conn = self.conn.lock().await;
            let _ = conn.execute(
                "INSERT INTO mcp_call_metrics (id, tool_name, episode_id, run_id, run_envelope_id, wall_time_ms, response_bytes, is_error, created_at)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8, ?9)",
                rusqlite::params![
                    Uuid::new_v4().to_string(), &tool_name, &corr_episode_id, &corr_run_id, &corr_run_envelope_id,
                    wall_time_ms, response_bytes, is_error, Utc::now().to_rfc3339(),
                ],
            );
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Issue #38's trusted-canonical-hash exemption, unit-tested directly as
    /// its own named policy (not just incidentally exercised through the
    /// larger benchmark_result_record integration tests below).
    #[test]
    fn test_trusted_canonical_hash_exemption_applies() {
        assert!(trusted_canonical_hash_exemption_applies(true),
            "a trusted_canonical_source suite's claim always resolves to canonical_statement_hash_match, so the exemption must apply");
        assert!(!trusted_canonical_hash_exemption_applies(false),
            "an untrusted suite gets no exemption — mode-enforcement must still run for it");
    }

    /// Issue #38's mode-enforcement policy function, unit-tested directly.
    #[test]
    fn test_enforce_dev_attestation_mode_policy() {
        // Any fidelity_status other than "attested" is allowed in any mode.
        assert!(enforce_dev_attestation_mode_policy("verified", "benchmark", false).is_ok());
        assert!(enforce_dev_attestation_mode_policy("unreviewed", "public_report", false).is_ok());

        // "attested" is unconditionally blocked for these three modes, flag or not.
        for mode in ["benchmark", "evaluation", "public_report"] {
            assert!(enforce_dev_attestation_mode_policy("attested", mode, false).is_err());
            assert!(enforce_dev_attestation_mode_policy("attested", mode, true).is_err(),
                "allow_dev_attested must NOT override benchmark/evaluation/public_report, per the policy's own spec");
        }

        // development: always allowed.
        assert!(enforce_dev_attestation_mode_policy("attested", "development", false).is_ok());

        // private_audit: blocked without the flag, allowed with it.
        assert!(enforce_dev_attestation_mode_policy("attested", "private_audit", false).is_err());
        assert!(enforce_dev_attestation_mode_policy("attested", "private_audit", true).is_ok());
    }

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

    /// Issue #35 acceptance: readme_first exists, is listed, and its content
    /// covers all five required sections (loop, trust boundary, proof
    /// attempts, cost boundary, benchmark mode) — checked structurally (as
    /// distinct JSON keys), not by fragile substring matching on prose.
    #[tokio::test]
    async fn test_readme_first_covers_required_sections() {
        let client = connected_client(test_handler()).await;
        let list_res = client.peer().list_tools(None).await.unwrap();
        assert!(list_res.tools.iter().any(|t| t.name == "readme_first"), "{:?}", list_res.tools.iter().map(|t| &t.name).collect::<Vec<_>>());

        let res = tool_json(&client.peer().call_tool(CallToolRequestParams::new("readme_first")).await.unwrap());
        assert!(res["the_loop"].as_str().unwrap().contains("episode_step"), "{:?}", res);
        assert!(res["trust_boundary"].as_str().unwrap().contains("evidence"), "{:?}", res);
        assert!(res["proof_attempts"]["rule"].as_str().unwrap().contains("episode_step"), "{:?}", res);
        assert!(res["cost_boundary"].as_str().unwrap().to_lowercase().contains("cost"), "{:?}", res);
        assert!(res["benchmark_mode"].as_str().unwrap().to_lowercase().contains("benchmark"), "{:?}", res);
    }

    #[tokio::test]
    async fn test_mcp_list_tools_and_describe() {
        let client = connected_client(test_handler()).await;

        let list_res = client.peer().list_tools(None).await.unwrap();
        assert_eq!(list_res.tools.len(), 54);

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

        // Issue #34's tool-classification audit: an honest count, tied to the
        // REAL number of registered tools (list_res.tools.len(), asserted
        // above) rather than a hand-maintained figure that could silently
        // drift out of sync with the actual tool surface as tools are added.
        let classification = &json["tool_classification"];
        let classified = classification["tools"].as_object().unwrap();
        assert_eq!(classification["classified_tool_count"].as_u64().unwrap() as usize, classified.len(),
            "classified_tool_count must match the real number of entries in the map: {classification}");
        assert_eq!(classification["total_tool_count"].as_u64().unwrap(), list_res.tools.len() as u64,
            "total_tool_count must match the real, registered tool count, not a hand-maintained figure that can drift: {classification}");
        assert_eq!(classification["classified_tool_count"], classification["total_tool_count"],
            "as of this audit pass, every registered tool has a classification entry — if a new tool is added without one, this must fail rather than silently under-count");
        // Every classified tool, not just a spot-check sample — catches a
        // future edit that adds a tool entry missing one of the 8 dimensions,
        // or that drops a dimension while editing an existing entry.
        for (tool, entry) in classified {
            for dim in ["side_effect", "trust_level", "cost_surface", "benchmark_safety", "replayability", "source_code_impact", "artifact_risk", "required_run_mode"] {
                assert!(entry[dim].is_string() && !entry[dim].as_str().unwrap().is_empty(),
                    "tool_classification.{tool}.{dim} must be a real, non-empty classification: {entry}");
            }
        }
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

    struct CountingMcpGateway {
        calls: Arc<std::sync::atomic::AtomicUsize>,
    }
    impl LeanGateway for CountingMcpGateway {
        fn verify_exact(
            &self,
            obligation: &Obligation,
            _p: &str,
            _d: &[Uuid],
            environment: &str,
            _m: &[String],
        ) -> Result<LeanVerificationResult, String> {
            self.calls.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
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

    async fn create_claimed_episode(
        peer: &rmcp::service::Peer<rmcp::RoleClient>,
        cost_budget_micros: Option<i64>,
        idempotency_key: &str,
    ) -> (String, i64, String, String) {
        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "budget regression",
            "root_formal_statement": "True",
            "unsafe_dev_attestation": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let mut episode_args = serde_json::json!({
            "problem_version_id": create["problem_version_id"],
            "max_steps": 5,
        });
        if let Some(cost_budget_micros) = cost_budget_micros {
            episode_args["cost_budget_micros"] = serde_json::json!(cost_budget_micros);
        }
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(
            episode_args.as_object().unwrap().clone()
        )).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let revision = req["episode_revision"].as_i64().unwrap();
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id,
            "action_request_id": req["id"],
            "idempotency_key": idempotency_key,
            "expected_revision": revision,
        }).as_object().unwrap().clone())).await.unwrap());
        (
            episode_id,
            revision,
            claim["action_attempt_id"].as_str().unwrap().to_string(),
            claim["claim_token"].as_str().unwrap().to_string(),
        )
    }

    async fn reserve_model_call(
        peer: &rmcp::service::Peer<rmcp::RoleClient>,
        episode_id: &str,
        action_attempt_id: &str,
        reserved_cost_micros: i64,
    ) -> String {
        let lease = tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_reserve").with_arguments(serde_json::json!({
            "episode_id": episode_id,
            "action_attempt_id": action_attempt_id,
            "runner_id": "budget-test-runner",
            "declared_model": "budget-test-model",
            "max_input_tokens": 100,
            "max_output_tokens": 100,
            "reserved_cost_micros": reserved_cost_micros,
        }).as_object().unwrap().clone())).await.unwrap());
        lease["lease_id"].as_str().unwrap().to_string()
    }

    fn episode_budget(conn: &Connection, episode_id: &str) -> Option<i64> {
        conn.query_row(
            "SELECT cost_budget_micros FROM episodes WHERE id = ?1",
            [episode_id],
            |row| row.get(0),
        ).unwrap()
    }

    #[tokio::test]
    async fn test_episode_step_rejects_negative_cost_at_mcp_boundary_without_budget_credit() {
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
        let (episode_id, revision, attempt_id, claim_token) =
            create_claimed_episode(&peer, Some(100), "negative-mcp-boundary").await;

        let rejected = peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id.clone(),
            "action_attempt_id": attempt_id,
            "expected_revision": revision,
            "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "trivial"},
            "cost_micros": -1,
        }).as_object().unwrap().clone())).await;

        assert!(rejected.is_err(), "negative MCP cost must be rejected: {:?}", rejected);
        let budget = {
            let conn = conn_arc.lock().await;
            episode_budget(&conn, &episode_id)
        };
        assert_eq!(budget, Some(100), "rejected negative cost must not credit the budget");
    }

    #[tokio::test]
    async fn test_episode_step_over_budget_denied_before_gateway_execution() {
        let calls = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let conn_arc = Arc::new(Mutex::new(conn));
        let handler = ChatDbMcp {
            conn: conn_arc.clone(),
            gateway: Box::new(CountingMcpGateway { calls: calls.clone() }),
            lean_available: false,
            lean_environment: None,
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();
        let (episode_id, revision, attempt_id, claim_token) =
            create_claimed_episode(&peer, Some(100), "over-budget-step").await;

        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id.clone(),
            "action_attempt_id": attempt_id,
            "expected_revision": revision,
            "claim_token": claim_token,
            "action": {"type": "solve", "proof_term": "trivial"},
            "cost_micros": 101,
        }).as_object().unwrap().clone())).await.unwrap());

        assert_eq!(step["disposition"], "error", "{:?}", step);
        assert!(step["diagnostics"].as_str().unwrap_or("").contains("budget_denied"), "{:?}", step);
        assert_eq!(calls.load(std::sync::atomic::Ordering::SeqCst), 0, "gateway must not run after budget denial");
        let budget = {
            let conn = conn_arc.lock().await;
            episode_budget(&conn, &episode_id)
        };
        assert_eq!(budget, Some(100), "denied step must leave budget unchanged");
    }

    #[tokio::test]
    async fn test_model_call_reserve_debits_budget_and_prevents_over_reservation() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(100), "reserve-debits").await;

        let first_lease = reserve_model_call(&peer, &episode_id, &attempt_id, 60).await;
        assert!(!first_lease.is_empty());
        {
            let conn = conn_arc.lock().await;
            assert_eq!(episode_budget(&conn, &episode_id), Some(40));
        }

        let denied = peer.call_tool(CallToolRequestParams::new("model_call_reserve").with_arguments(serde_json::json!({
            "episode_id": episode_id.clone(),
            "action_attempt_id": attempt_id.clone(),
            "runner_id": "budget-test-runner",
            "declared_model": "budget-test-model",
            "max_input_tokens": 100,
            "max_output_tokens": 100,
            "reserved_cost_micros": 41,
        }).as_object().unwrap().clone())).await;
        assert!(denied.is_err(), "second lease must not over-reserve same remaining budget");
        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(40));
        let lease_count: i64 = conn.query_row(
            "SELECT COUNT(*) FROM model_call_leases WHERE episode_id = ?1",
            [&episode_id],
            |row| row.get(0),
        ).unwrap();
        assert_eq!(lease_count, 1, "denied reservation must not insert a lease");
    }

    #[tokio::test]
    async fn test_model_call_reserve_rejects_negative_reserved_cost_without_budget_credit() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(100), "negative-model-reserve").await;

        let rejected = peer.call_tool(CallToolRequestParams::new("model_call_reserve").with_arguments(serde_json::json!({
            "episode_id": episode_id.clone(),
            "action_attempt_id": attempt_id,
            "runner_id": "budget-test-runner",
            "declared_model": "budget-test-model",
            "max_input_tokens": 100,
            "max_output_tokens": 100,
            "reserved_cost_micros": -1,
        }).as_object().unwrap().clone())).await;

        assert!(rejected.is_err(), "negative reserved cost must be rejected");
        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(100));
        let lease_count: i64 = conn.query_row(
            "SELECT COUNT(*) FROM model_call_leases WHERE episode_id = ?1",
            [&episode_id],
            |row| row.get(0),
        ).unwrap();
        assert_eq!(lease_count, 0, "negative reservation must not insert a lease");
    }

    #[tokio::test]
    async fn test_model_call_settle_lower_actual_refunds_delta() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(100), "settle-lower").await;
        let lease_id = reserve_model_call(&peer, &episode_id, &attempt_id, 60).await;

        tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id,
            "actual_cost_micros": 25,
            "status": "settled",
        }).as_object().unwrap().clone())).await.unwrap());

        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(75), "settlement must refund reserved - actual");
    }

    #[tokio::test]
    async fn test_model_call_settle_rejects_negative_actual_without_budget_change() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(100), "negative-model-settle").await;
        let lease_id = reserve_model_call(&peer, &episode_id, &attempt_id, 40).await;

        let rejected = peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id.clone(),
            "actual_cost_micros": -1,
            "status": "settled",
        }).as_object().unwrap().clone())).await;

        assert!(rejected.is_err(), "negative actual cost must be rejected");
        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(60));
        let status: String = conn.query_row(
            "SELECT status FROM model_call_leases WHERE id = ?1",
            [&lease_id],
            |row| row.get(0),
        ).unwrap();
        assert_eq!(status, "reserved", "negative settlement must leave the lease open");
    }

    #[tokio::test]
    async fn test_model_call_settle_higher_actual_charges_only_delta() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(100), "settle-higher").await;
        let lease_id = reserve_model_call(&peer, &episode_id, &attempt_id, 40).await;

        tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id,
            "actual_cost_micros": 70,
            "status": "settled",
        }).as_object().unwrap().clone())).await.unwrap());

        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(30), "settlement must charge only actual - reserved");
    }

    #[tokio::test]
    async fn test_model_call_settle_higher_actual_denied_when_delta_exceeds_remaining_budget() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(50), "settle-higher-denied").await;
        let lease_id = reserve_model_call(&peer, &episode_id, &attempt_id, 40).await;

        let denied = peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id.clone(),
            "actual_cost_micros": 55,
            "status": "settled",
        }).as_object().unwrap().clone())).await;
        assert!(denied.is_err(), "higher actual must be denied if the delta is not covered");

        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(10));
        let status: String = conn.query_row(
            "SELECT status FROM model_call_leases WHERE id = ?1",
            [&lease_id],
            |row| row.get(0),
        ).unwrap();
        assert_eq!(status, "reserved", "denied settlement must leave the lease open");
    }

    #[tokio::test]
    async fn test_model_call_settle_voided_refunds_reserved_amount() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(100), "settle-voided").await;
        let lease_id = reserve_model_call(&peer, &episode_id, &attempt_id, 60).await;

        tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id.clone(),
            "actual_cost_micros": 0,
            "status": "voided",
        }).as_object().unwrap().clone())).await.unwrap());

        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(100));
        let (status, actual): (String, Option<i64>) = conn.query_row(
            "SELECT status, actual_cost_micros FROM model_call_leases WHERE id = ?1",
            [&lease_id],
            |row| Ok((row.get(0)?, row.get(1)?)),
        ).unwrap();
        assert_eq!(status, "voided");
        assert_eq!(actual, None);
    }

    #[tokio::test]
    async fn test_model_call_double_settlement_rejected_without_second_budget_change() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, Some(100), "double-settle").await;
        let lease_id = reserve_model_call(&peer, &episode_id, &attempt_id, 40).await;

        tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id.clone(),
            "actual_cost_micros": 30,
            "status": "settled",
        }).as_object().unwrap().clone())).await.unwrap());
        let rejected = peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id.clone(),
            "actual_cost_micros": 10,
            "status": "settled",
        }).as_object().unwrap().clone())).await;

        assert!(rejected.is_err(), "already-settled lease must be clearly rejected");
        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), Some(70));
    }

    #[tokio::test]
    async fn test_null_episode_budget_remains_unbounded_for_model_reserve_and_settle() {
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
        let (episode_id, _, attempt_id, _) =
            create_claimed_episode(&peer, None, "null-budget-model-call").await;

        let lease_id = reserve_model_call(&peer, &episode_id, &attempt_id, 10_000_000).await;
        {
            let conn = conn_arc.lock().await;
            assert_eq!(episode_budget(&conn, &episode_id), None);
        }
        tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease_id,
            "actual_cost_micros": 20_000_000,
            "status": "settled",
        }).as_object().unwrap().clone())).await.unwrap());

        let conn = conn_arc.lock().await;
        assert_eq!(episode_budget(&conn, &episode_id), None, "NULL budget must remain unbounded across reserve/settle");
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
    async fn test_research_dossier_create_observe_without_problem_or_episode_and_with_links() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let standalone = tool_json(&peer.call_tool(CallToolRequestParams::new("research_dossier_create").with_arguments(serde_json::json!({
            "title": "Early-stage argument map",
            "description": "No formal problem exists yet",
        }).as_object().unwrap().clone())).await.unwrap());
        assert!(standalone["dossier_id"].as_str().is_some_and(|s| !s.is_empty()), "{:?}", standalone);
        assert!(standalone["problem_version_id"].is_null(), "{:?}", standalone);
        assert!(standalone["episode_id"].is_null(), "{:?}", standalone);

        let pv_id = create_problem(&peer, "True").await;
        let linked_problem = tool_json(&peer.call_tool(CallToolRequestParams::new("research_dossier_create").with_arguments(serde_json::json!({
            "title": "Problem-linked dossier",
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(linked_problem["problem_version_id"], pv_id);

        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let linked_episode = tool_json(&peer.call_tool(CallToolRequestParams::new("research_dossier_create").with_arguments(serde_json::json!({
            "title": "Episode-linked dossier",
            "problem_version_id": pv_id,
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(linked_episode["problem_version_id"], pv_id);
        assert_eq!(linked_episode["episode_id"], episode_id);
    }

    #[tokio::test]
    async fn test_research_dossier_observe_separates_cited_reviewed_assumed_rejected_and_open_statuses() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let dossier = tool_json(&peer.call_tool(CallToolRequestParams::new("research_dossier_create").with_arguments(serde_json::json!({
            "title": "Trust boundary dossier",
        }).as_object().unwrap().clone())).await.unwrap());
        let dossier_id = dossier["dossier_id"].as_str().unwrap().to_string();

        let node = tool_json(&peer.call_tool(CallToolRequestParams::new("research_node_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "section_title": "Main argument",
            "node_type": "open_gap",
            "title": "Packing gap",
            "statement": "Need a packing bound",
            "trust_status": "open_gap",
        }).as_object().unwrap().clone())).await.unwrap());
        let node_id = node["node_id"].as_str().unwrap().to_string();
        assert_eq!(node["dossier"]["sections"].as_array().unwrap().len(), 1);

        let reference = tool_json(&peer.call_tool(CallToolRequestParams::new("external_reference_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "title": "Classical bound",
            "authors": "A. Author",
            "theorem_label": "Theorem 2",
            "theorem_statement": "Every admissible object satisfies the cited bound",
        }).as_object().unwrap().clone())).await.unwrap());
        let claim_id = reference["external_theorem_claim_id"].as_str().unwrap().to_string();
        let before_review = &reference["dossier"]["trust_boundary"];
        assert_eq!(before_review["externally_cited"].as_array().unwrap().len(), 1, "{:?}", before_review);
        assert!(before_review["lean_verified"]["external_theorem_claims"].as_array().unwrap().is_empty(), "{:?}", before_review);

        let reviewed = tool_json(&peer.call_tool(CallToolRequestParams::new("citation_review_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "external_theorem_claim_id": claim_id,
            "reviewer_id": "human-reviewer-1",
            "decision": "human_reviewed",
            "notes": "Citation text matches the claim, but this is not a Lean proof.",
        }).as_object().unwrap().clone())).await.unwrap());
        let after_review = &reviewed["dossier"]["trust_boundary"];
        assert_eq!(after_review["human_reviewed_citations"].as_array().unwrap().len(), 1, "{:?}", after_review);
        assert!(after_review["lean_verified"]["external_theorem_claims"].as_array().unwrap().is_empty(), "{:?}", after_review);

        tool_json(&peer.call_tool(CallToolRequestParams::new("assumption_boundary_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "node_id": node_id,
            "label": "Assumption A",
            "statement": "The reduction preserves extremality",
            "assumption_status": "unformalized_assumption",
        }).as_object().unwrap().clone())).await.unwrap());
        let rejected = tool_json(&peer.call_tool(CallToolRequestParams::new("assumption_boundary_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "label": "Unsafe shortcut",
            "statement": "Assume the desired conclusion",
            "assumption_status": "rejected_unsafe_assumption",
        }).as_object().unwrap().clone())).await.unwrap());
        let boundary = &rejected["dossier"]["trust_boundary"];
        assert_eq!(boundary["unformalized_assumptions"].as_array().unwrap().len(), 1, "{:?}", boundary);
        assert_eq!(boundary["rejected_assumptions"].as_array().unwrap().len(), 1, "{:?}", boundary);
        assert_eq!(boundary["open_gaps"].as_array().unwrap().len(), 1, "{:?}", boundary);

        tool_json(&peer.call_tool(CallToolRequestParams::new("verification_layer_set").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "target_kind": "dossier",
            "target_id": dossier_id,
            "layer_kind": "construction_search",
            "status": "blocked",
            "summary": "Need a sharper construction before formalization.",
        }).as_object().unwrap().clone())).await.unwrap());
        let failed = tool_json(&peer.call_tool(CallToolRequestParams::new("verification_layer_set").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "target_kind": "node",
            "target_id": node_id,
            "layer_kind": "packing_or_size_bound",
            "status": "failed",
            "evidence_json": "{\"attempt\":\"bound too weak\"}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(failed["dossier"]["status"], "draft", "blocked/failed layers must not fail the dossier itself: {:?}", failed);
        let layer_statuses: Vec<&str> = failed["dossier"]["verification_layers"].as_array().unwrap()
            .iter()
            .map(|layer| layer["status"].as_str().unwrap())
            .collect();
        assert!(layer_statuses.contains(&"blocked"), "{:?}", layer_statuses);
        assert!(layer_statuses.contains(&"failed"), "{:?}", layer_statuses);

        let denied = peer.call_tool(CallToolRequestParams::new("verification_layer_set").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "target_kind": "external_theorem_claim",
            "target_id": claim_id,
            "layer_kind": "external_review",
            "status": "kernel_verified",
        }).as_object().unwrap().clone())).await;
        assert!(denied.is_err(), "human-reviewed external citations must not be mislabeled kernel_verified");
    }

    #[tokio::test]
    async fn test_research_dossier_distinguishes_mathlib_import_from_locally_proved_episode_claim() {
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

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let step = claim_and_solve(&peer, &episode_id, "trivial", "research-proof-claim").await;
        assert_eq!(step["outcome"], "kernel_verified");

        let proved_lemma_id: String = {
            let conn = conn_arc.lock().await;
            conn.query_row(
                "SELECT id FROM episode_verified_lemmas WHERE episode_id = ?1 LIMIT 1",
                [&episode_id],
                |row| row.get(0),
            ).unwrap()
        };

        let dossier = tool_json(&peer.call_tool(CallToolRequestParams::new("research_dossier_create").with_arguments(serde_json::json!({
            "title": "Mathlib versus local proof",
            "problem_version_id": pv_id,
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let dossier_id = dossier["dossier_id"].as_str().unwrap().to_string();

        tool_json(&peer.call_tool(CallToolRequestParams::new("external_reference_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "title": "Mathlib imported fact",
            "theorem_label": "Nat.zero_eq",
            "theorem_statement": "0 = 0",
            "claim_status": "imported_from_mathlib",
            "mathlib_name": "Nat.zero_eq",
        }).as_object().unwrap().clone())).await.unwrap());
        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("external_reference_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "title": "Locally proved fact",
            "theorem_label": "root",
            "theorem_statement": "True",
            "claim_status": "proved_in_episode",
            "proved_episode_id": episode_id,
            "proved_lemma_id": proved_lemma_id,
        }).as_object().unwrap().clone())).await.unwrap());

        let boundary = &observed["dossier"]["trust_boundary"];
        assert_eq!(boundary["mathlib_imported"].as_array().unwrap().len(), 1, "{:?}", boundary);
        assert_eq!(boundary["lean_verified"]["external_theorem_claims"].as_array().unwrap().len(), 1, "{:?}", boundary);
        assert_ne!(
            boundary["mathlib_imported"][0]["claim_status"],
            boundary["lean_verified"]["external_theorem_claims"][0]["claim_status"],
            "Mathlib imports and locally proved episode claims must remain distinct"
        );
    }

    #[tokio::test]
    async fn test_candidate_construction_can_exist_standalone_and_link_to_dossier_node_and_verification_layer() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        // A candidate construction can exist before a dossier, before a node, before an episode.
        let standalone = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_add").with_arguments(serde_json::json!({
            "construction_type": "graph_family",
            "informal_description": "A family of Kneser-like graphs indexed by n",
            "created_by": "researcher-1",
        }).as_object().unwrap().clone())).await.unwrap());
        let standalone_id = standalone["candidate_construction_id"].as_str().unwrap().to_string();
        assert!(standalone["dossier"].is_null(), "{:?}", standalone);
        assert_eq!(standalone["candidate_construction"]["status"], "proposed", "{:?}", standalone);
        assert_eq!(standalone["candidate_construction"]["trust_status"], "informal", "{:?}", standalone);
        assert!(standalone["candidate_construction"]["dossier_id"].is_null(), "{:?}", standalone);

        // A candidate construction can link to a dossier at creation time.
        let dossier = tool_json(&peer.call_tool(CallToolRequestParams::new("research_dossier_create").with_arguments(serde_json::json!({
            "title": "Candidate construction dossier",
        }).as_object().unwrap().clone())).await.unwrap());
        let dossier_id = dossier["dossier_id"].as_str().unwrap().to_string();
        let attached = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "construction_type": "counterexample",
            "informal_description": "Candidate counterexample to the conjectured bound",
            "created_by": "researcher-1",
        }).as_object().unwrap().clone())).await.unwrap());
        let attached_id = attached["candidate_construction_id"].as_str().unwrap().to_string();
        assert_eq!(attached["dossier"]["dossier_id"], dossier_id, "{:?}", attached);

        // research_dossier_observe puts candidate constructions in their own bucket, separate
        // from proved nodes, citations, assumptions, and verification layers.
        let observed_dossier = &attached["dossier"];
        assert_eq!(observed_dossier["candidate_constructions"].as_array().unwrap().len(), 1, "{:?}", observed_dossier);
        assert!(observed_dossier["nodes"].as_array().unwrap().is_empty(), "{:?}", observed_dossier);
        assert!(observed_dossier["external_theorem_claims"].as_array().unwrap().is_empty(), "{:?}", observed_dossier);
        assert!(observed_dossier["assumption_boundaries"].as_array().unwrap().is_empty(), "{:?}", observed_dossier);
        assert!(observed_dossier["verification_layers"].as_array().unwrap().is_empty(), "{:?}", observed_dossier);

        // A candidate construction can link to a research node; a standalone construction with
        // no prior dossier adopts the node's dossier rather than staying orphaned.
        let node = tool_json(&peer.call_tool(CallToolRequestParams::new("research_node_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "node_type": "open_gap",
            "title": "Need a sharper packing bound",
            "trust_status": "open_gap",
        }).as_object().unwrap().clone())).await.unwrap());
        let node_id = node["node_id"].as_str().unwrap().to_string();

        let linked_node = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_link_node").with_arguments(serde_json::json!({
            "candidate_construction_id": standalone_id,
            "node_id": node_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(linked_node["candidate_construction"]["related_node_id"], node_id, "{:?}", linked_node);
        assert_eq!(linked_node["candidate_construction"]["dossier_id"], dossier_id, "linking to a node with no prior dossier must adopt the node's dossier: {:?}", linked_node);

        // A candidate construction can link to a verification layer.
        let layer_result = tool_json(&peer.call_tool(CallToolRequestParams::new("verification_layer_set").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "target_kind": "dossier",
            "target_id": dossier_id,
            "layer_kind": "construction_search",
            "status": "empirical",
            "summary": "Brute-force search over small parameter ranges",
        }).as_object().unwrap().clone())).await.unwrap());
        let layer_id = layer_result["verification_layer_id"].as_str().unwrap().to_string();

        let linked_layer = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_link_verification_layer").with_arguments(serde_json::json!({
            "candidate_construction_id": attached_id,
            "verification_layer_id": layer_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(linked_layer["candidate_construction"]["verification_layer_id"], layer_id, "{:?}", linked_layer);
        assert_eq!(linked_layer["candidate_construction"]["has_kernel_evidence"], false, "an 'empirical' verification layer must not read as kernel evidence: {:?}", linked_layer);
    }

    #[tokio::test]
    async fn test_candidate_construction_trust_boundary_rejects_unearned_kernel_verified_and_keeps_falsified_visible() {
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

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let step = claim_and_solve(&peer, &episode_id, "trivial", "candidate-construction-claim").await;
        assert_eq!(step["outcome"], "kernel_verified");
        let proved_lemma_id: String = {
            let conn = conn_arc.lock().await;
            conn.query_row(
                "SELECT id FROM episode_verified_lemmas WHERE episode_id = ?1 LIMIT 1",
                [&episode_id],
                |row| row.get(0),
            ).unwrap()
        };

        let dossier = tool_json(&peer.call_tool(CallToolRequestParams::new("research_dossier_create").with_arguments(serde_json::json!({
            "title": "Candidate construction trust boundary dossier",
            "problem_version_id": pv_id,
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let dossier_id = dossier["dossier_id"].as_str().unwrap().to_string();

        let node = tool_json(&peer.call_tool(CallToolRequestParams::new("research_node_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "node_type": "theorem",
            "title": "root theorem",
            "trust_status": "proved_in_episode",
            "linked_verified_lemma_id": proved_lemma_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let node_id = node["node_id"].as_str().unwrap().to_string();

        // A real kernel_verified verification layer, backed by the proved_in_episode node.
        let kernel_layer = tool_json(&peer.call_tool(CallToolRequestParams::new("verification_layer_set").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "target_kind": "node",
            "target_id": node_id,
            "layer_kind": "formal_module",
            "status": "kernel_verified",
            "summary": "Matches the kernel-verified root lemma",
        }).as_object().unwrap().clone())).await.unwrap());
        let kernel_layer_id = kernel_layer["verification_layer_id"].as_str().unwrap().to_string();

        // A non-kernel-verified layer, for the negative cases below.
        let blocked_layer = tool_json(&peer.call_tool(CallToolRequestParams::new("verification_layer_set").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "target_kind": "dossier",
            "target_id": dossier_id,
            "layer_kind": "construction_search",
            "status": "blocked",
        }).as_object().unwrap().clone())).await.unwrap());
        let blocked_layer_id = blocked_layer["verification_layer_id"].as_str().unwrap().to_string();

        let candidate = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "construction_type": "counterexample",
            "informal_description": "Candidate counterexample under empirical review",
            "created_by": "researcher-1",
        }).as_object().unwrap().clone())).await.unwrap());
        let candidate_id = candidate["candidate_construction_id"].as_str().unwrap().to_string();

        // A kernel-verified construction status is rejected without real Lean/kernel evidence:
        // no linked verification layer at all.
        let no_layer = peer.call_tool(CallToolRequestParams::new("candidate_construction_update_status").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "trust_status": "kernel_verified_claim_linked",
        }).as_object().unwrap().clone())).await;
        assert!(no_layer.is_err(), "kernel_verified_claim_linked must be rejected without any linked verification layer");

        // ...and rejected even with a linked layer, if that layer's own status isn't kernel_verified.
        tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_link_verification_layer").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "verification_layer_id": blocked_layer_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let blocked_reject = peer.call_tool(CallToolRequestParams::new("candidate_construction_update_status").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "trust_status": "kernel_verified_claim_linked",
        }).as_object().unwrap().clone())).await;
        assert!(blocked_reject.is_err(), "kernel_verified_claim_linked must be rejected when the linked layer's own status is not kernel_verified");

        // An empirically supported construction is not kernel verified, even after a
        // supporting observation is recorded.
        tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_update_status").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "status": "empirically_supported",
            "trust_status": "empirical_evidence",
        }).as_object().unwrap().clone())).await.unwrap());
        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_observe").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "description": "Checked all graphs on 12 vertices",
            "result": "supports",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["candidate_construction"]["trust_status"], "empirical_evidence", "{:?}", observed);
        assert_eq!(observed["candidate_construction"]["has_kernel_evidence"], false, "empirical support must never read as kernel evidence: {:?}", observed);
        assert_eq!(observed["candidate_construction"]["empirical_checks"].as_array().unwrap().len(), 1, "{:?}", observed);

        // A human-reviewed construction is not kernel verified.
        let human_reviewed = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_update_status").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "trust_status": "human_reviewed",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(human_reviewed["candidate_construction"]["has_kernel_evidence"], false, "{:?}", human_reviewed);

        // A formalized-statement construction is not kernel verified unless kernel evidence exists.
        let formalized = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_update_status").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "trust_status": "formalized_statement_exists",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(formalized["candidate_construction"]["has_kernel_evidence"], false, "{:?}", formalized);

        // Re-link to the REAL kernel_verified layer: now kernel_verified_claim_linked is accepted.
        tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_link_verification_layer").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "verification_layer_id": kernel_layer_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let verified = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_update_status").with_arguments(serde_json::json!({
            "candidate_construction_id": candidate_id,
            "status": "linked_to_formal_claim",
            "trust_status": "kernel_verified_claim_linked",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(verified["candidate_construction"]["trust_status"], "kernel_verified_claim_linked", "{:?}", verified);
        assert_eq!(verified["candidate_construction"]["has_kernel_evidence"], true, "{:?}", verified);

        // A falsified construction remains visible as falsified, not deleted or silently ignored.
        let falsified_candidate = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_add").with_arguments(serde_json::json!({
            "dossier_id": dossier_id,
            "construction_type": "coloring",
            "informal_description": "A candidate 4-coloring that turned out not to work",
            "created_by": "researcher-1",
        }).as_object().unwrap().clone())).await.unwrap());
        let falsified_id = falsified_candidate["candidate_construction_id"].as_str().unwrap().to_string();
        let falsified = tool_json(&peer.call_tool(CallToolRequestParams::new("candidate_construction_update_status").with_arguments(serde_json::json!({
            "candidate_construction_id": falsified_id,
            "status": "falsified",
            "known_failures_json": "[\"fails at n=9\"]",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(falsified["candidate_construction"]["status"], "falsified", "{:?}", falsified);
        let dossier_observed = &falsified["dossier"];
        let candidate_constructions = dossier_observed["candidate_constructions"].as_array().unwrap();
        assert_eq!(candidate_constructions.len(), 2, "{:?}", dossier_observed);
        let statuses: Vec<&str> = candidate_constructions.iter().map(|c| c["status"].as_str().unwrap()).collect();
        assert!(statuses.contains(&"falsified"), "falsified constructions must remain visible in dossier observation: {:?}", statuses);
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

    // -- Run envelopes (issues #34, #38) -------------------------------------

    #[tokio::test]
    async fn test_run_envelope_create_update_and_observe() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();

        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "benchmark", "host_name": "Claude Code", "host_model": "claude-sonnet-5",
            "benchmark_suite_name": "PutnamBench",
        }).as_object().unwrap().clone())).await.unwrap());
        let envelope_id = created["run_envelope_id"].as_str().unwrap().to_string();
        assert_eq!(created["mode"], "benchmark");
        assert_eq!(created["host_cost_confidence"], "unknown", "omitted confidence must default to the honest 'unknown', not a made-up value");

        let updated = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_update").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id, "host_side_cost_micros": 42_000_000i64, "host_cost_confidence": "estimated",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(updated["host_side_cost_micros"], 42_000_000i64);
        assert_eq!(updated["host_cost_confidence"], "estimated");

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_observe").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["mode"], "benchmark");
        assert_eq!(observed["host_name"], "Claude Code");
        assert_eq!(observed["benchmark_suite_name"], "PutnamBench");
        assert_eq!(observed["host_side_cost_micros"], 42_000_000i64);
        assert_eq!(observed["episodes"].as_array().unwrap().len(), 0);
    }

    #[tokio::test]
    async fn test_run_envelope_update_preserves_omitted_fields() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "development", "notes": "original note",
        }).as_object().unwrap().clone())).await.unwrap());
        let envelope_id = created["run_envelope_id"].as_str().unwrap().to_string();

        // Update ONLY cost — notes must survive untouched.
        tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_update").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id, "host_side_cost_micros": 10i64,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_observe").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["notes"], "original note", "an update that omits notes must not clear it");
        assert_eq!(observed["host_side_cost_micros"], 10i64);
    }

    #[tokio::test]
    async fn test_run_envelope_attach_episode_rejects_unknown_ids() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "development",
        }).as_object().unwrap().clone())).await.unwrap());
        let envelope_id = created["run_envelope_id"].as_str().unwrap().to_string();

        let bad1 = peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
            "run_envelope_id": "not-a-real-envelope", "episode_id": episode_id,
        }).as_object().unwrap().clone())).await;
        assert!(bad1.is_err());
        let bad2 = peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id, "episode_id": "not-a-real-episode",
        }).as_object().unwrap().clone())).await;
        assert!(bad2.is_err());

        // Happy path: attaching succeeds and shows up in observe.
        tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id, "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_observe").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let episodes = observed["episodes"].as_array().unwrap();
        assert_eq!(episodes.len(), 1, "{:?}", episodes);
        assert_eq!(episodes[0]["episode_id"], episode_id);
    }

    /// Core regression test: tagging an episode with a run envelope may set
    /// `episodes.run_id` (that's the whole point), but must never touch any
    /// OTHER column — outcome, state, current_revision, or anything in
    /// episode_obligations. Snapshots every column of both tables before and
    /// after, with run_id excluded from the episodes comparison (it's
    /// EXPECTED to change), asserting everything else is byte-identical.
    #[tokio::test]
    async fn test_run_envelope_attach_only_changes_run_id_column() {
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
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "development",
        }).as_object().unwrap().clone())).await.unwrap());
        let envelope_id = envelope["run_envelope_id"].as_str().unwrap().to_string();

        // Snapshot every column EXCEPT run_id (found by name, not by a
        // hardcoded index) — that one is expected to change.
        let snapshot = |conn: &Connection| -> (String, String) {
            let episodes: Vec<String> = conn.prepare("SELECT * FROM episodes ORDER BY id").unwrap()
                .query_map([], |row| {
                    let names = row.as_ref().column_names();
                    let n = row.as_ref().column_count();
                    Ok((0..n)
                        .filter(|&i| names[i] != "run_id")
                        .map(|i| format!("{:?}", row.get_ref(i).unwrap()))
                        .collect::<Vec<_>>().join(","))
                }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            let obligations: Vec<String> = conn.prepare("SELECT * FROM episode_obligations ORDER BY id").unwrap()
                .query_map([], |row| { let n = row.as_ref().column_count(); Ok((0..n).map(|i| format!("{:?}", row.get_ref(i).unwrap())).collect::<Vec<_>>().join(",")) }).unwrap()
                .collect::<Result<Vec<_>, _>>().unwrap();
            (episodes.join("|"), obligations.join("|"))
        };
        let before = { let c = conn_arc.lock().await; snapshot(&c) };

        tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
            "run_envelope_id": envelope_id, "episode_id": episode_id,
        }).as_object().unwrap().clone())).await.unwrap());

        let after = { let c = conn_arc.lock().await; snapshot(&c) };
        assert_eq!(before, after, "attaching a run envelope must change ONLY episodes.run_id — everything else (outcome, state, revision, obligations) must be untouched");

        let run_id: Option<String> = { let c = conn_arc.lock().await; c.query_row("SELECT run_id FROM episodes WHERE id = ?1", [&episode_id], |row| row.get(0)).unwrap() };
        assert_eq!(run_id.as_deref(), Some(envelope_id.as_str()), "run_id must actually be set to the envelope id");
    }

    // -- PutnamBench benchmark schema (issues #29, #30) ----------------------

    /// Issue #38's fidelity-basis policy: trusted_canonical_source=true,
    /// matching every existing test's implicit assumption that its suite
    /// behaves like a real, externally-curated corpus (PutnamBench) whose
    /// own canonical statement-hash match is sufficient fidelity evidence —
    /// dedicated tests below exercise the untrusted-suite rejection path
    /// explicitly via a raw benchmark_suite_create call instead of this helper.
    async fn create_suite(peer: &rmcp::service::Peer<rmcp::RoleClient>, name: &str) -> String {
        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_suite_create").with_arguments(serde_json::json!({
            "name": name, "trusted_canonical_source": true,
        }).as_object().unwrap().clone())).await.unwrap());
        created["suite_id"].as_str().unwrap().to_string()
    }

    /// benchmark_run_create requires an existing run_envelope_id (issue #34:
    /// "a benchmark run should not start unless a run envelope exists").
    async fn create_run_envelope(peer: &rmcp::service::Peer<rmcp::RoleClient>) -> String {
        let created = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "development", "host_name": "test-suite",
        }).as_object().unwrap().clone())).await.unwrap());
        created["run_envelope_id"].as_str().unwrap().to_string()
    }

    #[tokio::test]
    async fn test_benchmark_suite_create_rejects_duplicate_name() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        create_suite(&peer, "PutnamBench").await;
        let dup = peer.call_tool(CallToolRequestParams::new("benchmark_suite_create").with_arguments(serde_json::json!({
            "name": "PutnamBench",
        }).as_object().unwrap().clone())).await;
        assert!(dup.is_err(), "duplicate suite name must be rejected");
    }

    #[tokio::test]
    async fn test_benchmark_problem_register_computes_hash_and_rejects_duplicate() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;

        let registered = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "putnam_1988_a1", "theorem_name": "putnam_1988_a1",
            "root_formal_statement": "∀ n : ℕ, n = n", "import_manifest": ["Mathlib.Tactic.Ring"],
        }).as_object().unwrap().clone())).await.unwrap());
        assert!(!registered["root_statement_hash"].as_str().unwrap().is_empty());

        let dup = peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "putnam_1988_a1", "theorem_name": "putnam_1988_a1",
            "root_formal_statement": "∀ n : ℕ, n = n",
        }).as_object().unwrap().clone())).await;
        assert!(dup.is_err(), "the same upstream_problem_id in the same suite must be rejected on re-registration");
    }

    #[tokio::test]
    async fn test_benchmark_problem_register_computes_prover_ready_statement_hash() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        // prover_ready_statement is ALWAYS server-derived (via to_pi_form),
        // never a settable field on the wire — there is no
        // "prover_ready_statement" argument to pass here at all.
        let registered = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1",
            "root_formal_statement": "theorem p1 (n : ℕ) : n = n := sorry",
        }).as_object().unwrap().clone())).await.unwrap());
        assert!(!registered["prover_ready_statement_hash"].as_str().unwrap().is_empty());
        assert_ne!(registered["root_statement_hash"], registered["prover_ready_statement_hash"],
            "the catalog's faithful declaration text and the server-derived Pi-type form are different strings and must hash differently");

        // A root_formal_statement that isn't a `theorem NAME (binders) : type`
        // declaration (to_pi_form can't find "theorem p2" here) must leave
        // both DB columns NULL, not error — this is the normal case for any
        // benchmark suite/problem that needs no conversion.
        let without = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p2", "theorem_name": "p2",
            "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        assert!(without["prover_ready_statement_hash"].is_null());
    }

    #[tokio::test]
    async fn test_benchmark_problem_register_ignores_any_client_supplied_prover_ready_statement() {
        // Regression for a real fabrication bug an adversarial review found:
        // an earlier version accepted prover_ready_statement directly from
        // the client with no cross-check against root_formal_statement — a
        // caller could register a hard theorem's root_formal_statement
        // alongside an arbitrary, trivially-easy prover_ready_statement (or
        // vice versa) and have benchmark_result_record's cross-check
        // validate an episode against the WRONG statement. Confirm that
        // even if a client tries to smuggle a "prover_ready_statement" field
        // into the call, it has no effect — the stored hash is always the
        // server's own to_pi_form derivation from root_formal_statement.
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let registered = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1",
            "root_formal_statement": "theorem p1 (n : ℕ) : n = n := sorry",
            "prover_ready_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let expected_hash = canonical_hash(&"∀ (n : ℕ), n = n".to_string()).unwrap();
        assert_eq!(registered["prover_ready_statement_hash"], expected_hash,
            "a client-supplied prover_ready_statement must be silently ignored, never trusted: {:?}", registered);
        assert_ne!(registered["prover_ready_statement_hash"], canonical_hash(&"True".to_string()).unwrap());
    }

    #[tokio::test]
    async fn test_benchmark_result_record_cross_check_uses_prover_ready_statement_when_present() {
        // The real bug this regression-tests: a benchmark suite (like
        // PutnamBench) whose catalog root_formal_statement is NOT itself a
        // valid problem_create statement (e.g. a named-binder declaration,
        // not a bare Pi-type) must still be able to record a genuine result
        // — the episode's problem_version is created against the PROVER-READY
        // text, which necessarily differs from root_formal_statement, so the
        // cross-check must compare against prover_ready_statement_hash, not
        // root_statement_hash, whenever the former is present.
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1",
            "root_formal_statement": "theorem p1 (n : ℕ) : n = n := sorry",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        // The episode is created against the PROVER-READY text (what a real
        // runner submits), NOT root_formal_statement.
        let pv_id = create_problem(&peer, "∀ (n : ℕ), n = n").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "prover-ready-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "rfl"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let result = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await;
        assert!(result.is_ok(), "an episode proving the PROVER-READY form must be accepted even though it doesn't hash-match root_formal_statement: {:?}", result.err());
    }

    #[tokio::test]
    async fn test_benchmark_run_create_reads_lean_environment_from_server_not_client() {
        let conn = Connection::open_in_memory().unwrap();
        init_db(&conn).unwrap();
        let handler = ChatDbMcp {
            conn: Arc::new(Mutex::new(conn)),
            gateway: Box::new(MockGateway),
            lean_available: true,
            lean_environment: Some(chatdb_proof_core::lean::LeanEnvironmentInfo {
                toolchain: "leanprover/lean4:v4.32.0-rc1".to_string(),
                mathlib_rev: "360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56".to_string(),
                descriptor: "leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56".to_string(),
                // Deliberately distinct from mathlib_rev: in production `hash` is
                // canonical_hash(descriptor) (a SHA-256 fingerprint of the whole
                // descriptor string), never equal to the raw git commit. A fixture
                // that set these equal previously masked a bug where
                // benchmark_run_create stored `hash` into the `mathlib_commit`
                // column instead of the real `mathlib_rev`.
                hash: "deadbeefcafef00d0000000000000000000000000000000000000000000000".to_string(),
            }),
            lean_project_path: PathBuf::from("dummy"),
        };
        let client = connected_client(handler).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;

        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(run["lean_version"], "leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56");
        assert_eq!(run["mathlib_commit"], "360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56");
    }

    /// Issue #34's required behavior: "A benchmark run should not start
    /// unless a run envelope exists."
    #[tokio::test]
    async fn test_benchmark_run_create_requires_run_envelope() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;

        // Omitted entirely: rejected (the field is required in the wire schema).
        let missing = peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await;
        assert!(missing.is_err(), "run_envelope_id must be required, not optional");

        // A nonexistent run_envelope_id: also rejected.
        let bogus = peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": "00000000-0000-0000-0000-000000000000",
            "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await;
        assert!(bogus.is_err(), "a nonexistent run_envelope_id must be rejected");

        // A real run_envelope_id: accepted.
        let run_envelope_id = create_run_envelope(&peer).await;
        let ok = peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": run_envelope_id, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await;
        assert!(ok.is_ok(), "a real run_envelope_id must be accepted: {:?}", ok.err());
    }

    /// Issue #38's cost policy, redesigned per explicit product direction:
    /// three-tier monetary completeness (total_cost_known /
    /// reported_total_not_exact / total_cost_incomplete), never merging an
    /// attested/estimated figure into a claimed exact total. `total_cost_known`
    /// requires EVERY material cost surface to be exact — currently
    /// unreachable in practice since mcp_side_cost/storage_export_cost have
    /// no instrumentation at all yet, which is the intentional, honest state
    /// until they do (see the third case below).
    #[tokio::test]
    async fn test_benchmark_run_observe_marks_cost_completeness_from_host_confidence() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;

        // Default confidence ("unknown", the honest default when unset) -> incomplete.
        let unknown_envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "benchmark", "host_name": "test-host",
        }).as_object().unwrap().clone())).await.unwrap());
        let run_unknown = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": unknown_envelope["run_envelope_id"], "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let observed_unknown = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run_unknown["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed_unknown["cost_summary"]["cost_completeness"], "total_cost_incomplete",
            "no monetary signal at all (no host cost, no model-call cost) must report incomplete, not a made-up middle state");
        assert!(observed_unknown["cost_summary"]["mcp_side_cost_micros"].is_null(),
            "un-instrumented cost surfaces must be null, never silently reported as zero");
        assert!(observed_unknown["cost_summary"]["known_exact_cost_micros"].is_null());
        assert!(observed_unknown["cost_summary"]["reported_attested_cost_micros"].is_null());
        assert!(observed_unknown["cost_summary"]["estimated_cost_micros"].is_null());
        assert_eq!(observed_unknown["cost_summary"]["unknown_cost_present"], true);

        // "estimated" confidence: a REAL monetary signal exists now, just not
        // an exact one -- this is the honest middle tier, not "incomplete"
        // (which should mean "we know nothing"), and not "known" (which
        // would overstate an estimate's reliability).
        let estimated_envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "benchmark", "host_name": "test-host", "host_side_cost_micros": 100, "host_cost_confidence": "estimated",
        }).as_object().unwrap().clone())).await.unwrap());
        let run_estimated = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": estimated_envelope["run_envelope_id"], "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let observed_estimated = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run_estimated["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed_estimated["cost_summary"]["cost_completeness"], "reported_total_not_exact",
            "an estimate is real signal, not nothing, but is not the same reliability tier as a real receipt/meter reading");
        assert_eq!(observed_estimated["cost_summary"]["estimated_cost_micros"], 100);
        assert!(observed_estimated["cost_summary"]["known_exact_cost_micros"].is_null(),
            "an estimated figure must never be counted toward the exact bucket");

        // exact_local_meter: host cost itself is exact, but mcp_side_cost/
        // storage_export_cost still have zero instrumentation today, so the
        // report as a WHOLE still cannot claim total_cost_known -- that state
        // is intentionally unreachable until those surfaces are instrumented,
        // exactly the point of never conflating "one surface is exact" with
        // "the total is known."
        let exact_envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "benchmark", "host_name": "test-host", "host_side_cost_micros": 100, "host_cost_confidence": "exact_local_meter",
        }).as_object().unwrap().clone())).await.unwrap());
        let run_exact = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": exact_envelope["run_envelope_id"], "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let observed_exact = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run_exact["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed_exact["cost_summary"]["known_exact_cost_micros"], 100);
        assert_eq!(observed_exact["cost_summary"]["host_side_cost_micros"], 100);
        assert_eq!(observed_exact["cost_summary"]["cost_completeness"], "reported_total_not_exact",
            "total_cost_known must stay unreachable while mcp_side_cost/storage_export_cost remain uninstrumented, even with an exact host figure");
    }

    /// Issue #38's verifier_cost groundwork: a real, previously-undiscovered
    /// gap found while designing cost_summary — RealLeanGateway already
    /// computes real Lean invocation timing on every verification call, but
    /// the active step.rs/attempt_finalize path discarded everything except
    /// the outcome enum before this fix. Confirms the full pipeline:
    /// attempt_finalize persists the raw result onto
    /// action_attempts.lean_result_json, and benchmark_run_observe sums
    /// wall_time_ms/lean_cpu_time_ms across every attempt on the episode into
    /// cost_summary.verifier_wall_time_ms/verifier_cpu_time_ms.
    #[tokio::test]
    async fn test_benchmark_run_observe_aggregates_real_verifier_cost_from_persisted_attempts() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run_envelope_id = create_run_envelope(&peer).await;
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": run_envelope_id, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        // A real episode with TWO real verification attempts (one failed
        // kernel_fail, one successful) — both must contribute their
        // MockGateway-reported wall_time_ms (1 each) to the total.
        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req1 = &ep["next_action_request"];
        let claim1 = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req1["id"], "idempotency_key": "verifier-cost-1",
            "expected_revision": req1["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        let step1 = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim1["action_attempt_id"],
            "expected_revision": req1["episode_revision"], "claim_token": claim1["claim_token"],
            "action": {"type": "solve", "proof_term": "sorry"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        let req2 = &step1["next_action_request"];
        let claim2 = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req2["id"], "idempotency_key": "verifier-cost-2",
            "expected_revision": req2["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim2["action_attempt_id"],
            "expected_revision": req2["episode_revision"], "claim_token": claim2["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 2,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        // MockGateway reports wall_time_ms=1 and lean_cpu_time_ms=1 per
        // verification call; 2 real attempts on this episode -> both sums
        // must be 2, not null, not 0 by coincidence. mcp_action_count is a
        // real, always-present count (not gated on any "found" flag) of
        // every action_attempts row for this episode.
        assert_eq!(observed["cost_summary"]["verifier_wall_time_ms"], 2,
            "verifier_wall_time_ms must sum real persisted timing across every attempt on the episode: {:?}", observed["cost_summary"]);
        assert_eq!(observed["cost_summary"]["verifier_cpu_time_ms"], 2,
            "verifier_cpu_time_ms must sum real persisted cpu timing across every attempt on the episode: {:?}", observed["cost_summary"]);
        assert_eq!(observed["cost_summary"]["mcp_action_count"], 2,
            "mcp_action_count must be a real count of action_attempts, not gated on any timing data being present: {:?}", observed["cost_summary"]);
    }

    /// Issue #38's MCP-side/storage observability (v0.3.23): every tool call
    /// is logged (by call_tool's generic wrapper) with real wall-clock time,
    /// correlated to this run via the episode_id it references. Confirms
    /// mcp_handler_wall_time_ms and storage_bytes_written are real,
    /// non-null, positive numbers after genuine episode/attempt activity —
    /// and, critically (the explicit regression this issue asked for),
    /// that cost_completeness STILL cannot reach total_cost_known even once
    /// these new metrics are real and populated, since mcp_side_cost_micros/
    /// storage_export_cost_micros remain null (no pricing profile exists).
    #[tokio::test]
    async fn test_benchmark_run_observe_aggregates_real_mcp_and_storage_metrics() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "mcp1", "theorem_name": "mcp1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run_envelope_id = create_run_envelope(&peer).await;
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": run_envelope_id, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "mcp-metrics-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        // A real export call against this same episode contributes to
        // storage_export_bytes/storage_export_wall_time_ms specifically.
        tool_json(&peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "public_summary",
        }).as_object().unwrap().clone())).await.unwrap());

        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        let cs = &observed["cost_summary"];

        assert!(cs["mcp_handler_wall_time_ms"].as_i64().unwrap_or(-1) >= 0,
            "mcp_handler_wall_time_ms must be a real, non-null number once real tool calls reference this run's episode: {cs:?}");
        assert!(cs["storage_bytes_written"].as_i64().unwrap_or(-1) > 0,
            "storage_bytes_written must be a real positive byte count from the real persisted lean_result_json: {cs:?}");
        assert!(cs["storage_export_bytes"].as_i64().unwrap_or(-1) > 0,
            "storage_export_bytes must reflect the real proof_export call's returned content length: {cs:?}");
        assert!(cs["storage_export_wall_time_ms"].as_i64().unwrap_or(-1) >= 0,
            "storage_export_wall_time_ms must be a real, non-null number once a real proof_export/trajectory_export call references this run's episode: {cs:?}");

        // The explicit regression this issue asked for: real MCP/storage
        // METRICS existing must never be conflated with real MCP/storage
        // COST existing -- mcp_side_cost_micros/storage_export_cost_micros
        // stay null (no pricing profile), so cost_completeness must still
        // be unable to reach total_cost_known.
        assert!(cs["mcp_side_cost_micros"].is_null(),
            "mcp_side_cost_micros must stay null even with real mcp_handler_wall_time_ms data -- a metric is not a price: {cs:?}");
        assert!(cs["storage_export_cost_micros"].is_null(),
            "storage_export_cost_micros must stay null even with real storage_export_bytes data -- a metric is not a price: {cs:?}");
        assert_ne!(cs["cost_completeness"], "total_cost_known",
            "cost_completeness must remain unable to reach total_cost_known despite real MCP/storage metrics, since no pricing profile exists for either surface: {cs:?}");
    }

    /// A run with genuinely NO tool-call activity correlated to it at all
    /// (a fresh run with no episodes, no results) must report every new
    /// metric as null, never fabricated as 0 -- "no data yet" and "zero
    /// real cost" are different claims.
    #[tokio::test]
    async fn test_benchmark_run_observe_reports_null_mcp_storage_metrics_for_empty_run() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let run_envelope_id = create_run_envelope(&peer).await;
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": run_envelope_id, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        let cs = &observed["cost_summary"];
        assert!(cs["storage_bytes_written"].is_null(), "no episodes -> no persisted bytes -> null, not 0: {cs:?}");
        assert!(cs["storage_export_bytes"].is_null(), "no export calls -> null, not 0: {cs:?}");
        assert!(cs["storage_export_wall_time_ms"].is_null(), "no export calls -> null, not 0: {cs:?}");
    }

    /// Regression for a real, critical bug an adversarial review caught in
    /// this same instrumentation pass: `call_tool`'s metrics-logging code
    /// originally ran AFTER a plain `match request.name.as_ref() { ... }` —
    /// but `?` and `return Err(...)` inside a match arm target the nearest
    /// enclosing FUNCTION, not the match itself, so EVERY arm that uses
    /// either (the overwhelming majority — arg-parsing failures, CAS
    /// mismatches, policy rejections, DB errors) bypassed the metrics
    /// insert entirely, silently undercounting mcp_handler_wall_time_ms for
    /// any run with even one rejected call. Fixed by wrapping the whole
    /// match in its own `async move { ... }.await` block, which gives
    /// `?`/`return` a closer boundary to target. This test constructs its
    /// own handler (not test_handler_with_gateway, which drops its own
    /// Arc<Mutex<Connection>>) specifically to keep a raw handle on the
    /// underlying connection, so it can directly query mcp_call_metrics
    /// after a deliberately-failing call and prove a row was actually
    /// logged for it — the exact case the bug silently dropped.
    #[tokio::test]
    async fn test_call_tool_logs_metrics_for_rejected_calls_not_just_successes() {
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

        // episode_status's arg-parsing failure (missing required episode_id)
        // hits `serde_json::from_value(...).map_err(...)?` -- a genuine `?`
        // early return, exactly the bug class this regression guards
        // against (as opposed to e.g. episode_status's OWN "unknown
        // episode_id" rejection, which is a plain match-arm tail Err(...)
        // value that would have flowed through even before this fix).
        let rejected = peer.call_tool(CallToolRequestParams::new("episode_status").with_arguments(
            serde_json::json!({}).as_object().unwrap().clone()
        )).await;
        assert!(rejected.is_err(), "missing required episode_id must be rejected");

        let logged: i64 = conn_arc.lock().await.query_row(
            "SELECT COUNT(*) FROM mcp_call_metrics WHERE tool_name = 'episode_status' AND is_error = 1",
            [], |row| row.get(0),
        ).unwrap();
        assert_eq!(logged, 1,
            "a rejected call that failed via `?` inside its arm must still be logged into mcp_call_metrics with is_error=1, not silently dropped");
    }

    /// Issue #34/#38's model_call_leases finding, now wired in per explicit
    /// product direction: real per-attempt self-reported model-call cost is
    /// folded into benchmark_run_observe as model_call_reported_cost_micros,
    /// ALWAYS at "attested" confidence (never independently measured by
    /// ChatDB) — so it must land in reported_attested_cost_micros, never
    /// known_exact_cost_micros, and its presence must keep cost_completeness
    /// at reported_total_not_exact even when the host-side figure is
    /// separately exact.
    #[tokio::test]
    async fn test_benchmark_run_observe_folds_in_model_call_cost_as_attested() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "benchmark", "host_name": "test-host", "host_side_cost_micros": 500, "host_cost_confidence": "exact_local_meter",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": envelope["run_envelope_id"], "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "model-call-cost-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        let action_attempt_id = claim["action_attempt_id"].as_str().unwrap().to_string();

        let lease = tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_reserve").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": action_attempt_id, "runner_id": "test-runner",
            "declared_model": "test-model", "max_input_tokens": 1000, "max_output_tokens": 500, "reserved_cost_micros": 300,
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_settle").with_arguments(serde_json::json!({
            "lease_id": lease["lease_id"], "actual_cost_micros": 250, "status": "settled",
        }).as_object().unwrap().clone())).await.unwrap());

        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": action_attempt_id,
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        let cs = &observed["cost_summary"];
        assert_eq!(cs["model_call_reported_cost_micros"], 250, "must sum settled actual_cost_micros, not reserved_cost_micros: {cs:?}");
        assert_eq!(cs["model_call_cost_confidence"], "attested");
        assert_eq!(cs["known_exact_cost_micros"], 500, "the host-side exact figure must still land in the exact bucket on its own");
        assert_eq!(cs["reported_attested_cost_micros"], 250, "model-call cost must land in the attested bucket, never merged into known_exact");
        assert_eq!(cs["cost_completeness"], "reported_total_not_exact",
            "attested model-call cost present alongside an exact host figure must still block total_cost_known: {cs:?}");
    }

    /// A reserved-but-never-settled lease must not contribute a phantom cost
    /// figure — actual_cost_micros is NULL until settlement, so it must be
    /// excluded from the sum entirely, not treated as 0. Critically, the
    /// episode carrying the unsettled lease IS actually linked into this
    /// run's results (via benchmark_result_record's episode_id) so the
    /// aggregation loop genuinely visits it — an adversarial review of an
    /// earlier version of this test caught that it passed vacuously
    /// (run_envelope_attach_episode does NOT feed benchmark_run_observe's
    /// aggregation at all; only benchmark_results.episode_id does), so the
    /// episode must actually reach a concluded outcome and be recorded via
    /// benchmark_result_record with a real episode_id for this test to mean
    /// anything.
    #[tokio::test]
    async fn test_benchmark_run_observe_ignores_unsettled_model_call_leases() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "unsettled1", "theorem_name": "unsettled1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run_envelope_id = create_run_envelope(&peer).await;
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": run_envelope_id, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "unsettled-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("model_call_reserve").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"], "runner_id": "test-runner",
            "declared_model": "test-model", "max_input_tokens": 1000, "max_output_tokens": 500, "reserved_cost_micros": 900,
        }).as_object().unwrap().clone())).await.unwrap());
        // Deliberately does NOT call episode_step on this claimed attempt:
        // step.rs::attempt_finalize's real, pre-existing behavior auto-settles
        // ANY 'reserved' lease matching the stepped (episode_id, action_attempt_id)
        // pair using that step's OWN cost_micros as actual_cost_micros --
        // discovered while writing this exact test (an earlier version used
        // episode_step/give_up here and the "unsettled" lease was silently
        // auto-settled to cost_micros=1, making the test pass vacuously for a
        // second, different reason than the first fix). episode_close is used
        // instead: it force-terminates the episode without touching
        // model_call_leases at all, so this lease genuinely stays 'reserved'.
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_close").with_arguments(serde_json::json!({
            "episode_id": episode_id, "reason": "test",
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "failed", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run["run_id"],
        }).as_object().unwrap().clone())).await.unwrap());
        // Sanity check that this test actually visits the episode at all
        // (mcp_action_count > 0 proves the aggregation loop ran against a
        // real linked episode, not an empty/unreferenced one).
        assert_eq!(observed["cost_summary"]["mcp_action_count"], 1,
            "the episode must genuinely be linked into this run's results for this test to mean anything: {:?}", observed["cost_summary"]);
        assert!(observed["cost_summary"]["model_call_reported_cost_micros"].is_null(),
            "an unsettled (reserved-only) lease has no actual_cost_micros yet and must not contribute a phantom figure: {:?}", observed["cost_summary"]);
        assert!(observed["cost_summary"]["model_call_cost_confidence"].is_null());
    }

    #[tokio::test]
    async fn test_benchmark_run_create_rejects_nonpositive_attempt_budget() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let res = peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 0,
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err());
    }

    #[tokio::test]
    async fn test_benchmark_result_record_rejects_cross_suite_problem() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_a = create_suite(&peer, "PutnamBench").await;
        let suite_b = create_suite(&peer, "OtherBench").await;
        let problem_b = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_b, "upstream_problem_id": "p1", "theorem_name": "p1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run_a = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_a, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        let res = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_a["run_id"], "benchmark_problem_id": problem_b["benchmark_problem_id"],
            "status": "failed", "attempts_used": 1,
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "a result must not reference a problem from a different suite than its run");
    }

    /// Issue #36's core invariant, closed at its widest gap: earlier
    /// enforcement (outcome-match, statement-match) only ran when an
    /// episode_id happened to be given at all — a caller claiming
    /// kernel_verified/certified with NO episode_id whatsoever skipped
    /// every check and was accepted with zero backing evidence. A verified
    /// claim must always reference the episode that reached it; any other
    /// status (failed/timeout/infra_error/formalization_gap/skipped)
    /// legitimately has no episode to reference.
    #[tokio::test]
    async fn test_benchmark_result_record_rejects_verified_claims_with_no_episode() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        // No episode_id at all: both verified statuses must be rejected outright.
        for status in ["kernel_verified", "certified"] {
            let res = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
                "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
                "status": status, "attempts_used": 1,
            }).as_object().unwrap().clone())).await;
            assert!(res.is_err(), "claiming {} with no episode_id must be rejected — it has zero backing evidence: {:?}", status, res);
        }

        // Non-verified statuses legitimately have no episode to reference —
        // must still be accepted (this is not a blanket "episode_id always
        // required" rule, only for statuses that claim verification).
        for status in ["failed", "timeout", "infra_error", "formalization_gap", "skipped"] {
            let res = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
                "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
                "status": status, "attempts_used": 1,
            }).as_object().unwrap().clone())).await;
            assert!(res.is_ok(), "status {} with no episode_id must still be accepted: {:?}", status, res.err());
        }
    }

    /// Issue #36's core invariant, enforced concretely: a benchmark result
    /// cannot claim kernel_verified/certified unless the referenced episode
    /// ACTUALLY reached that outcome, and cannot reference an episode that
    /// hasn't concluded at all.
    #[tokio::test]
    async fn test_benchmark_result_record_enforces_episode_outcome_consistency() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        // An episode that has NOT concluded (no Solve/GiveUp yet).
        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();

        let unconcluded = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await;
        assert!(unconcluded.is_err(), "a result must not reference an episode that hasn't concluded");

        // Conclude the episode with GiveUp (outcome = gave_up), then claim
        // kernel_verified anyway — must be rejected as a mismatch.
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "bench-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "give_up"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let mismatched = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await;
        assert!(mismatched.is_err(), "claiming kernel_verified for an episode that actually gave up must be rejected");

        // The honest status (failed) for the same episode succeeds.
        let honest = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "failed", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(honest["status"], "failed");
        assert_eq!(honest["benchmark_fidelity_basis"], "none",
            "a non-kernel_verified/certified status makes no proof claim, so it must report benchmark_fidelity_basis='none', not fabricate one");
    }

    /// Issue #38's fidelity-basis policy, the core new enforcement: a
    /// kernel_verified/certified claim against an UNTRUSTED suite (the
    /// default for any newly registered suite) backed only by an
    /// unsafe_dev_attestation problem (fidelity_status='attested', never
    /// independently reviewed) must be REJECTED outright — a statement-hash
    /// match alone is only sufficient fidelity evidence for a suite that
    /// explicitly opted into trusted_canonical_source (a real, externally-
    /// curated corpus like PutnamBench); an arbitrary custom suite gets no
    /// such shortcut.
    #[tokio::test]
    async fn test_benchmark_result_record_rejects_untrusted_suite_without_independent_review() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        // NOT create_suite() -- that helper defaults trusted_canonical_source
        // to true; this test needs the real, untrusted default explicitly.
        let suite = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_suite_create").with_arguments(serde_json::json!({
            "name": "UntrustedCustomSuite",
        }).as_object().unwrap().clone())).await.unwrap());
        let suite_id = suite["suite_id"].as_str().unwrap().to_string();
        assert_eq!(suite["trusted_canonical_source"], false, "trusted_canonical_source must default to false, never silently true");
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "u1", "theorem_name": "u1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        // create_problem uses unsafe_dev_attestation -> fidelity_status='attested', never 'verified'.
        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "untrusted-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let rejected = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await;
        assert!(rejected.is_err(),
            "an untrusted suite + an unreviewed (attested) problem must not be sufficient fidelity evidence for a kernel_verified claim");

        // A REAL independent fidelity review (fidelity_status='verified')
        // unblocks the exact same untrusted suite -- basis becomes
        // problem_fidelity_verified, not canonical_statement_hash_match.
        let create = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
            "source_problem_text": "reviewed problem for untrusted suite", "root_formal_statement": "1 + 1 = 2",
        }).as_object().unwrap().clone())).await.unwrap());
        let reviewed_pv_id = create["problem_version_id"].as_str().unwrap().to_string();
        let review = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_submit_fidelity_review").with_arguments(serde_json::json!({
            "problem_version_id": reviewed_pv_id, "decision": "verified", "method": "human_review",
            "approver_id": "reviewer-1", "rubric_version": "v1",
            "source_problem_hash": create["source_problem_hash"], "root_statement_hash": create["root_statement_hash"],
            "rendering_hash": create["rendering_hash"], "evidence_json": "{}",
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(review["fidelity_status"], "verified");

        let problem2 = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "u2", "theorem_name": "u2", "root_formal_statement": "1 + 1 = 2",
        }).as_object().unwrap().clone())).await.unwrap());
        let ep2 = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": reviewed_pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode2_id = ep2["episode_id"].as_str().unwrap().to_string();
        let req2 = &ep2["next_action_request"];
        let claim2 = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode2_id, "action_request_id": req2["id"], "idempotency_key": "untrusted-2",
            "expected_revision": req2["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        // reviewed_pv_id's fidelity_status is ALREADY 'verified' (from the
        // review above) before this episode's root gets proved, so per
        // step.rs's promotion logic the outcome lands directly on
        // 'certified', not 'kernel_verified' -- reflect that here.
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode2_id, "action_attempt_id": claim2["action_attempt_id"],
            "expected_revision": req2["episode_revision"], "claim_token": claim2["claim_token"],
            "action": {"type": "solve", "proof_term": "norm_num"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        let accepted = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem2["benchmark_problem_id"],
            "episode_id": episode2_id, "status": "certified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(accepted["benchmark_fidelity_basis"], "problem_fidelity_verified",
            "an untrusted suite backed by a REAL independent review must be accepted with the problem_fidelity_verified basis, not canonical_statement_hash_match: {accepted:?}");
    }

    /// Issue #38's mode-enforcement policy, the exact wording it specifies:
    /// an untrusted suite's kernel_verified claim backed by an
    /// unsafe_dev_attestation problem, recorded against a "benchmark"-mode
    /// run envelope, must be rejected with the specific boring message —
    /// not the longer fidelity-basis message this same scenario would
    /// otherwise also independently trigger. Confirms the mode check fires
    /// FIRST (a mode violation is a harder rejection than a missing
    /// fidelity basis).
    #[tokio::test]
    async fn test_benchmark_result_record_reports_exact_mode_enforcement_message_for_untrusted_suite() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_suite_create").with_arguments(serde_json::json!({
            "name": "UntrustedBenchmarkModeSuite",
        }).as_object().unwrap().clone())).await.unwrap());
        let suite_id = suite["suite_id"].as_str().unwrap().to_string();
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "m1", "theorem_name": "m1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "benchmark", "host_name": "test-host",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": envelope["run_envelope_id"], "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        let pv_id = create_problem(&peer, "True").await; // unsafe_dev_attestation -> fidelity_status='attested'
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "mode-enforce-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let rejected = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await;
        let err_text = format!("{:?}", rejected.unwrap_err());
        assert!(err_text.contains("attested/dev-bypass problems are not valid for benchmark/evaluation/public_report runs"),
            "must report the exact specified boring rejection message, not a different one: {err_text}");
    }

    /// Issue #38's mode-enforcement policy where it has real behavioral
    /// bite: run_envelope_attach_episode has no suite/trust concept at all,
    /// so an attested-fidelity episode is unconditionally blocked from
    /// benchmark/evaluation/public_report envelopes (development is always
    /// fine; private_audit needs the explicit allow_dev_attested override).
    #[tokio::test]
    async fn test_run_envelope_attach_episode_blocks_attested_episode_from_measured_modes() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "True").await; // unsafe_dev_attestation -> fidelity_status='attested'

        async fn new_episode(peer: &rmcp::service::Peer<rmcp::RoleClient>, pv_id: &str) -> String {
            tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
                "problem_version_id": pv_id, "max_steps": 5,
            }).as_object().unwrap().clone())).await.unwrap())["episode_id"].as_str().unwrap().to_string()
        }

        for mode in ["benchmark", "evaluation", "public_report"] {
            let envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
                "mode": mode, "host_name": "test-host",
            }).as_object().unwrap().clone())).await.unwrap());
            let episode_id = new_episode(&peer, &pv_id).await;
            let rejected = peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
                "run_envelope_id": envelope["run_envelope_id"], "episode_id": episode_id,
            }).as_object().unwrap().clone())).await;
            assert!(rejected.is_err(), "an attested episode must be blocked from a {mode:?}-mode envelope, no override possible");
            let err_text = format!("{:?}", rejected.unwrap_err());
            assert!(err_text.contains("attested/dev-bypass problems are not valid for benchmark/evaluation/public_report runs"),
                "mode={mode:?}: {err_text}");
        }

        // development: always allowed, no flag needed.
        let dev_envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "development", "host_name": "test-host",
        }).as_object().unwrap().clone())).await.unwrap());
        let dev_episode_id = new_episode(&peer, &pv_id).await;
        let dev_ok = peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
            "run_envelope_id": dev_envelope["run_envelope_id"], "episode_id": dev_episode_id,
        }).as_object().unwrap().clone())).await;
        assert!(dev_ok.is_ok(), "development mode must always allow an attested episode: {:?}", dev_ok.err());

        // private_audit: blocked without the explicit override, allowed with it.
        let audit_envelope = tool_json(&peer.call_tool(CallToolRequestParams::new("run_envelope_create").with_arguments(serde_json::json!({
            "mode": "private_audit", "host_name": "test-host",
        }).as_object().unwrap().clone())).await.unwrap());
        let audit_episode_id = new_episode(&peer, &pv_id).await;
        let audit_denied = peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
            "run_envelope_id": audit_envelope["run_envelope_id"], "episode_id": audit_episode_id,
        }).as_object().unwrap().clone())).await;
        assert!(audit_denied.is_err(), "private_audit must require the explicit allow_dev_attested override, not allow it silently");
        let audit_allowed = peer.call_tool(CallToolRequestParams::new("run_envelope_attach_episode").with_arguments(serde_json::json!({
            "run_envelope_id": audit_envelope["run_envelope_id"], "episode_id": audit_episode_id, "allow_dev_attested": true,
        }).as_object().unwrap().clone())).await;
        assert!(audit_allowed.is_ok(), "private_audit + allow_dev_attested=true must succeed: {:?}", audit_allowed.err());
    }

    /// Issue #38's fidelity-basis policy: a TRUSTED suite's own canonical
    /// statement-hash match is sufficient on its own, WITHOUT requiring a
    /// separate independent review — the exact PutnamBench scenario this
    /// policy exists for.
    #[tokio::test]
    async fn test_benchmark_result_record_trusted_suite_accepts_hash_match_alone() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await; // trusted_canonical_source: true
        let problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "t1", "theorem_name": "t1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        // create_problem -> unsafe_dev_attestation -> fidelity_status='attested', deliberately NOT 'verified'.
        let pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "trusted-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let accepted = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(accepted["benchmark_fidelity_basis"], "canonical_statement_hash_match",
            "a trusted suite's own hash match must be sufficient fidelity evidence without an independent review: {accepted:?}");
    }

    #[tokio::test]
    async fn test_benchmark_result_record_rejects_episode_problem_statement_mismatch() {
        // A real, concluded, kernel_verified episode must NOT be usable as
        // "proof" of a DIFFERENT benchmark problem's statement — only an
        // episode that actually proved the SAME root_formal_statement
        // (compared via root_statement_hash) may back a claimed result.
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        // Register a "hard" benchmark problem with a distinct statement.
        let hard_problem = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "hard1", "theorem_name": "hard1",
            "root_formal_statement": "putnam_1988_a1_real_statement",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        // Drive a genuinely kernel_verified episode, but for a TRIVIAL, UNRELATED statement.
        let trivial_pv_id = create_problem(&peer, "True").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": trivial_pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "mismatch-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(step["termination_reason"], "root_proved", "sanity check: the trivial episode really did conclude kernel_verified");

        // Attempting to claim this UNRELATED, genuinely-verified episode as evidence
        // for the hard benchmark problem must be rejected — the episode proved a
        // different statement than benchmark_problem_id claims.
        let res = peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run["run_id"], "benchmark_problem_id": hard_problem["benchmark_problem_id"],
            "episode_id": episode_id, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await;
        assert!(res.is_err(), "an episode that verified a different statement must not back a result for this benchmark problem");
    }

    #[tokio::test]
    async fn test_benchmark_result_record_upserts_and_run_observe_computes_metrics() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let p1 = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p1", "theorem_name": "p1", "root_formal_statement": "True",
        }).as_object().unwrap().clone())).await.unwrap());
        let p2 = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "p2", "theorem_name": "p2", "root_formal_statement": "1 + 1 = 2",
        }).as_object().unwrap().clone())).await.unwrap());
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let run_id = run["run_id"].as_str().unwrap().to_string();

        // First attempt for p1: failed, attempts_used=1.
        let first = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": p1["benchmark_problem_id"], "status": "failed", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(first["updated"], false);
        // Second attempt for the SAME problem: upserts to kernel_verified,
        // attempts_used=2 — backed by a real episode that actually proved
        // "True" (issue #36: kernel_verified/certified must reference the
        // episode that reached it, never a bare claim).
        let p1_pv_id = create_problem(&peer, "True").await;
        let p1_ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": p1_pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let p1_episode_id = p1_ep["episode_id"].as_str().unwrap().to_string();
        let p1_req = &p1_ep["next_action_request"];
        let p1_claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": p1_episode_id, "action_request_id": p1_req["id"], "idempotency_key": "upsert-p1-1",
            "expected_revision": p1_req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": p1_episode_id, "action_attempt_id": p1_claim["action_attempt_id"],
            "expected_revision": p1_req["episode_revision"], "claim_token": p1_claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        let second = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": p1["benchmark_problem_id"], "episode_id": p1_episode_id,
            "status": "kernel_verified", "attempts_used": 2,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(second["updated"], true);
        // p2: skipped.
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": p2["benchmark_problem_id"], "status": "skipped", "attempts_used": 0,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run_id,
        }).as_object().unwrap().clone())).await.unwrap());
        let results = observed["results"].as_array().unwrap();
        assert_eq!(results.len(), 2, "upserting the same problem twice must not create a duplicate result row: {:?}", results);
        assert_eq!(observed["metrics"]["problems_attempted"], 2);
        assert_eq!(observed["metrics"]["solved_count"], 1);
        assert_eq!(observed["metrics"]["kernel_verified_count"], 1);
        assert_eq!(observed["metrics"]["certified_count"], 0);
        // p1 only reached kernel_verified on its SECOND attempt — must not count
        // toward pass_at_1_rate even though it counts toward solved_count/solved_rate.
        assert_eq!(observed["metrics"]["solved_rate"], 0.5, "1 of 2 problems solved at all");
        assert_eq!(observed["metrics"]["pass_at_1_rate"], 0.0, "the only solve took 2 attempts, so pass@1 is 0");
    }

    #[tokio::test]
    async fn test_benchmark_run_observe_pass_at_1_rate_distinguishes_first_try_from_eventual_solve() {
        // pass_at_1_rate must reflect genuine first-attempt success, not merely
        // "solved at all within the run's attempt budget" (which is solved_rate).
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let mut problem_ids = vec![];
        for upstream_id in ["p1", "p2", "p3", "p4"] {
            let p = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
                "suite_id": suite_id, "upstream_problem_id": upstream_id, "theorem_name": upstream_id,
                "root_formal_statement": format!("stmt_{}", upstream_id),
            }).as_object().unwrap().clone())).await.unwrap());
            problem_ids.push(p["benchmark_problem_id"].as_str().unwrap().to_string());
        }
        let run = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_create").with_arguments(serde_json::json!({
            "suite_id": suite_id, "run_envelope_id": create_run_envelope(&peer).await, "solve_mode": "solve_only", "attempt_budget": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let run_id = run["run_id"].as_str().unwrap().to_string();

        // Each "solved" claim below (issue #36) must reference a real
        // episode that actually proved the SAME statement — a helper that
        // creates one, proves it, and returns the episode_id.
        async fn solved_episode_for(peer: &rmcp::service::Peer<rmcp::RoleClient>, statement: &str, key: &str) -> String {
            let pv_id = create_problem(peer, statement).await;
            let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
                "problem_version_id": pv_id, "max_steps": 5,
            }).as_object().unwrap().clone())).await.unwrap());
            let episode_id = ep["episode_id"].as_str().unwrap().to_string();
            let req = &ep["next_action_request"];
            let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
                "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": key,
                "expected_revision": req["episode_revision"],
            }).as_object().unwrap().clone())).await.unwrap());
            tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
                "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
                "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
                "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
            }).as_object().unwrap().clone())).await.unwrap());
            episode_id
        }

        // p1: solved, but attempts_used=2 and no explicit pass_at -- NOT pass@1.
        let p1_episode = solved_episode_for(&peer, "stmt_p1", "pass1-p1").await;
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": problem_ids[0], "episode_id": p1_episode, "status": "kernel_verified", "attempts_used": 2,
        }).as_object().unwrap().clone())).await.unwrap());
        // p2: solved, attempts_used=1, no explicit pass_at -- fallback counts as pass@1.
        let p2_episode = solved_episode_for(&peer, "stmt_p2", "pass1-p2").await;
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": problem_ids[1], "episode_id": p2_episode, "status": "kernel_verified", "attempts_used": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        // p3: solved, attempts_used=3 but explicit pass_at=1 (authoritative) -- pass@1.
        let p3_episode = solved_episode_for(&peer, "stmt_p3", "pass1-p3").await;
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": problem_ids[2], "episode_id": p3_episode, "status": "kernel_verified", "attempts_used": 3, "pass_at": 1,
        }).as_object().unwrap().clone())).await.unwrap());
        // p4: not solved at all.
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_result_record").with_arguments(serde_json::json!({
            "run_id": run_id, "benchmark_problem_id": problem_ids[3], "status": "failed", "attempts_used": 5,
        }).as_object().unwrap().clone())).await.unwrap());

        let observed = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_run_observe").with_arguments(serde_json::json!({
            "run_id": run_id,
        }).as_object().unwrap().clone())).await.unwrap());
        assert_eq!(observed["metrics"]["problems_attempted"], 4);
        assert_eq!(observed["metrics"]["solved_count"], 3);
        assert_eq!(observed["metrics"]["solved_rate"], 0.75);
        assert_eq!(observed["metrics"]["pass_at_1_rate"], 0.5, "only p2 and p3 count as genuine pass@1 out of 4 attempted");
    }

    #[tokio::test]
    async fn test_proof_export_public_summary_never_contains_proof_body() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let statement = "putnam_export_secret_proof_statement";
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "e1", "theorem_name": "e1", "root_formal_statement": statement,
        }).as_object().unwrap().clone())).await.unwrap());

        let pv_id = create_problem(&peer, statement).await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "pub-sum-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "my_super_secret_proof_tactic_xyz"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "public_summary",
        }).as_object().unwrap().clone())).await.unwrap();
        let text = res.content[0].as_text().unwrap().text.clone();
        assert!(!text.contains("my_super_secret_proof_tactic_xyz"), "public_summary must never contain the proof body: {text}");
        assert!(text.contains("PutnamBench"), "public_summary should identify the linked benchmark suite: {text}");
        assert!(text.contains("KERNEL_VERIFIED") || text.contains("CERTIFIED"), "public_summary should report the outcome: {text}");
    }

    #[tokio::test]
    async fn test_proof_export_gates_proof_body_for_benchmark_linked_problem() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBench").await;
        let statement = "putnam_export_gate_statement";
        tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
            "suite_id": suite_id, "upstream_problem_id": "g1", "theorem_name": "g1", "root_formal_statement": statement,
        }).as_object().unwrap().clone())).await.unwrap());

        let pv_id = create_problem(&peer, statement).await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "gate-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        // Without the flag: rejected for a proof-body-exposing mode.
        let denied = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "markdown",
        }).as_object().unwrap().clone())).await;
        assert!(denied.is_err(), "exporting a proof body for a benchmark-linked problem must be gated by default");

        // With the flag: allowed.
        let allowed = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "markdown", "allow_putnambench_proof_export": true,
        }).as_object().unwrap().clone())).await.unwrap();
        let text = allowed.content[0].as_text().unwrap().text.clone();
        assert!(text.contains("trivial"), "with the explicit opt-in, the proof body must be included: {text}");

        // public_summary needs no opt-in, ever.
        let summary = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "public_summary",
        }).as_object().unwrap().clone())).await;
        assert!(summary.is_ok(), "public_summary must never require the opt-in flag");

        // Issue #34's tool-classification audit found a real gap:
        // trajectory_export's raw payload_json carries the exact same
        // completed proof body content (the solve action's proof_term) but
        // originally had no equivalent gate at all — an ungated side channel
        // around the #33 contamination policy proof_export enforces.
        let traj_denied = peer.call_tool(CallToolRequestParams::new("trajectory_export").with_arguments(serde_json::json!({
            "episode_id": episode_id,
        }).as_object().unwrap().clone())).await;
        assert!(traj_denied.is_err(), "trajectory_export of a benchmark-linked episode must be gated by default, same as proof_export");

        let traj_allowed = tool_json(&peer.call_tool(CallToolRequestParams::new("trajectory_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "allow_putnambench_proof_export": true,
        }).as_object().unwrap().clone())).await.unwrap());
        let traj_text = serde_json::to_string(&traj_allowed).unwrap();
        assert!(traj_text.contains("trivial"), "with the explicit opt-in, trajectory_export must still include the real payload: {traj_text}");
    }

    #[tokio::test]
    async fn test_proof_export_ambiguous_suite_match_still_gates_without_misattribution() {
        // If the identical root_formal_statement is registered under TWO
        // distinct benchmark suites, the suite lookup must not silently pick
        // an arbitrary one (nondeterministic, possibly wrong) — it must still
        // gate (the safe default) but report the ambiguity honestly rather
        // than a specific, possibly-incorrect suite name.
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let statement = "putnam_ambiguous_dup_statement";
        let suite_a = create_suite(&peer, "SuiteA").await;
        let suite_b = create_suite(&peer, "SuiteB").await;
        for (suite_id, upstream_id) in [(&suite_a, "a1"), (&suite_b, "b1")] {
            tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
                "suite_id": suite_id, "upstream_problem_id": upstream_id, "theorem_name": upstream_id,
                "root_formal_statement": statement,
            }).as_object().unwrap().clone())).await.unwrap());
        }

        let pv_id = create_problem(&peer, statement).await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "ambig-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "trivial"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        // Still gated without the flag (safe default for an ambiguous match).
        let denied = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "markdown",
        }).as_object().unwrap().clone())).await;
        assert!(denied.is_err(), "an ambiguous suite match must still gate by default, not silently pick one");
        let err_text = format!("{:?}", denied.unwrap_err());
        assert!(err_text.contains("ambiguous") && !err_text.contains("SuiteA") && !err_text.contains("SuiteB"),
            "the error must report ambiguity honestly, not a specific (possibly wrong) suite name: {err_text}");

        // public_summary must not misattribute a specific suite either.
        let summary = tool_json(&peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "public_summary",
        }).as_object().unwrap().clone())).await.unwrap());
        let suite_field = summary["benchmark_suite"].as_str().unwrap_or("");
        assert!(suite_field.contains("ambiguous"), "public_summary must not silently attribute one specific suite when the match is ambiguous: {summary}");
        assert!(summary["benchmark_upstream_problem_id"].is_null(), "an ambiguous match must not report a specific upstream problem id either: {summary}");
    }

    #[tokio::test]
    async fn test_proof_export_audit_archive_contains_failed_attempts() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "audit archive check").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "audit-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        // A failing attempt (contains "sorry" -> MockGateway returns KernelFail).
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "sorry"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "audit_archive", "allow_putnambench_proof_export": true,
        }).as_object().unwrap().clone())).await.unwrap();
        let text = res.content[0].as_text().unwrap().text.clone();
        assert!(text.contains("AUDIT ARCHIVE"), "audit_archive must carry its private banner: {text}");
        assert!(text.contains("❌"), "audit_archive must show the failed attempt's diagnostic: {text}");
    }

    #[tokio::test]
    async fn test_proof_export_training_export_produces_structured_records() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "training export check").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "train-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "norm_num"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "training_export", "allow_putnambench_proof_export": true,
        }).as_object().unwrap().clone())).await.unwrap();
        let text = res.content[0].as_text().unwrap().text.clone();
        let parsed: serde_json::Value = serde_json::from_str(&text).expect("training_export must be valid JSON");
        let arr = parsed.as_array().expect("training_export must be a JSON array");
        assert!(!arr.is_empty(), "training_export must contain at least one record");
        assert!(arr[0].get("action").is_some(), "each record must carry an action field: {text}");
        assert!(arr[0].get("reward").is_some(), "each record must carry a reward field: {text}");
    }

    #[tokio::test]
    async fn test_proof_export_paper_dossier_contains_narrative() {
        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let pv_id = create_problem(&peer, "paper dossier check").await;
        let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
            "problem_version_id": pv_id, "max_steps": 5,
        }).as_object().unwrap().clone())).await.unwrap());
        let episode_id = ep["episode_id"].as_str().unwrap().to_string();
        let req = &ep["next_action_request"];
        let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": "paper-1",
            "expected_revision": req["episode_revision"],
        }).as_object().unwrap().clone())).await.unwrap());
        tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
            "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
            "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
            "action": {"type": "solve", "proof_term": "norm_num"}, "cost_micros": 1,
        }).as_object().unwrap().clone())).await.unwrap());

        let res = peer.call_tool(CallToolRequestParams::new("proof_export").with_arguments(serde_json::json!({
            "episode_id": episode_id, "format": "paper_dossier", "allow_putnambench_proof_export": true,
        }).as_object().unwrap().clone())).await.unwrap();
        let text = res.content[0].as_text().unwrap().text.clone();
        assert!(text.contains("## Narrative"), "paper_dossier must include a written narrative section, not just tables: {text}");
        assert!(text.contains("PAPER DOSSIER"), "paper_dossier must carry its private banner: {text}");
    }

    /// Issue #36's code-review guard: the PutnamBench runner must never call
    /// `RealLeanGateway`/`LeanGateway::verify_exact`/`verify_module`
    /// directly for candidate proof search — its only path to Lean must be
    /// the tracked `episode_step` MCP tool. A static source-text check
    /// (embedded at compile time, same as the smoke fixture below) is
    /// deliberately simpler and more robust than trying to intercept calls
    /// at runtime: if a future change ever adds a "shortcut" direct-gateway
    /// call to the runner (e.g. to pre-screen a candidate before submitting
    /// it), this fails immediately and unambiguously, regardless of whether
    /// any test happens to exercise that code path.
    #[test]
    fn test_putnam_runner_never_references_lean_gateway_directly() {
        const RUNNER_SOURCE: &str = include_str!("../examples/putnam_runner.rs");
        // Strip comment lines first — the module's own doc comment
        // legitimately NAMES these APIs (backtick-quoted) to explain the
        // invariant it upholds; only actual code usage should fail this.
        let code_only: String = RUNNER_SOURCE.lines()
            .filter(|line| !line.trim_start().starts_with("//"))
            .collect::<Vec<_>>().join("\n");
        for forbidden in ["RealLeanGateway", "verify_exact(", "verify_module(", "LeanGateway::verify"] {
            assert!(!code_only.contains(forbidden),
                "putnam_runner.rs must never reference {:?} in actual code — issue #36: a proof attempt that bypasses episode_step is not part of ChatDB evidence", forbidden);
        }
    }

    // PutnamBench smoke subset (issue #32). Embedded at compile time via
    // include_str! — this test needs NO CHATDB_PUTNAM_BENCH_PATH / external
    // clone, so it runs in every normal `cargo test`, unlike a full-suite
    // import/run which is deliberately opt-in only (see
    // docs/benchmarks/putnambench.md).
    const PUTNAMBENCH_SMOKE_FIXTURE: &str = include_str!("../../../benchmarks/putnambench_smoke.json");

    #[derive(serde::Deserialize)]
    struct SmokeImportFixture {
        upstream_problem_id: String,
        theorem_name: String,
        root_formal_statement: String,
        root_statement_hash: String,
        prover_ready_statement_hash: Option<String>,
        import_manifest: Vec<String>,
    }

    #[derive(serde::Deserialize)]
    struct SmokeCannedProofFixture {
        fixture_id: String,
        kind: String,
        root_formal_statement: String,
        import_manifest: Vec<String>,
        attempt: serde_json::Value,
        expected_status: String,
    }

    #[derive(serde::Deserialize)]
    struct SmokeFixtureFile {
        import_fixtures: Vec<SmokeImportFixture>,
        canned_proof_fixtures: Vec<SmokeCannedProofFixture>,
    }

    #[tokio::test]
    async fn test_putnambench_smoke_import_fixtures_register_with_stable_hashes() {
        // Real, embedded PutnamBench problems (not synthetic) — verifies the
        // importer's hash computation is stable over time: if canonical_hash
        // or to_pi_form's conversion ever changes behavior, these
        // hand-verified expected hashes (captured against the real corpus at
        // commit a23d8e6d4e9e3418fd78f76de7bfcb9414cbfd39) would catch it.
        let fixture: SmokeFixtureFile = serde_json::from_str(PUTNAMBENCH_SMOKE_FIXTURE).unwrap();
        assert!(fixture.import_fixtures.len() >= 5, "issue #32 requires 5-10 selected Lean targets");

        let client = connected_client(test_handler_with_gateway(MockGateway)).await;
        let peer = client.peer();
        let suite_id = create_suite(&peer, "PutnamBenchSmoke").await;

        for f in &fixture.import_fixtures {
            let registered = tool_json(&peer.call_tool(CallToolRequestParams::new("benchmark_problem_register").with_arguments(serde_json::json!({
                "suite_id": suite_id, "upstream_problem_id": f.upstream_problem_id, "theorem_name": f.theorem_name,
                "root_formal_statement": f.root_formal_statement, "import_manifest": f.import_manifest,
            }).as_object().unwrap().clone())).await.unwrap());
            assert_eq!(registered["root_statement_hash"], f.root_statement_hash,
                "root_statement_hash for {} must match the hand-verified expected value — canonical_hash must be stable", f.upstream_problem_id);
            match &f.prover_ready_statement_hash {
                Some(expected) => assert_eq!(registered["prover_ready_statement_hash"], *expected,
                    "prover_ready_statement_hash for {} must match — to_pi_form's conversion must be stable", f.upstream_problem_id),
                None => assert!(registered["prover_ready_statement_hash"].is_null()),
            }
        }
    }

    #[tokio::test]
    async fn test_putnambench_smoke_canned_proof_fixtures_produce_expected_status() {
        // Deliberately synthetic statements (real Putnam problems require
        // genuine multi-step argument, not a one-line tactic) — this is the
        // "canned-proof fixture" / "expected-fail fixture" modes issue #32
        // asks for: at least one Solve-only success, one SubmitModule
        // success, one intentionally-bad attempt, all driven through the
        // real episode_step path and checked against the fixture's own
        // expected_status.
        let fixture: SmokeFixtureFile = serde_json::from_str(PUTNAMBENCH_SMOKE_FIXTURE).unwrap();
        assert!(fixture.canned_proof_fixtures.iter().any(|f| f.kind == "solve_only" && f.expected_status == "kernel_verified"),
            "issue #32 requires at least one Solve-only success fixture");
        assert!(fixture.canned_proof_fixtures.iter().any(|f| matches!(f.attempt["type"].as_str(), Some("submit_module")) && f.expected_status == "kernel_verified"),
            "issue #32 requires at least one SubmitModule success fixture");
        assert!(fixture.canned_proof_fixtures.iter().any(|f| f.expected_status != "kernel_verified" && f.expected_status != "certified"),
            "issue #32 requires at least one expected-failure fixture");

        for f in &fixture.canned_proof_fixtures {
            let client = connected_client(test_handler_with_gateway(MockGateway)).await;
            let peer = client.peer();
            let pv = tool_json(&peer.call_tool(CallToolRequestParams::new("problem_create").with_arguments(serde_json::json!({
                "source_problem_text": format!("smoke fixture: {}", f.fixture_id),
                "root_formal_statement": f.root_formal_statement,
                "problem_imports": f.import_manifest,
                "unsafe_dev_attestation": true,
            }).as_object().unwrap().clone())).await.unwrap());
            let ep = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_create").with_arguments(serde_json::json!({
                "problem_version_id": pv["problem_version_id"], "max_steps": 5,
            }).as_object().unwrap().clone())).await.unwrap());
            let episode_id = ep["episode_id"].as_str().unwrap().to_string();
            let req = &ep["next_action_request"];
            let claim = tool_json(&peer.call_tool(CallToolRequestParams::new("attempt_claim").with_arguments(serde_json::json!({
                "episode_id": episode_id, "action_request_id": req["id"], "idempotency_key": format!("{}-1", f.fixture_id),
                "expected_revision": req["episode_revision"],
            }).as_object().unwrap().clone())).await.unwrap());
            let step = tool_json(&peer.call_tool(CallToolRequestParams::new("episode_step").with_arguments(serde_json::json!({
                "episode_id": episode_id, "action_attempt_id": claim["action_attempt_id"],
                "expected_revision": req["episode_revision"], "claim_token": claim["claim_token"],
                "action": f.attempt, "cost_micros": 1,
            }).as_object().unwrap().clone())).await.unwrap());

            match f.expected_status.as_str() {
                "kernel_verified" | "certified" => assert_eq!(step["outcome"], f.expected_status,
                    "fixture {} expected {} but got: {:?}", f.fixture_id, f.expected_status, step),
                _ => {
                    // A real adversarial-review finding: `outcome` is JSON
                    // null after ANY non-terminal step (a genuine kernel
                    // rejection with attempts remaining, an infra hiccup, a
                    // malformed action that still parsed) — asserting only
                    // `outcome != "kernel_verified"` would pass identically
                    // for all of those, not specifically for "the kernel
                    // correctly rejected this attempt." `accepted: false`
                    // is the field that actually means the verification
                    // step ran and was rejected, which is what an
                    // expected-failure fixture must demonstrate.
                    assert_eq!(step["accepted"], false,
                        "fixture {} is an expected-failure case and the step must be rejected (accepted=false), not just non-terminal: {:?}", f.fixture_id, step);
                    assert_ne!(step["outcome"], "kernel_verified", "{:?}", step);
                    assert_ne!(step["outcome"], "certified", "{:?}", step);
                }
            }
        }
    }
}
