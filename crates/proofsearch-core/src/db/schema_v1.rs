use rusqlite::Connection;
use serde_json;

pub const V1_SCHEMA: &str = r#"
-- Canonical Tables
CREATE TABLE IF NOT EXISTS schema_migrations (
    version INTEGER PRIMARY KEY,
    applied_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS problem_versions (
    id TEXT PRIMARY KEY,
    source_problem_text TEXT NOT NULL,
    source_problem_hash TEXT NOT NULL,
    source_metadata_json TEXT NOT NULL,
    root_formal_statement TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    normalized_root_rendering TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    -- Immutable per problem_version: the exact Lean import closure the verifier
    -- compiles candidate proofs against. An 'unknown identifier' failure only
    -- ever establishes that a name didn't resolve under THIS manifest — never
    -- that it's absent from the pinned library. See lean_declaration_lookup and
    -- docs/fix_plan_playtest_03.md. Defaults preserve the pre-manifest behavior
    -- (Ring + NormNum) for rows/fixtures that predate this column.
    import_manifest_json TEXT NOT NULL DEFAULT '["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum"]',
    import_manifest_hash TEXT NOT NULL DEFAULT '',
    fidelity_status TEXT NOT NULL,
    fidelity_method TEXT NOT NULL,
    fidelity_approval_id TEXT,
    root_obligation_id TEXT,
    state TEXT NOT NULL,
    created_at TEXT NOT NULL,
    -- 'attested' (an honest, explicitly-named dev bypass — see problem_create's
    -- unsafe_dev_attestation) may enter proving, but only a real
    -- problem_submit_fidelity_review decision can reach 'verified', and only
    -- 'verified' may reach COMPLETE. This is the DB-level backstop for the
    -- proof-soundness-vs-statement-fidelity invariant; see docs/fix_plan_playtest_02.md.
    -- 'benchmark_aligned' (issue #43) is proving-capable like 'attested' but
    -- honestly named: a curated-benchmark hash-alignment basis, NOT independent
    -- NL review. It is deliberately absent from the COMPLETE check below, so it
    -- can reach kernel_verified but never 'certified'/COMPLETE.
    CHECK(state NOT IN ('PROVING', 'ROOT_PROVED_COVERAGE_PENDING', 'ROOT_PROVED_COVERAGE_UNCONVERGED') OR fidelity_status IN ('verified', 'attested', 'benchmark_aligned')),
    CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified'),
    CHECK(fidelity_status IN ('unreviewed', 'attested', 'verified', 'rejected', 'revoked', 'benchmark_aligned'))
);

-- Fidelity belongs to the problem version, not to any one proof episode: an
-- immutable record of who/what decided the formal statement represents the
-- source problem, bound to the exact hashes reviewed so a later edit can never
-- silently inherit an old approval.
CREATE TABLE IF NOT EXISTS problem_fidelity_reviews (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    source_problem_hash TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    normalized_rendering_hash TEXT NOT NULL,
    decision TEXT NOT NULL,
    method TEXT NOT NULL,
    approver_id TEXT NOT NULL,
    rubric_version TEXT NOT NULL,
    evidence_json TEXT NOT NULL,
    notes TEXT,
    signature TEXT,
    created_at TEXT NOT NULL,
    revoked_at TEXT,
    -- 'benchmark_aligned' (issue #43): the formal_benchmark_hash_alignment basis
    -- — recorded via problem_record_benchmark_alignment, never a path to certified.
    CHECK(decision IN ('verified', 'rejected', 'benchmark_aligned'))
);

CREATE TABLE IF NOT EXISTS canonical_verified_lemmas (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    obligation_id TEXT NOT NULL,
    polarity TEXT NOT NULL,
    theorem_name TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    proof_source_artifact_hash TEXT NOT NULL,
    compiled_artifact_hash TEXT NOT NULL,
    proof_term_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    actual_dependency_ids_json TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    verified_at TEXT NOT NULL,
    CHECK(polarity IN ('positive', 'negative'))
);

CREATE TABLE IF NOT EXISTS canonical_certificates (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    root_obligation_id TEXT NOT NULL,
    root_verified_lemma_id TEXT NOT NULL REFERENCES canonical_verified_lemmas(id),
    root_statement_hash TEXT NOT NULL,
    root_proof_artifact_hash TEXT NOT NULL,
    proof_dependency_manifest_hash TEXT NOT NULL,
    active_sketch_snapshot_hash TEXT NOT NULL,
    toolchain_manifest_hash TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    coverage_state TEXT NOT NULL,
    convergence_record_hash TEXT,
    kernel_verified_at TEXT NOT NULL,
    completed_at TEXT,
    CHECK(coverage_state IN ('pending', 'converged', 'unconverged', 'integrity_blocked'))
);

CREATE TABLE IF NOT EXISTS approved_formalizations (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    lean_statement TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    normalized_rendering TEXT NOT NULL,
    quantifiers_json TEXT NOT NULL,
    hypotheses_json TEXT NOT NULL,
    domain_restrictions_json TEXT NOT NULL,
    origin_type TEXT NOT NULL,
    origin_config_hash TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(problem_version_id, statement_hash)
);

-- Episode-Local Tables
CREATE TABLE IF NOT EXISTS episodes (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    task_id TEXT,
    task_revision INTEGER,
    environment_version TEXT,
    protocol_version TEXT,
    observation_schema_version TEXT,
    action_schema_version TEXT,
    reward_policy_version TEXT,
    verifier_version TEXT,
    lean_toolchain_version TEXT,
    seed INTEGER,
    state TEXT NOT NULL,
    current_revision INTEGER NOT NULL DEFAULT 0,
    initial_state_hash TEXT,
    current_state_hash TEXT,
    step_count INTEGER NOT NULL DEFAULT 0,
    max_steps INTEGER,
    token_budget INTEGER,
    cost_budget_micros INTEGER,
    wall_clock_deadline TEXT,
    invalid_action_count INTEGER NOT NULL DEFAULT 0,
    invalid_action_limit INTEGER,
    outcome TEXT,
    termination_reason TEXT,
    truncation_reason TEXT,
    run_id TEXT,
    parent_episode_id TEXT REFERENCES episodes(id),
    created_at TEXT NOT NULL,
    updated_at TEXT,
    completed_at TEXT,
    CHECK(state IN ('awaiting_external_action', 'executing_action', 'terminated', 'truncated')),
    -- 'kernel_verified': the root obligation passed the Lean kernel but the
    -- problem's statement fidelity is not (yet) 'verified' — proof soundness
    -- without statement fidelity. Distinct from 'certified', which requires both.
    -- Never treat 'kernel_verified' as a synonym for 'certified' downstream.
    CHECK(outcome IN ('certified', 'kernel_verified', 'refuted', 'gave_up', 'timeout', 'budget_exhausted', 'model_error', 'infrastructure_error') OR outcome IS NULL),
    CHECK((state = 'terminated' AND outcome IS NOT NULL AND termination_reason IS NOT NULL) OR state <> 'terminated'),
    CHECK((state = 'truncated' AND outcome IS NOT NULL AND truncation_reason IS NOT NULL) OR state <> 'truncated'),
    CHECK(NOT (state = 'terminated' AND truncation_reason IS NOT NULL)),
    CHECK(NOT (state = 'truncated' AND termination_reason IS NOT NULL))
);

CREATE TABLE IF NOT EXISTS episode_obligations (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    kind TEXT NOT NULL,
    theorem_name TEXT NOT NULL,
    lean_statement TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    natural_description TEXT NOT NULL,
    status TEXT NOT NULL,
    depth_from_root INTEGER NOT NULL,
    created_by TEXT NOT NULL,
    created_by_epoch_id TEXT,
    superseded_by_id TEXT REFERENCES episode_obligations(id),
    proved_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    refutation_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    failure_lesson TEXT,
    attempt_count INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL,
    closed_at TEXT,
    UNIQUE(episode_id, theorem_name),
    CHECK(status IN ('open', 'in_progress', 'proved', 'refuted', 'superseded', 'abandoned', 'blocked_needs_human')),
    CHECK(kind IN ('root', 'proof', 'coverage', 'counterexample')),
    CHECK(created_by IN ('initial_sketch', 'decomposition', 'reviewer', 'human')),
    CHECK(
      (status = 'proved' AND proved_lemma_id IS NOT NULL AND refutation_lemma_id IS NULL) OR
      (status = 'refuted' AND refutation_lemma_id IS NOT NULL AND proved_lemma_id IS NULL) OR
      (status NOT IN ('proved', 'refuted') AND proved_lemma_id IS NULL AND refutation_lemma_id IS NULL)
    )
);

CREATE TABLE IF NOT EXISTS episode_obligation_edges (
    parent_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    dependency_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    edge_kind TEXT NOT NULL,
    case_group TEXT,
    created_at TEXT NOT NULL,
    PRIMARY KEY(parent_obligation_id, dependency_obligation_id),
    CHECK(parent_obligation_id <> dependency_obligation_id),
    CHECK(edge_kind IN ('lemma', 'case_branch', 'witness', 'reduction'))
);

CREATE TABLE IF NOT EXISTS episode_proposal_attempts (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    role TEXT NOT NULL,
    model_config_hash TEXT,
    prompt_hash TEXT NOT NULL,
    context_manifest_hash TEXT NOT NULL,
    candidate_source_artifact_hash TEXT,
    diagnostic_json TEXT,
    outcome TEXT NOT NULL,
    input_tokens INTEGER NOT NULL,
    output_tokens INTEGER NOT NULL,
    cost_usd_micros INTEGER NOT NULL,
    wall_time_ms INTEGER NOT NULL,
    lean_cpu_time_ms INTEGER NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(outcome IN ('kernel_pass', 'kernel_fail', 'preflight_reject', 'model_invalid_output', 'infrastructure_error', 'budget_denied', 'timeout', 'cancelled'))
);

CREATE TABLE IF NOT EXISTS episode_verified_lemmas (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    polarity TEXT NOT NULL,
    theorem_name TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    proof_source_artifact_hash TEXT NOT NULL,
    compiled_artifact_hash TEXT NOT NULL,
    proof_term_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    actual_dependency_ids_json TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    verified_at TEXT NOT NULL,
    UNIQUE(obligation_id, polarity),
    CHECK(polarity IN ('positive', 'negative'))
);

-- A verified module submission (defs + helper theorems + root theorem checked
-- as one unit — see docs/submit_module.md). One row per successful SubmitModule.
-- Episode-local, like episode_verified_lemmas: canonical/promotion equivalents
-- can come later, but the verified development must be remembered as a
-- structured, replayable artifact NOW so module solves become training data,
-- not just a compiled side effect. module_items_json holds the exact structured
-- items + root theorem, so the precise Lean source re-assembles deterministically
-- (its hash must equal module_source_hash).
CREATE TABLE IF NOT EXISTS episode_verified_modules (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    root_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    root_statement_hash TEXT NOT NULL,
    import_manifest_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    module_source_hash TEXT NOT NULL,
    module_items_json TEXT NOT NULL,
    declaration_manifest_hash TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    verified_at TEXT NOT NULL,
    UNIQUE(episode_id, root_obligation_id, module_source_hash)
);

-- One row per declaration in a verified module, in assembly order. item_kind
-- is 'def' | 'theorem' | 'root_theorem' (a MutualGroup member is still 'def'
-- or 'theorem' — the grouping itself is recorded in mutual_group, not a
-- distinct item_kind); the single root_theorem row is explicitly linked to the
-- root obligation via its parent module row. mutual_group is NULL for a
-- standalone item/the root theorem, or a 0-based group index shared by every
-- member of the same `mutual ... end` block (issue #19) — purely
-- informational: replay/export never key on it, since the exact source
-- re-assembles from the parent module's module_items_json regardless.
CREATE TABLE IF NOT EXISTS episode_verified_module_items (
    id TEXT PRIMARY KEY,
    module_id TEXT NOT NULL REFERENCES episode_verified_modules(id),
    item_order INTEGER NOT NULL,
    item_kind TEXT NOT NULL,
    lean_name TEXT NOT NULL,
    statement_or_type_hash TEXT NOT NULL,
    body_hash TEXT NOT NULL,
    depends_on_json TEXT NOT NULL,
    policy_result_json TEXT NOT NULL,
    mutual_group INTEGER,
    UNIQUE(module_id, item_order),
    CHECK(item_kind IN ('def', 'theorem', 'root_theorem'))
);

CREATE TABLE IF NOT EXISTS episode_budget_ledger (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    obligation_id TEXT REFERENCES episode_obligations(id),
    call_kind TEXT NOT NULL,
    reservation_id TEXT NOT NULL,
    state TEXT NOT NULL,
    reserved_input_tokens INTEGER NOT NULL,
    reserved_output_tokens INTEGER NOT NULL,
    actual_input_tokens INTEGER,
    actual_output_tokens INTEGER,
    reserved_cost_usd_micros INTEGER NOT NULL,
    actual_cost_usd_micros INTEGER,
    reserved_wall_time_ms INTEGER NOT NULL,
    actual_wall_time_ms INTEGER,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS episode_review_epochs (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    epoch_number INTEGER NOT NULL,
    trigger TEXT NOT NULL,
    eligible BOOLEAN NOT NULL,
    reviewer_count INTEGER NOT NULL,
    diverse_family_count INTEGER NOT NULL,
    lens_count INTEGER NOT NULL,
    admitted_count INTEGER NOT NULL,
    surviving_count INTEGER,
    surviving_rate REAL,
    ema_rate REAL,
    created_at TEXT NOT NULL,
    completed_at TEXT,
    UNIQUE(episode_id, epoch_number)
);

CREATE TABLE IF NOT EXISTS episode_review_proposals (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    epoch_id TEXT NOT NULL REFERENCES episode_review_epochs(id),
    reviewer_config_hash TEXT NOT NULL,
    lens TEXT NOT NULL,
    natural_description TEXT NOT NULL,
    proposed_lean_statement TEXT NOT NULL,
    proposed_statement_hash TEXT NOT NULL,
    proposed_dependencies_json TEXT NOT NULL,
    proposal_kind TEXT NOT NULL,
    admission_outcome TEXT,
    admitted_obligation_id TEXT REFERENCES episode_obligations(id),
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS episode_certificate_candidates (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    root_obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    root_verified_lemma_id TEXT NOT NULL REFERENCES episode_verified_lemmas(id),
    root_statement_hash TEXT NOT NULL,
    root_proof_artifact_hash TEXT NOT NULL,
    proof_dependency_manifest_hash TEXT NOT NULL,
    active_sketch_snapshot_hash TEXT NOT NULL,
    toolchain_manifest_hash TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    coverage_state TEXT NOT NULL,
    convergence_record_hash TEXT,
    kernel_verified_at TEXT NOT NULL,
    completed_at TEXT,
    CHECK(coverage_state IN ('pending', 'converged', 'unconverged', 'integrity_blocked'))
);

CREATE TABLE IF NOT EXISTS episode_drafts (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    model_config_hash TEXT NOT NULL,
    prompt_template_hash TEXT NOT NULL,
    content_artifact_hash TEXT NOT NULL,
    extracted_moves_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS episode_formalization_candidates (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    lean_statement TEXT NOT NULL,
    statement_hash TEXT NOT NULL,
    normalized_rendering TEXT NOT NULL,
    quantifiers_json TEXT NOT NULL,
    hypotheses_json TEXT NOT NULL,
    domain_restrictions_json TEXT NOT NULL,
    origin_type TEXT NOT NULL,
    origin_config_hash TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(episode_id, statement_hash)
);

CREATE TABLE IF NOT EXISTS episode_fidelity_reviews (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    source_problem_hash TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    rendering_hash TEXT NOT NULL,
    approval_method TEXT NOT NULL,
    approver_id TEXT NOT NULL,
    signature TEXT,
    notes TEXT,
    created_at TEXT NOT NULL
);

-- Proof-pattern memory (issue #24): reusable repair doctrine mined from real
-- attempts (Mathlib API drift, def-unfold-before-decide, well-founded
-- recursion needing simp, mutual recursion needing MutualGroup, ...). Purely
-- advisory — a pattern can inform what a client tries next, but nothing here
-- can mark an obligation proved, change fidelity status, or affect
-- certification; only a real Lean kernel pass does that. See
-- docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md for the seed
-- patterns' provenance.
CREATE TABLE IF NOT EXISTS proof_patterns (
    id TEXT PRIMARY KEY,
    pattern_key TEXT NOT NULL UNIQUE,
    title TEXT NOT NULL,
    failure_signature TEXT NOT NULL,
    recommended_repair TEXT NOT NULL,
    applicable_when_json TEXT NOT NULL,
    avoid_when_json TEXT NOT NULL,
    -- NULL for a seeded/hand-authored pattern with no single originating
    -- episode (or when that episode was in a scratch/dev database and isn't
    -- present here).
    source_episode_id TEXT REFERENCES episodes(id),
    source_attempt_ids_json TEXT NOT NULL,
    confidence TEXT NOT NULL,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(confidence IN ('seed', 'mined', 'confirmed')),
    CHECK(status IN ('active', 'deprecated'))
);

-- One row per real (episode[, attempt]) association with a pattern: a failing
-- attempt the pattern's failure_signature matched, a repaired attempt that
-- applied the recommended_repair, or an advisory hint surfaced to a client
-- before it acted. Deliberately insert-only metadata: recording an
-- application never writes to episodes/episode_obligations/action_attempts —
-- see the regression test in proofsearch-mcp's proof_pattern tests.
CREATE TABLE IF NOT EXISTS proof_pattern_applications (
    id TEXT PRIMARY KEY,
    pattern_id TEXT NOT NULL REFERENCES proof_patterns(id),
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    action_attempt_id TEXT REFERENCES action_attempts(id),
    role TEXT NOT NULL,
    notes TEXT,
    created_at TEXT NOT NULL,
    CHECK(role IN ('failed_example', 'repair_example', 'suggested_hint'))
);

-- Draft artifacts (issue #23): informal reasoning/planning content, explicitly
-- untrusted. A draft can NEVER mark anything proved and never itself creates
-- an obligation — it exists purely so an informal sketch gets preserved and
-- structured before formalization planning begins. episode_id is nullable: a
-- draft may exist before any episode is created for the problem.
CREATE TABLE IF NOT EXISTS drafts (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    content TEXT NOT NULL,
    content_hash TEXT NOT NULL,
    author TEXT NOT NULL,
    created_at TEXT NOT NULL
);

-- Formalization plans (issue #10 + #23, designed together: both issues wanted
-- to own this schema — #23 as the promotion target for draft moves, #10 as
-- the Mathlib-coverage-tracking roadmap). source_draft_id is nullable: a plan
-- can be created directly, without going through a draft first.
CREATE TABLE IF NOT EXISTS formalization_plans (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    source_draft_id TEXT REFERENCES drafts(id),
    title TEXT NOT NULL,
    status TEXT NOT NULL,
    risk_flags_json TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(status IN ('draft', 'active', 'completed', 'abandoned'))
);

-- One row per planned concept/definition/lemma/module/citation. Advisory —
-- mathlib_coverage_status and lookup_result_json are hints from
-- lean_declaration_lookup, never a proof authority; promoted_obligation_id is
-- a metadata LINK to an obligation that already exists (created through the
-- normal, budget-accounted Decompose action), never created by this table's
-- own tools. An item is promotable exactly once (status transitions
-- open -> promoted, never back), so a client can't silently double-link.
CREATE TABLE IF NOT EXISTS formalization_plan_items (
    id TEXT PRIMARY KEY,
    plan_id TEXT NOT NULL REFERENCES formalization_plans(id),
    item_order INTEGER NOT NULL,
    kind TEXT NOT NULL,
    description TEXT NOT NULL,
    mathlib_coverage_status TEXT NOT NULL,
    mathlib_candidate_names_json TEXT NOT NULL,
    lookup_result_json TEXT,
    promoted_obligation_id TEXT REFERENCES episode_obligations(id),
    -- Issue #12: optional growth-rate role, so an asymptotic proof's steps
    -- (a lower/upper growth bound, an infinite-family extraction, a
    -- sufficiently-large threshold, a limit comparison) are labeled distinctly
    -- from finite sanity checks. Descriptive only; never proof authority. Added
    -- to pre-existing DBs by migrate_add_plan_item_asymptotic_role_column.
    asymptotic_role TEXT,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(plan_id, item_order),
    CHECK(kind IN ('concept', 'missing_definition', 'missing_lemma', 'planned_module', 'external_citation')),
    CHECK(mathlib_coverage_status IN ('unknown', 'found', 'not_found', 'partial')),
    CHECK(status IN ('open', 'promoted', 'dropped')),
    CHECK(asymptotic_role IS NULL OR asymptotic_role IN ('growth_lower_bound', 'growth_upper_bound', 'infinite_family_extraction', 'sufficiently_large_threshold', 'limit_comparison'))
);

-- One row per extracted move within a draft, in the order the client
-- identified them. The server never infers these itself (no inference code
-- lives in LLM-Driven Proof Search Environment) — the external agent proposes structured moves the same
-- way Decompose's sub_lemmas are client-proposed, and this table just
-- persists them. promoted_plan_item_id links a move to the plan item it
-- seeded, once promoted (nullable: most moves are metadata, never promoted).
CREATE TABLE IF NOT EXISTS draft_moves (
    id TEXT PRIMARY KEY,
    draft_id TEXT NOT NULL REFERENCES drafts(id),
    move_order INTEGER NOT NULL,
    move_kind TEXT NOT NULL,
    description TEXT NOT NULL,
    promoted_plan_item_id TEXT REFERENCES formalization_plan_items(id),
    created_at TEXT NOT NULL,
    UNIQUE(draft_id, move_order),
    CHECK(move_kind IN ('construction', 'auxiliary_lemma', 'case_split', 'induction', 'reduction', 'bijection', 'counterexample_search', 'asymptotic_step', 'external_citation', 'unknown'))
);

-- Self-review finding: without this, two different plan items (in the same
-- plan or different ones) could both claim the same real obligation via
-- formalization_plan_promote_item_to_obligation, silently "double-spending"
-- one real obligation across multiple plan-tracking rows. A partial index
-- (SQLite supports a WHERE clause on a UNIQUE index) since most rows have
-- promoted_obligation_id = NULL and NULLs must stay unconstrained.
CREATE UNIQUE INDEX IF NOT EXISTS idx_formalization_plan_items_promoted_obligation
    ON formalization_plan_items(promoted_obligation_id) WHERE promoted_obligation_id IS NOT NULL;

-- Level 4 research substrate (issues #9, #11, #13): paper-scale research
-- state, external citation/assumption boundaries, and independent verification
-- layers. These tables are deliberately metadata-only: no row here can mark an
-- episode obligation proved, create a canonical lemma, certify a problem, or
-- change a proof outcome. Kernel verification still lives only in the existing
-- Lean-backed episode/canonical tables.
CREATE TABLE IF NOT EXISTS research_dossiers (
    id TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    description TEXT,
    problem_version_id TEXT REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(status IN ('draft', 'active', 'blocked', 'completed', 'abandoned'))
);

CREATE TABLE IF NOT EXISTS research_sections (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    section_order INTEGER NOT NULL,
    title TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(dossier_id, section_order)
);

CREATE TABLE IF NOT EXISTS research_nodes (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    section_id TEXT REFERENCES research_sections(id),
    node_order INTEGER NOT NULL,
    node_type TEXT NOT NULL,
    title TEXT NOT NULL,
    statement TEXT,
    content TEXT,
    trust_status TEXT NOT NULL,
    linked_obligation_id TEXT REFERENCES episode_obligations(id),
    linked_verified_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    UNIQUE(dossier_id, node_order),
    CHECK(node_type IN ('definition', 'proposition', 'lemma', 'theorem', 'remark', 'reference', 'open_gap')),
    CHECK(trust_status IN (
        'open_gap',
        'proved_in_episode',
        'imported_from_mathlib',
        'external_citation_unreviewed',
        'external_citation_human_reviewed',
        'unformalized_assumption',
        'rejected_unsafe_assumption'
    )),
    CHECK(trust_status <> 'proved_in_episode' OR linked_verified_lemma_id IS NOT NULL)
);

CREATE TABLE IF NOT EXISTS external_references (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    title TEXT NOT NULL,
    authors TEXT,
    venue TEXT,
    year TEXT,
    url TEXT,
    doi TEXT,
    raw_citation TEXT,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS external_theorem_claims (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    reference_id TEXT REFERENCES external_references(id),
    node_id TEXT REFERENCES research_nodes(id),
    label TEXT NOT NULL,
    statement TEXT NOT NULL,
    claim_status TEXT NOT NULL,
    mathlib_name TEXT,
    proved_episode_id TEXT REFERENCES episodes(id),
    proved_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    notes TEXT,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(claim_status IN (
        'proved_in_episode',
        'imported_from_mathlib',
        'external_citation_unreviewed',
        'external_citation_human_reviewed',
        'unformalized_assumption',
        'rejected_unsafe_assumption'
    )),
    CHECK(claim_status <> 'proved_in_episode' OR proved_lemma_id IS NOT NULL),
    CHECK(claim_status <> 'imported_from_mathlib' OR mathlib_name IS NOT NULL)
);

CREATE TABLE IF NOT EXISTS assumption_boundaries (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    node_id TEXT REFERENCES research_nodes(id),
    label TEXT NOT NULL,
    statement TEXT NOT NULL,
    assumption_status TEXT NOT NULL,
    rationale TEXT,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(assumption_status IN ('unformalized_assumption', 'rejected_unsafe_assumption'))
);

CREATE TABLE IF NOT EXISTS citation_reviews (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    external_theorem_claim_id TEXT NOT NULL REFERENCES external_theorem_claims(id),
    reviewer_id TEXT NOT NULL,
    decision TEXT NOT NULL,
    review_status TEXT NOT NULL,
    notes TEXT,
    created_at TEXT NOT NULL,
    CHECK(decision IN ('human_reviewed', 'rejected', 'needs_formalization')),
    CHECK(review_status IN ('external_citation_unreviewed', 'external_citation_human_reviewed', 'rejected_unsafe_assumption'))
);

CREATE TABLE IF NOT EXISTS verification_layers (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    target_kind TEXT NOT NULL,
    target_id TEXT NOT NULL,
    layer_kind TEXT NOT NULL,
    status TEXT NOT NULL,
    summary TEXT,
    evidence_json TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    UNIQUE(dossier_id, target_kind, target_id, layer_kind),
    CHECK(target_kind IN ('dossier', 'node', 'assumption', 'external_theorem_claim', 'problem_version', 'episode')),
    CHECK(layer_kind IN (
        'construction_search',
        'arithmetic_construction',
        'geometric_criterion',
        'packing_or_size_bound',
        'asymptotic_extraction',
        'formal_module',
        'statement_fidelity',
        'external_review',
        'exposition_review'
    )),
    CHECK(status IN ('not_started', 'informal', 'empirical', 'cited', 'human_reviewed', 'kernel_verified', 'failed', 'blocked', 'rejected')),
    CHECK(status <> 'kernel_verified' OR layer_kind IN ('formal_module', 'statement_fidelity'))
);
CREATE INDEX IF NOT EXISTS idx_research_dossiers_problem_version ON research_dossiers(problem_version_id);
CREATE INDEX IF NOT EXISTS idx_research_dossiers_episode ON research_dossiers(episode_id);
CREATE INDEX IF NOT EXISTS idx_research_nodes_dossier ON research_nodes(dossier_id);
CREATE INDEX IF NOT EXISTS idx_external_claims_dossier ON external_theorem_claims(dossier_id);
CREATE INDEX IF NOT EXISTS idx_assumption_boundaries_dossier ON assumption_boundaries(dossier_id);
CREATE INDEX IF NOT EXISTS idx_verification_layers_dossier ON verification_layers(dossier_id);

-- Candidate construction artifacts (issue #8): proposed mathematical objects
-- (graph families, colorings, point configurations, counterexamples, ...)
-- captured as the first durable object layer for MOTIVATED discovery. Beyond
-- "what object is proposed", each row records why it was proposed
-- (motivating_move, source_observation), what role it should play
-- (intended_role), the strategic context and the case for/against it
-- (strategy_context, why_this_might_work, why_this_might_fail), what to check
-- next (next_check), and how it may later connect to downstream systems
-- (verification_targets_json, future_challenge_relevance) -- encoding the
-- observation -> motivated move -> proposed object -> intended role ->
-- next check loop.
--
-- A candidate construction can exist before a dossier is written up, before a
-- Lean theorem exists, before an episode exists, and before #26's empirical
-- math lab exists to generate/test/rank/falsify them. Every link
-- (dossier_id, related_node_id, verification_layer_id, problem_version_id,
-- episode_id) is nullable. It is a research artifact, never proof authority:
-- trust_status='kernel_verified_claim_linked' is the only status this table
-- can carry that claims kernel evidence, and it is only reachable (enforced
-- at the MCP layer, mirroring enforce_kernel_verified_research_boundary) when
-- verification_layer_id names a verification_layers row whose own status is
-- already 'kernel_verified'. empirically_supported / human_reviewed /
-- formalized_statement_exists / linked_to_formal_claim are NOT proof.
CREATE TABLE IF NOT EXISTS candidate_constructions (
    id TEXT PRIMARY KEY,
    dossier_id TEXT REFERENCES research_dossiers(id),
    related_node_id TEXT REFERENCES research_nodes(id),
    verification_layer_id TEXT REFERENCES verification_layers(id),
    problem_version_id TEXT REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    construction_type TEXT NOT NULL,
    name TEXT,
    informal_description TEXT NOT NULL,
    parameters_json TEXT NOT NULL DEFAULT '{}',
    construction_json TEXT NOT NULL DEFAULT '{}',
    claimed_properties_json TEXT NOT NULL DEFAULT '[]',
    known_failures_json TEXT NOT NULL DEFAULT '[]',
    empirical_checks_json TEXT NOT NULL DEFAULT '[]',
    verification_targets_json TEXT NOT NULL DEFAULT '[]',
    -- Motivated-discovery metadata (nullable: a bare object proposal is still
    -- valid, but the discovery loop is what makes the artifact useful).
    motivating_move TEXT,
    source_observation TEXT,
    intended_role TEXT,
    strategy_context TEXT,
    why_this_might_work TEXT,
    why_this_might_fail TEXT,
    next_check TEXT,
    future_challenge_relevance TEXT,
    status TEXT NOT NULL DEFAULT 'proposed',
    trust_status TEXT NOT NULL DEFAULT 'informal',
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(construction_type IN (
        'graph_family',
        'point_configuration',
        'coloring',
        'field_tower',
        'lattice',
        'counterexample',
        'asymptotic_family',
        'algebraic_object',
        'combinatorial_design',
        'other'
    )),
    CHECK(motivating_move IS NULL OR motivating_move IN (
        'generalize',
        'specialize',
        'decompose',
        'analogize',
        'search_extremal_example',
        'search_counterexample',
        'lift_construction',
        'compress_structure',
        'introduce_invariant',
        'weaken_hypothesis',
        'strengthen_conclusion',
        'change_representation',
        'reduce_to_known_theorem',
        'other'
    )),
    CHECK(intended_role IS NULL OR intended_role IN (
        'witness',
        'counterexample',
        'extremal_example',
        'lower_bound_construction',
        'upper_bound_obstruction',
        'lemma_motivator',
        'formalization_target',
        'heuristic_test_case',
        'asymptotic_family',
        'bridge_to_existing_theorem',
        'future_challenge_submission',
        'other'
    )),
    CHECK(status IN (
        'proposed',
        'under_review',
        'refined',
        'empirically_supported',
        'falsified',
        'rejected',
        'linked_to_formal_claim'
    )),
    CHECK(trust_status IN (
        'informal',
        'empirical_evidence',
        'cited',
        'human_reviewed',
        'formalized_statement_exists',
        'kernel_verified_claim_linked'
    )),
    CHECK(trust_status <> 'kernel_verified_claim_linked' OR verification_layer_id IS NOT NULL)
);
CREATE INDEX IF NOT EXISTS idx_candidate_constructions_dossier ON candidate_constructions(dossier_id);
CREATE INDEX IF NOT EXISTS idx_candidate_constructions_node ON candidate_constructions(related_node_id);
CREATE INDEX IF NOT EXISTS idx_candidate_constructions_verification_layer ON candidate_constructions(verification_layer_id);
CREATE INDEX IF NOT EXISTS idx_candidate_constructions_problem_version ON candidate_constructions(problem_version_id);
CREATE INDEX IF NOT EXISTS idx_candidate_constructions_episode ON candidate_constructions(episode_id);

-- Exposition artifacts (issue #7): human-readable mathematical exposition that
-- lives ALONGSIDE, and explicitly separate from, kernel-verified proof. A
-- serious result needs an explanation layer (what the construction means, why
-- the definitions were chosen, what the key lemma does, what remains
-- unformalized) -- but prose must never be mistaken for proof. Every artifact
-- carries a prose_status making its epistemic weight explicit: 'prose' (raw
-- author narrative), 'reviewed_prose' (a human read it), or 'formalized' (the
-- described claim is backed by a linked formal artifact). None of these is
-- kernel verification. These rows are metadata: no exposition artifact changes
-- an episode outcome, obligation status, fidelity_status, canonical promotion,
-- training eligibility, budget, or benchmark state. An artifact can attach to a
-- problem_version, an episode, a specific obligation, a verified module, a
-- verified helper lemma, and/or a Level 4 research dossier -- every link is
-- optional.
CREATE TABLE IF NOT EXISTS exposition_artifacts (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    obligation_id TEXT REFERENCES episode_obligations(id),
    verified_module_id TEXT REFERENCES episode_verified_modules(id),
    verified_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    dossier_id TEXT REFERENCES research_dossiers(id),
    section_kind TEXT NOT NULL,
    prose_status TEXT NOT NULL DEFAULT 'prose',
    title TEXT,
    content TEXT NOT NULL,
    content_hash TEXT NOT NULL,
    author TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(section_kind IN (
        'problem_summary',
        'formalization_explanation',
        'construction_intuition',
        'key_lemmas',
        'proof_strategy',
        'verified_claim',
        'unverified_bridges',
        'reviewer_notes',
        'next_formalization_targets'
    )),
    CHECK(prose_status IN ('prose', 'reviewed_prose', 'formalized'))
);
CREATE INDEX IF NOT EXISTS idx_exposition_artifacts_episode ON exposition_artifacts(episode_id);
CREATE INDEX IF NOT EXISTS idx_exposition_artifacts_problem_version ON exposition_artifacts(problem_version_id);
CREATE INDEX IF NOT EXISTS idx_exposition_artifacts_dossier ON exposition_artifacts(dossier_id);

-- Semantic statement skeletons and module-aware fidelity notes (issue #6).
-- ADDITIVE and metadata-only: a row here NEVER marks anything proved, never
-- sets problem_versions.fidelity_status, never changes an episode outcome,
-- obligation status, budget, or benchmark state, and never substitutes for the
-- root problem_submit_fidelity_review gate. It records a STRUCTURED reading of
-- what a statement/module/solution actually says (quantifiers, hypotheses,
-- conclusion, helper definitions, construction/final-answer map, a natural-
-- language back-translation) plus fidelity risk flags, so fidelity review can
-- inspect module-level structure (helper defs, bijection/construction claims,
-- final-answer extraction, domain restrictions, prose-only bridges) WITHOUT
-- weakening the existing root-statement gate. All FK links are nullable: a
-- skeleton can describe a bare root statement before any dossier/episode/module
-- exists. review_scope says WHAT was read; risk_flags_json says what looked
-- wrong; neither is a pass/fail verdict. semantic_fingerprint_hash is
-- server-computed over the normalized skeleton content, never client-supplied.
-- The table carries NO status column able to hold kernel evidence -- that
-- structural absence, not a CHECK, is the proof-safety guarantee.
CREATE TABLE IF NOT EXISTS semantic_skeletons (
    id TEXT PRIMARY KEY,
    problem_version_id TEXT REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    root_obligation_id TEXT REFERENCES episode_obligations(id),
    module_id TEXT REFERENCES episode_verified_modules(id),
    module_item_id TEXT REFERENCES episode_verified_module_items(id),
    verified_lemma_id TEXT REFERENCES episode_verified_lemmas(id),
    dossier_id TEXT REFERENCES research_dossiers(id),
    node_id TEXT REFERENCES research_nodes(id),
    root_fidelity_review_id TEXT REFERENCES problem_fidelity_reviews(id),
    review_scope TEXT NOT NULL,
    quantifiers_json TEXT NOT NULL DEFAULT '[]',
    hypotheses_json TEXT NOT NULL DEFAULT '[]',
    conclusion_json TEXT NOT NULL DEFAULT '{}',
    definitions_json TEXT NOT NULL DEFAULT '[]',
    construction_map_json TEXT NOT NULL DEFAULT '[]',
    backtranslation_text TEXT,
    risk_flags_json TEXT NOT NULL DEFAULT '[]',
    review_notes_json TEXT NOT NULL DEFAULT '[]',
    semantic_fingerprint_hash TEXT NOT NULL,
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(review_scope IN (
        'root_statement_only',
        'module_artifact',
        'source_aligned_solution',
        'computational_check_only',
        'structural_proof'
    )),
    -- A module_artifact-scoped skeleton is ABOUT a module, so it must name one.
    CHECK(review_scope <> 'module_artifact' OR module_id IS NOT NULL OR module_item_id IS NOT NULL)
);
CREATE INDEX IF NOT EXISTS idx_semantic_skeletons_problem_version ON semantic_skeletons(problem_version_id);
CREATE INDEX IF NOT EXISTS idx_semantic_skeletons_episode ON semantic_skeletons(episode_id);
CREATE INDEX IF NOT EXISTS idx_semantic_skeletons_module ON semantic_skeletons(module_id);
CREATE INDEX IF NOT EXISTS idx_semantic_skeletons_dossier ON semantic_skeletons(dossier_id);
CREATE INDEX IF NOT EXISTS idx_semantic_skeletons_fingerprint ON semantic_skeletons(semantic_fingerprint_hash);

-- Expert-review artifacts and role-separated research ledger (issue #14): an
-- ADDITIVE, metadata-only ledger of who reviewed what and what they decided.
-- Unlike citation_review_add (which updates external_theorem_claims.claim_status),
-- expert_review_add is a PURE INSERT: a row here NEVER marks anything proved and
-- never mutates episode outcome, obligation status, certification, budget,
-- benchmark, or any other table. reviewer_id is caller-supplied free text, NOT an
-- authenticated principal. A 'domain_expert'/'reviewer' 'approved' decision is
-- human-attested and stays explicitly distinct from Lean kernel verification --
-- the same trust boundary citation_reviews and candidate_constructions already
-- apply. dossier_id is nullable so a review can exist standalone; the
-- (review_target_kind, review_target_id) pair is polymorphic and validated
-- per-kind at the MCP layer. The table carries NO column capable of holding
-- kernel evidence -- that structural absence, not a CHECK, is the proof-safety
-- guarantee. revoked_at soft-retracts a review without deleting the historical
-- row (a rejection must not delete the reviewed artifact; a retraction must not
-- delete the review).
CREATE TABLE IF NOT EXISTS expert_reviews (
    id TEXT PRIMARY KEY,
    dossier_id TEXT REFERENCES research_dossiers(id),
    reviewer_id TEXT NOT NULL,
    reviewer_role TEXT NOT NULL,
    expertise_tags_json TEXT NOT NULL DEFAULT '[]',
    review_target_kind TEXT NOT NULL,
    review_target_id TEXT NOT NULL,
    decision TEXT NOT NULL,
    confidence TEXT,
    notes TEXT,
    requested_changes_json TEXT NOT NULL DEFAULT '[]',
    risk_flags_json TEXT NOT NULL DEFAULT '[]',
    created_at TEXT NOT NULL,
    revoked_at TEXT,
    CHECK(reviewer_role IN (
        'proposer',
        'construction_searcher',
        'formalizer',
        'prover',
        'reviewer',
        'domain_expert',
        'refuter',
        'editor',
        'librarian'
    )),
    CHECK(review_target_kind IN (
        'source_problem',
        'formal_statement',
        'construction_artifact',
        'module_artifact',
        'external_citation',
        'asymptotic_extraction',
        'exposition',
        'full_dossier'
    )),
    CHECK(decision IN (
        'approved',
        'approved_with_changes',
        'needs_changes',
        'rejected',
        'abstain'
    )),
    CHECK(confidence IS NULL OR confidence IN ('low', 'medium', 'high'))
);
CREATE INDEX IF NOT EXISTS idx_expert_reviews_dossier ON expert_reviews(dossier_id);
CREATE INDEX IF NOT EXISTS idx_expert_reviews_target ON expert_reviews(review_target_kind, review_target_id);
CREATE INDEX IF NOT EXISTS idx_expert_reviews_role ON expert_reviews(reviewer_role);

-- Empirical math lab (issue #26): records small-case searches, counterexample
-- searches, construction searches, finite checks, parameter sweeps, and
-- candidate rankings as research EVIDENCE. This is the object layer #8's
-- candidate constructions are generated/tested/ranked/falsified against, and it
-- is bound by one hard rule: empirical evidence is NEVER proof. The table has
-- NO column capable of holding kernel evidence; the strongest trust_status is
-- 'linked_to_formal_target' ("this evidence points at a formalization target"),
-- which is still not a proof. No row here can set or imply kernel_verified,
-- certified, proved, statement_fidelity_approved, benchmark_certified, or
-- training_eligible -- that structural absence, not a CHECK, is the guarantee.
-- Guardrails (enforced at the MCP layer + by this structure): finite/no-
-- counterexample evidence cannot certify an asymptotic or universal theorem; a
-- successful construction search supports but never proves a candidate's
-- claimed properties; a candidate ranking never changes proof authority;
-- external tool output stays empirical unless independently kernel-verified
-- elsewhere. Every link is nullable: a search can exist before any dossier,
-- candidate, episode, or Lean proof. cost_summary_json/runtime_metadata_json
-- are self-reported metadata about the EXTERNAL search run, isolated from
-- LLM-Driven Proof Search Environment's own #38 cost surfaces (never merged into benchmark_run_observe).
CREATE TABLE IF NOT EXISTS empirical_searches (
    id TEXT PRIMARY KEY,
    dossier_id TEXT REFERENCES research_dossiers(id),
    related_node_id TEXT REFERENCES research_nodes(id),
    candidate_construction_id TEXT REFERENCES candidate_constructions(id),
    verification_layer_id TEXT REFERENCES verification_layers(id),
    problem_version_id TEXT REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    search_type TEXT NOT NULL,
    search_space_description TEXT NOT NULL,
    parameters_json TEXT NOT NULL DEFAULT '{}',
    generator_description TEXT,
    checks_json TEXT NOT NULL DEFAULT '[]',
    results_json TEXT NOT NULL DEFAULT '{}',
    counterexamples_json TEXT NOT NULL DEFAULT '[]',
    candidate_construction_ids_json TEXT NOT NULL DEFAULT '[]',
    status TEXT NOT NULL DEFAULT 'planned',
    trust_status TEXT NOT NULL DEFAULT 'unreviewed_empirical',
    runtime_metadata_json TEXT NOT NULL DEFAULT '{}',
    cost_summary_json TEXT NOT NULL DEFAULT '{}',
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(search_type IN (
        'small_case_search',
        'counterexample_search',
        'construction_search',
        'parameter_sweep',
        'finite_model_check',
        'candidate_ranking',
        'random_search',
        'exhaustive_search',
        'symbolic_search',
        'external_tool_run',
        'other'
    )),
    CHECK(status IN (
        'planned',
        'running',
        'completed',
        'completed_with_counterexample',
        'completed_no_counterexample_found',
        'failed',
        'timed_out',
        'rejected',
        'superseded'
    )),
    CHECK(trust_status IN (
        'unreviewed_empirical',
        'reproducible_empirical',
        'human_reviewed_empirical',
        'linked_to_formal_target',
        'rejected_empirical'
    ))
);
CREATE INDEX IF NOT EXISTS idx_empirical_searches_dossier ON empirical_searches(dossier_id);
CREATE INDEX IF NOT EXISTS idx_empirical_searches_candidate ON empirical_searches(candidate_construction_id);
CREATE INDEX IF NOT EXISTS idx_empirical_searches_verification_layer ON empirical_searches(verification_layer_id);
CREATE INDEX IF NOT EXISTS idx_empirical_searches_node ON empirical_searches(related_node_id);

-- Paper/PDF ingestion (issue #27): turns a paper, manuscript, model-written
-- proof sketch, or human exposition into a REVIEWABLE research workspace inside
-- a dossier. LLM-Driven Proof Search Environment does no OCR/LLM extraction itself (no inference code lives
-- here) -- the host performs extraction and records the structured result,
-- which is UNTRUSTED by construction. Ingestion is not verification: an
-- ingested_documents row and its extracted ingested_document_nodes have NO
-- column able to hold kernel evidence. extraction_trust_status tops out at
-- 'human_reviewed_extraction'/'linked_to_dossier_artifact' -- still not proof.
-- No ingested artifact can mark anything kernel_verified, certified, proved,
-- statement_fidelity_approved, benchmark_certified, or training_eligible; that
-- structural absence, not a CHECK, is the guarantee. Extracted theorem text is
-- NOT statement-fidelity approval, an extracted citation is NOT citation
-- validation, and an extracted assumption is NOT an accepted assumption -- each
-- is a candidate that must go through the existing fidelity/citation/review
-- paths (or Lean) to gain any authority. dossier_id is nullable: a document can
-- be ingested before it is attached to a dossier.
CREATE TABLE IF NOT EXISTS ingested_documents (
    id TEXT PRIMARY KEY,
    dossier_id TEXT REFERENCES research_dossiers(id),
    title TEXT NOT NULL,
    source_kind TEXT NOT NULL,
    source_ref TEXT,
    source_content_hash TEXT,
    ingest_status TEXT NOT NULL DEFAULT 'planned',
    extraction_trust_status TEXT NOT NULL DEFAULT 'unreviewed_extraction',
    notes TEXT,
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(source_kind IN ('pdf', 'manuscript', 'proof_sketch', 'exposition', 'webpage', 'other')),
    CHECK(ingest_status IN ('planned', 'ingesting', 'ingested', 'failed', 'superseded')),
    CHECK(extraction_trust_status IN (
        'unreviewed_extraction',
        'machine_extracted',
        'human_reviewed_extraction',
        'rejected_extraction',
        'linked_to_dossier_artifact'
    ))
);

-- One extracted node from an ingested document, in document order. Every field
-- is untrusted extraction. formalization_status can never reach a proved/
-- verified value here -- 'prose_only' / 'formalization_pending' /
-- 'formalization_target_linked' only; kernel verification lives in the
-- episode/canonical tables alone. citation_status/review_status likewise never
-- confer validation or fidelity approval. source_span traces the node back to
-- the paper text so a reviewer can check it.
CREATE TABLE IF NOT EXISTS ingested_document_nodes (
    id TEXT PRIMARY KEY,
    document_id TEXT NOT NULL REFERENCES ingested_documents(id),
    dossier_id TEXT REFERENCES research_dossiers(id),
    node_order INTEGER NOT NULL,
    node_kind TEXT NOT NULL,
    natural_language_text TEXT NOT NULL,
    -- Required (issue #27 acceptance: source-span tracking). Every extracted
    -- node must be traceable back to the paper text; the MCP handler also
    -- rejects a blank span.
    source_span TEXT NOT NULL,
    confidence TEXT,
    formalization_status TEXT NOT NULL DEFAULT 'prose_only',
    citation_status TEXT NOT NULL DEFAULT 'uncited',
    review_status TEXT NOT NULL DEFAULT 'unreviewed_extraction',
    risk_flags_json TEXT NOT NULL DEFAULT '[]',
    -- Forward links set by paper_ingest_link_node when a node is promoted
    -- through a real path. A link records provenance only — it never grants the
    -- node proof/kernel authority (the linked artifact keeps its own trust).
    linked_external_reference_id TEXT REFERENCES external_references(id),
    linked_external_theorem_claim_id TEXT REFERENCES external_theorem_claims(id),
    linked_research_node_id TEXT REFERENCES research_nodes(id),
    linked_formalization_plan_item_id TEXT REFERENCES formalization_plan_items(id),
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    UNIQUE(document_id, node_order),
    CHECK(node_kind IN (
        'abstract', 'main_theorem', 'definition', 'proposition', 'lemma',
        'proof_step', 'construction', 'remark', 'appendix_fact', 'reference', 'open_gap'
    )),
    CHECK(formalization_status IN ('prose_only', 'formalization_pending', 'formalization_target_linked')),
    CHECK(citation_status IN ('uncited', 'citation_recorded')),
    CHECK(confidence IS NULL OR confidence IN ('low', 'medium', 'high')),
    CHECK(review_status IN (
        'unreviewed_extraction',
        'machine_extracted',
        'human_reviewed_extraction',
        'rejected_extraction',
        'linked_to_dossier_artifact'
    )),
    -- A "backed" status must be backed by a real forward link (issue #27, PR #58
    -- review, blocker #2). These three terminal states are reachable ONLY via
    -- paper_ingest_link_node, which sets the matching FK in the same UPDATE; a
    -- node can never be *labeled* citation_recorded / formalization_target_linked
    -- / linked_to_dossier_artifact while pointing at nothing. Structural, not a
    -- handler courtesy: even a future bug or a raw INSERT cannot decouple the
    -- label from the artifact it claims to be tied to. A database that created
    -- this table before these three CHECKs existed is rebuilt into them by
    -- migrate_ingested_document_nodes_backed_status_checks (keep the two
    -- definitions in sync).
    CHECK(citation_status <> 'citation_recorded'
          OR linked_external_reference_id IS NOT NULL
          OR linked_external_theorem_claim_id IS NOT NULL),
    CHECK(formalization_status <> 'formalization_target_linked'
          OR linked_research_node_id IS NOT NULL
          OR linked_formalization_plan_item_id IS NOT NULL),
    CHECK(review_status <> 'linked_to_dossier_artifact'
          OR linked_external_reference_id IS NOT NULL
          OR linked_external_theorem_claim_id IS NOT NULL
          OR linked_research_node_id IS NOT NULL
          OR linked_formalization_plan_item_id IS NOT NULL)
);
CREATE INDEX IF NOT EXISTS idx_ingested_documents_dossier ON ingested_documents(dossier_id);
CREATE INDEX IF NOT EXISTS idx_ingested_document_nodes_document ON ingested_document_nodes(document_id);
CREATE INDEX IF NOT EXISTS idx_ingested_document_nodes_dossier ON ingested_document_nodes(dossier_id);

-- Run envelopes (issues #34 core concept + #38 cost-surface splitting): a
-- run envelope separates WHO/WHAT/WHY around a set of episodes from the
-- episodes themselves -- host identity, run mode (a plain dev/exploratory
-- episode vs. a frozen benchmark run like PutnamBench), and host-side cost
-- accounting LLM-Driven Proof Search Environment itself cannot observe (MCP-visible cost_micros/budget
-- ledger fields only ever reflect this environment's OWN bookkeeping --
-- Lean invocation time and internal accounting -- never the total cost of
-- running the external host/model that's calling these tools; see
-- readme_first's cost_boundary section). Purely descriptive metadata: a run
-- envelope's mode/cost fields never affect proof status, and episodes.run_id
-- (below) is never validated with a DB-level foreign key -- see the comment
-- on run_envelope_attach_episode for why.
CREATE TABLE IF NOT EXISTS run_envelopes (
    id TEXT PRIMARY KEY,
    mode TEXT NOT NULL,
    host_name TEXT,
    host_model TEXT,
    benchmark_suite_name TEXT,
    host_side_cost_micros INTEGER,
    host_cost_confidence TEXT NOT NULL,
    notes TEXT,
    -- Issue #46: head of the append-only host-side cost observation chain
    -- (also added to pre-existing DBs by migrate_add_current_cost_observation_column).
    current_cost_observation_id TEXT,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(mode IN ('development', 'evaluation', 'benchmark', 'private_audit', 'public_report')),
    CHECK(host_cost_confidence IN ('exact_provider_receipt', 'exact_local_meter', 'estimated', 'attested', 'unknown'))
);

-- Append-only host-side cost observations (issue #46): a run envelope's
-- host-side cost figure is often a CORRECTION of an earlier estimate (an
-- estimate replaced by a provider receipt, etc.). Overwriting host_side_cost_
-- micros in place destroys the audit trail. Instead every value is recorded as
-- an immutable observation that supersedes (points back to) the one it
-- replaces; run_envelopes.host_side_cost_micros/host_cost_confidence remain as
-- a convenience mirror of the CURRENT observation (run_envelopes.current_cost_
-- observation_id, added by migration). Same confidence tiers as run_envelopes;
-- purely descriptive host metadata, never proof authority, never a fabricated
-- exact figure (a NULL cost stays NULL, its confidence still recorded).
CREATE TABLE IF NOT EXISTS run_envelope_cost_observations (
    id TEXT PRIMARY KEY,
    run_envelope_id TEXT NOT NULL REFERENCES run_envelopes(id),
    host_side_cost_micros INTEGER,
    host_cost_confidence TEXT NOT NULL,
    source TEXT NOT NULL,
    notes TEXT,
    supersedes_observation_id TEXT REFERENCES run_envelope_cost_observations(id),
    created_at TEXT NOT NULL,
    CHECK(host_cost_confidence IN ('exact_provider_receipt', 'exact_local_meter', 'estimated', 'attested', 'unknown'))
);
CREATE INDEX IF NOT EXISTS idx_cost_observations_envelope ON run_envelope_cost_observations(run_envelope_id);

-- PutnamBench benchmark schema (issues #29, #30, designed together since
-- benchmark_results references benchmark_problems and benchmark_runs
-- references benchmark_suites -- one interlocking schema, not two
-- independent ones). #30 ships all four tables plus manual suite/problem
-- registration and the run/result tools; #29's real Lean-file-parsing
-- importer (populating benchmark_problems automatically from a real
-- PutnamBench checkout) is still unimplemented -- see the design note on
-- issue #29.
-- trusted_canonical_source (issue #38's fidelity-basis policy): an honest,
-- self-declared trust assertion the CALLER makes when registering a suite —
-- LLM-Driven Proof Search Environment never independently verifies it, same idiom as
-- unsafe_dev_attestation/host_cost_confidence elsewhere. Defaults to 0
-- (untrusted) so an arbitrary custom suite can never silently gain the
-- "statement-hash match alone is sufficient fidelity evidence" treatment
-- meant only for a real, externally-curated corpus like PutnamBench. See
-- migrate_add_trusted_canonical_source_column for the full rationale.
CREATE TABLE IF NOT EXISTS benchmark_suites (
    id TEXT PRIMARY KEY,
    name TEXT NOT NULL UNIQUE,
    upstream_url TEXT,
    upstream_commit TEXT,
    language TEXT NOT NULL,
    trusted_canonical_source INTEGER NOT NULL DEFAULT 0,
    imported_at TEXT NOT NULL
);

-- Issue #65: the trust flag above is a load-bearing fidelity-basis input
-- (benchmark_result_record accepts a hash match against a trusted suite as
-- sufficient fidelity evidence), so changing it after creation must leave an
-- append-only audit trail — who asserted the change, from what value to what
-- value, and why. benchmark_suite_set_trust writes one row here per change
-- and never deletes; the current flag on benchmark_suites is just the fold of
-- this history.
CREATE TABLE IF NOT EXISTS benchmark_suite_trust_reviews (
    id TEXT PRIMARY KEY,
    suite_id TEXT NOT NULL REFERENCES benchmark_suites(id),
    previous_value INTEGER NOT NULL,
    new_value INTEGER NOT NULL,
    approver_id TEXT NOT NULL,
    notes TEXT,
    created_at TEXT NOT NULL,
    CHECK(previous_value IN (0, 1)),
    CHECK(new_value IN (0, 1))
);
CREATE INDEX IF NOT EXISTS idx_benchmark_suite_trust_reviews_suite ON benchmark_suite_trust_reviews(suite_id);

-- root_statement_hash is server-computed (canonical_hash of
-- root_formal_statement), never trusted from the client -- same "never
-- trust a client-supplied hash for something the server can independently
-- verify" principle problem_create already applies to its own root
-- statement hash.
CREATE TABLE IF NOT EXISTS benchmark_problems (
    id TEXT PRIMARY KEY,
    suite_id TEXT NOT NULL REFERENCES benchmark_suites(id),
    upstream_problem_id TEXT NOT NULL,
    theorem_name TEXT NOT NULL,
    source_file_path TEXT,
    root_formal_statement TEXT NOT NULL,
    root_statement_hash TEXT NOT NULL,
    import_manifest_json TEXT NOT NULL,
    context_hash TEXT,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    -- The exact text a runner actually submits to problem_create/SubmitModule
    -- for this problem, when it differs from root_formal_statement (e.g.
    -- PutnamBench's named-binder declaration syntax vs. the Pi-type LLM-Driven Proof Search Environment's
    -- model requires as a single self-contained type expression). NULL when
    -- root_formal_statement is already directly usable as-is. See
    -- migrate_add_prover_ready_statement_columns for the full rationale.
    prover_ready_statement TEXT,
    prover_ready_statement_hash TEXT,
    -- Issue #12: goal class distinguishes a finite/exact target from a
    -- parameterized family, an inductive growth bound, or a genuinely
    -- asymptotic statement. brute_force_admissible records whether finite
    -- enumeration is admissible evidence at all — an asymptotic goal is NOT
    -- decidable by finite brute force, so it is forced to 0. Descriptive
    -- benchmark metadata; neither column is proof authority. Added to
    -- pre-existing DBs by migrate_add_benchmark_goal_class_columns (which cannot
    -- re-add the cross-column CHECK — the MCP handler enforces it for those).
    goal_class TEXT NOT NULL DEFAULT 'finite_exact',
    brute_force_admissible INTEGER NOT NULL DEFAULT 1,
    UNIQUE(suite_id, upstream_problem_id),
    CHECK(status IN ('imported', 'skipped_ambiguous', 'deprecated')),
    CHECK(goal_class IN ('finite_exact', 'parameterized_family', 'inductive_growth_bound', 'asymptotic')),
    CHECK(brute_force_admissible IN (0, 1)),
    CHECK(goal_class <> 'asymptotic' OR brute_force_admissible = 0)
);

-- run_envelope_id links to the host/model/mode/cost tracking issues
-- #34/#38 already added -- benchmark_runs does NOT duplicate host_name/
-- host_model/mode fields, only what's genuinely benchmark-specific.
-- lean_version/mathlib_commit are never accepted from the client (see
-- benchmark_run_create) -- they're read from the server's OWN detected
-- environment, the only trustworthy source, exactly like
-- RealLeanGateway/lean_environment already is everywhere else in this repo.
CREATE TABLE IF NOT EXISTS benchmark_runs (
    id TEXT PRIMARY KEY,
    suite_id TEXT NOT NULL REFERENCES benchmark_suites(id),
    run_envelope_id TEXT REFERENCES run_envelopes(id),
    proofsearch_commit TEXT,
    lean_version TEXT,
    mathlib_commit TEXT,
    solve_mode TEXT NOT NULL,
    allowed_tools_json TEXT NOT NULL,
    attempt_budget INTEGER NOT NULL,
    wall_clock_budget_ms INTEGER,
    lean_timeout_ms INTEGER,
    created_at TEXT NOT NULL,
    CHECK(solve_mode IN ('solve_only', 'submit_module_allowed', 'submit_module_plus_draft_planning', 'submit_module_plus_librarian'))
);

-- One row per (run, problem) -- UPSERT, not insert-only, since a live
-- benchmark run naturally updates a result across pass@k retries before it
-- finalizes. episode_id, when given, is cross-checked against that
-- episode's ACTUAL recorded outcome (see benchmark_result_record) --
-- issue #36's "a proof attempt that bypasses the ledger is not part of
-- LLM-Driven Proof Search Environment evidence" principle applied concretely: a benchmark result cannot
-- claim an outcome the referenced episode didn't actually reach.
CREATE TABLE IF NOT EXISTS benchmark_results (
    id TEXT PRIMARY KEY,
    run_id TEXT NOT NULL REFERENCES benchmark_runs(id),
    benchmark_problem_id TEXT NOT NULL REFERENCES benchmark_problems(id),
    problem_version_id TEXT REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    status TEXT NOT NULL,
    outcome TEXT,
    pass_at INTEGER,
    attempts_used INTEGER NOT NULL,
    time_to_first_success_ms INTEGER,
    cost_micros INTEGER,
    final_diagnostic_category TEXT,
    proof_artifact_hash TEXT,
    trajectory_export_hash TEXT,
    replay_status TEXT,
    -- benchmark_fidelity_basis (issue #38): what evidence, if any, backs a
    -- kernel_verified/certified claim's STATEMENT fidelity specifically --
    -- deliberately distinct from problem_versions.fidelity_status (whether
    -- the formal statement faithfully represents the informal problem).
    -- 'canonical_statement_hash_match': the episode's problem_version hash
    -- matches this benchmark_problem's registered hash AND the suite is
    -- trusted_canonical_source -- sufficient fidelity evidence for a real,
    -- externally-curated corpus like PutnamBench without requiring a
    -- separate independent review.
    -- 'problem_fidelity_verified': the backing problem_version's own
    -- fidelity_status is 'verified' (a real problem_submit_fidelity_review
    -- landed), independent of suite trust.
    -- 'none': no proof claim is being made (a non-kernel_verified/certified
    -- status has no fidelity basis to report).
    -- 'mismatch': reserved for defensive completeness; a real hash mismatch
    -- is rejected outright by benchmark_result_record before a row is ever
    -- written, so this value is never actually persisted today.
    benchmark_fidelity_basis TEXT,
    -- Issue #76: structured formalization-gap taxonomy for failed/gave-up
    -- results — a JSON array of category slugs (validated at the MCP layer
    -- against a fixed vocabulary). Additive metadata for reporting only:
    -- never proof authority, never affects status/score/eligibility.
    gap_categories_json TEXT,
    -- Issue #92: kit-aware reporting metadata (never proof authority) —
    -- fully qualified kit lemma names the attempt used (JSON array), and the
    -- specific kit route step a failed result was missing (free text).
    kit_lemmas_used_json TEXT,
    missing_route_step TEXT,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    UNIQUE(run_id, benchmark_problem_id),
    CHECK(status IN ('kernel_verified', 'certified', 'failed', 'timeout', 'infra_error', 'formalization_gap', 'skipped')),
    CHECK(benchmark_fidelity_basis IS NULL OR benchmark_fidelity_basis IN ('canonical_statement_hash_match', 'problem_fidelity_verified', 'none', 'mismatch'))
);

CREATE TABLE IF NOT EXISTS action_requests (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    episode_revision INTEGER NOT NULL,
    request_sequence_number INTEGER NOT NULL,
    role TEXT NOT NULL,
    action_schema_id TEXT,
    action_schema_version TEXT,
    environment_version TEXT,
    target_obligation_id TEXT REFERENCES episode_obligations(id),
    observation_json TEXT,
    observation_hash TEXT,
    state_hash_before TEXT,
    expected_response_type TEXT,
    allowed_action_variants_json TEXT,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    expiration_at TEXT,
    claimed_at TEXT,
    fulfilled_at TEXT,
    fulfilled_attempt_id TEXT,
    superseding_request_id TEXT,
    cancellation_reason TEXT,
    CHECK(status IN ('pending', 'claimed', 'fulfilled', 'expired', 'cancelled'))
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_active_request_per_revision
ON action_requests(episode_id, episode_revision)
WHERE status IN ('pending', 'claimed');

CREATE TABLE IF NOT EXISTS action_attempts (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    action_request_id TEXT NOT NULL REFERENCES action_requests(id),
    idempotency_key TEXT NOT NULL,
    expected_revision INTEGER NOT NULL,
    claim_token TEXT NOT NULL,
    submitted_action_json TEXT,
    raw_external_response BLOB,
    raw_external_response_content_type TEXT,
    raw_external_response_encoding TEXT,
    raw_external_response_byte_length INTEGER,
    raw_external_response_sha256 TEXT,
    status TEXT NOT NULL,
    claimed_at TEXT NOT NULL,
    claim_expiration TEXT,
    execution_started_at TEXT,
    execution_completed_at TEXT,
    preflight_result_json TEXT,
    lean_invocation_id TEXT,
    lean_result_json TEXT,
    -- issue #38's storage-bytes metric: the real byte length (Rust
    -- String::len(), NOT SQLite's LENGTH() which counts UTF-8 CHARACTERS,
    -- undercounting multi-byte math notation like ∀/≥/⟨⟩) of
    -- lean_result_json as actually persisted, computed once at write time
    -- rather than recomputed per read. NULL exactly when lean_result_json
    -- is NULL (no verification ran for this attempt).
    lean_result_bytes INTEGER,
    commit_result_json TEXT,
    failure_reason TEXT,
    CHECK(status IN ('claimed', 'preflight_rejected', 'executing', 'verified', 'rejected', 'committed', 'abandoned', 'expired', 'infrastructure_failed'))
);

-- issue #38's MCP-side/storage-export observability: a generic, per-call
-- timing/size log populated for EVERY MCP tool call (success or failure —
-- an honest total of real handler time spent, not just successful calls),
-- with best-effort correlation IDs duck-typed out of the call's own args
-- (episode_id/run_id/run_envelope_id, whichever the specific tool happens to
-- accept) so benchmark_run_observe can aggregate mcp_handler_wall_time_ms
-- for a run's episodes/run_id/run_envelope without any per-tool special
-- casing. response_bytes is the real byte length of the returned content —
-- used for storage_export_bytes when tool_name is proof_export/
-- trajectory_export, otherwise just a general diagnostic. No monetary
-- figure is ever derived from this table: mcp_side_cost_micros/
-- storage_export_cost_micros stay null until a real pricing profile exists.
CREATE TABLE IF NOT EXISTS mcp_call_metrics (
    id TEXT PRIMARY KEY,
    tool_name TEXT NOT NULL,
    episode_id TEXT,
    run_id TEXT,
    run_envelope_id TEXT,
    wall_time_ms INTEGER NOT NULL,
    response_bytes INTEGER,
    is_error INTEGER NOT NULL,
    created_at TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS idx_mcp_call_metrics_episode_id ON mcp_call_metrics(episode_id);
CREATE INDEX IF NOT EXISTS idx_mcp_call_metrics_run_id ON mcp_call_metrics(run_id);
CREATE INDEX IF NOT EXISTS idx_mcp_call_metrics_run_envelope_id ON mcp_call_metrics(run_envelope_id);
CREATE INDEX IF NOT EXISTS idx_mcp_call_metrics_tool_name ON mcp_call_metrics(tool_name);

CREATE UNIQUE INDEX IF NOT EXISTS idx_attempt_idempotency
ON action_attempts(episode_id, idempotency_key);

-- Partial index for active attempts
CREATE UNIQUE INDEX IF NOT EXISTS idx_one_active_attempt_per_request
ON action_attempts(action_request_id)
WHERE status IN ('claimed', 'executing', 'verified');

CREATE TABLE IF NOT EXISTS model_call_leases (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    action_attempt_id TEXT NOT NULL REFERENCES action_attempts(id),
    model_descriptor_json TEXT NOT NULL,
    reserved_cost_micros INTEGER NOT NULL,
    actual_cost_micros INTEGER,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    settled_at TEXT,
    CHECK(status IN ('reserved', 'settled', 'voided'))
);

CREATE TABLE IF NOT EXISTS trajectory_events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    event_sequence_number INTEGER NOT NULL,
    event_type TEXT NOT NULL,
    event_hash TEXT NOT NULL,
    previous_event_hash TEXT NOT NULL,
    state_hash_before TEXT NOT NULL,
    state_hash_after TEXT NOT NULL,
    lean_environment_hash TEXT NOT NULL,
    payload_json TEXT NOT NULL,
    payload_hash TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(episode_id, event_sequence_number),
    UNIQUE(episode_id, event_hash)
);

-- Challenge / task / scoring substrate (issue #53): channels AI-generated
-- mathematical material into small, bounded, typed, scored, reviewable tasks
-- instead of giant opaque proof dumps. A dossier defines a challenge; a
-- challenge defines bounded tasks; a task accepts submissions; a submission is
-- validated, scored, and reviewed; accepted work links back to candidate
-- constructions / empirical results / verification layers, and reusable method
-- knowledge is distilled into strategy artifacts.
--
-- TRUST BOUNDARY (same discipline as every Level-4 table): none of these tables
-- has a column that can hold kernel evidence. A scored submission is not a
-- proof; a validated empirical result is not a proof; a human-reviewed
-- submission is not a proof; a distilled strategy is not a proof. Only Lean /
-- kernel verification creates kernel-verified proof authority. Submission
-- status (validated / scored / accepted / ...) and review decisions are
-- research bookkeeping and never mutate episode outcome, obligation status,
-- fidelity status, benchmark results, or canonical lemma authority. A rejected
-- or superseded submission stays visible (never deleted). Links to a
-- kernel-verified verification_layer / candidate_construction record provenance
-- only — they never confer proof authority on the submission itself.
CREATE TABLE IF NOT EXISTS research_challenges (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    problem_version_id TEXT REFERENCES problem_versions(id),
    episode_id TEXT REFERENCES episodes(id),
    title TEXT NOT NULL,
    description TEXT,
    status TEXT NOT NULL DEFAULT 'open',
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(status IN ('open', 'closed', 'archived', 'superseded'))
);

-- A validation protocol: HOW a task's submissions are checked. Reusable and
-- optional; a task may point at one. The protocol describes a check; running it
-- (or a human running it) is what validates a submission — the protocol row is
-- never itself proof.
CREATE TABLE IF NOT EXISTS validation_protocols (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    challenge_id TEXT REFERENCES research_challenges(id),
    name TEXT NOT NULL,
    validation_method TEXT NOT NULL,
    description TEXT,
    protocol_json TEXT NOT NULL DEFAULT '{}',
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(validation_method IN (
        'reproducible_script',
        'property_check',
        'independent_recompute',
        'finite_case_check',
        'symbolic_check',
        'manual_review',
        'external_tool',
        'other'
    ))
);

-- A bounded task under a challenge. task_type is the shape of contribution
-- requested; bounds_json states the explicit bound that keeps it small and
-- reviewable. status open/closed/superseded — a superseded task stays visible.
CREATE TABLE IF NOT EXISTS research_tasks (
    id TEXT PRIMARY KEY,
    challenge_id TEXT NOT NULL REFERENCES research_challenges(id),
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    validation_protocol_id TEXT REFERENCES validation_protocols(id),
    task_type TEXT NOT NULL,
    title TEXT NOT NULL,
    description TEXT,
    bounds_json TEXT NOT NULL DEFAULT '{}',
    success_criteria TEXT,
    status TEXT NOT NULL DEFAULT 'open',
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(task_type IN (
        'find_candidate_object',
        'improve_bound',
        'find_counterexample',
        'classify_small_cases',
        'produce_witness',
        'minimize_example',
        'maximize_parameter',
        'verify_property',
        'compress_strategy',
        'distill_method',
        'formalize_claim'
    )),
    CHECK(status IN ('open', 'closed', 'superseded'))
);

-- A submission to a task. content_json is the untrusted contribution payload.
-- status walks submitted -> validated/validation_failed -> scored ->
-- human_reviewed -> accepted/rejected/superseded/merged_into_dossier. It links
-- to a candidate construction / empirical result / verification layer as
-- PROVENANCE only. is_proof is structurally false: no column here can hold
-- kernel evidence, and the linked artifacts keep their own independent trust.
CREATE TABLE IF NOT EXISTS research_task_submissions (
    id TEXT PRIMARY KEY,
    task_id TEXT NOT NULL REFERENCES research_tasks(id),
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    submitted_by TEXT NOT NULL,
    content_json TEXT NOT NULL DEFAULT '{}',
    notes TEXT,
    status TEXT NOT NULL DEFAULT 'submitted',
    linked_candidate_construction_id TEXT REFERENCES candidate_constructions(id),
    linked_empirical_result_id TEXT REFERENCES empirical_searches(id),
    linked_verification_layer_id TEXT REFERENCES verification_layers(id),
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(status IN (
        'submitted',
        'validation_failed',
        'validated',
        'scored',
        'human_reviewed',
        'accepted',
        'rejected',
        'superseded',
        'merged_into_dossier'
    ))
);

-- A score attached to a submission. Descriptive measurement, never proof:
-- score_value/units/rule record what was measured and how; validation_method
-- records how it was checked; the linked artifacts are provenance. cost_summary_id
-- ties the score to a real cost observation when one exists.
CREATE TABLE IF NOT EXISTS scoring_results (
    id TEXT PRIMARY KEY,
    submission_id TEXT NOT NULL REFERENCES research_task_submissions(id),
    score_value REAL,
    score_units TEXT,
    scoring_rule TEXT NOT NULL,
    validation_method TEXT,
    reproducibility_notes TEXT,
    novelty_notes TEXT,
    cost_summary_id TEXT REFERENCES run_envelope_cost_observations(id),
    linked_candidate_construction_id TEXT REFERENCES candidate_constructions(id),
    linked_empirical_result_id TEXT REFERENCES empirical_searches(id),
    linked_verification_layer_id TEXT REFERENCES verification_layers(id),
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL
);

-- A human review of a submission. Human review is distinct from kernel
-- verification. A rejected review keeps the submission visible.
CREATE TABLE IF NOT EXISTS review_results (
    id TEXT PRIMARY KEY,
    submission_id TEXT NOT NULL REFERENCES research_task_submissions(id),
    reviewer_id TEXT NOT NULL,
    decision TEXT NOT NULL,
    review_status TEXT NOT NULL DEFAULT 'human_reviewed',
    notes TEXT,
    created_at TEXT NOT NULL,
    CHECK(decision IN ('accepted', 'rejected', 'needs_changes', 'superseded')),
    CHECK(review_status IN ('human_reviewed', 'machine_prechecked'))
);

-- Reusable distilled strategy knowledge: compressed search experience (cheat
-- sheets, heuristics, counterexample patterns, construction recipes, ...). A
-- distilled strategy is NOT a proof; trust_status tops out at human_reviewed.
CREATE TABLE IF NOT EXISTS distilled_strategy_artifacts (
    id TEXT PRIMARY KEY,
    dossier_id TEXT NOT NULL REFERENCES research_dossiers(id),
    challenge_id TEXT REFERENCES research_challenges(id),
    task_id TEXT REFERENCES research_tasks(id),
    submission_id TEXT REFERENCES research_task_submissions(id),
    artifact_type TEXT NOT NULL,
    title TEXT NOT NULL,
    content TEXT NOT NULL,
    content_hash TEXT NOT NULL,
    tags_json TEXT NOT NULL DEFAULT '[]',
    trust_status TEXT NOT NULL DEFAULT 'informal',
    created_by TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(artifact_type IN (
        'strategy_cheat_sheet',
        'failed_attempt_summary',
        'heuristic_rule',
        'counterexample_pattern',
        'construction_recipe',
        'formalization_hint',
        'review_checklist'
    )),
    CHECK(trust_status IN ('informal', 'human_reviewed', 'deprecated', 'superseded'))
);

CREATE INDEX IF NOT EXISTS idx_research_challenges_dossier ON research_challenges(dossier_id);
CREATE INDEX IF NOT EXISTS idx_research_tasks_challenge ON research_tasks(challenge_id);
CREATE INDEX IF NOT EXISTS idx_research_task_submissions_task ON research_task_submissions(task_id);
CREATE INDEX IF NOT EXISTS idx_scoring_results_submission ON scoring_results(submission_id);
CREATE INDEX IF NOT EXISTS idx_review_results_submission ON review_results(submission_id);
CREATE INDEX IF NOT EXISTS idx_validation_protocols_dossier ON validation_protocols(dossier_id);
CREATE INDEX IF NOT EXISTS idx_distilled_strategy_artifacts_dossier ON distilled_strategy_artifacts(dossier_id);

-- Interactive proof-session persistence (issue #160, part of the Pantograph-
-- style interaction epic #158): first-class storage for tactic-by-tactic
-- proof search built on top of #159's InteractiveProofGateway trait
-- (`crate::lean::interactive`) and #162's canonical ProofStateObservation /
-- ProofStateDiagnostic model (`crate::lean::observation`). Without this,
-- an interactive backend would be another untracked scratchpad -- exactly the
-- negative-space loss this project exists to fix.
--
-- TRUST BOUNDARY (same rule #159/#162 already state, restated here because it
-- is this table group's entire reason for existing): every row below is
-- SEARCH EVIDENCE ONLY. No row here, and no column combination across them,
-- can mark an `episode_obligations` row proved -- that structural absence is
-- the guarantee, not a CHECK. The ONLY path from an interactive session to a
-- proved obligation is: reconstruct a script -> resubmit it through the
-- EXISTING Solve/SubmitModule -> action_attempts kernel-verification path
-- (unchanged by this migration) -> link the resulting action_attempts row
-- back onto `interactive_proof_reconstructed_scripts.verified_attempt_id`.
-- That link column (and `verification_outcome` beside it) is nullable and is
-- NEVER populated at INSERT time by this schema -- see that table's own doc.
--
-- Judgment call -- `interactive_proof_diagnostics` (issue #160 lists this as
-- a proposed 5th table without giving it its own column list): folded into
-- `interactive_proof_steps` as `diagnostic_json` + `diagnostics_hash` rather
-- than kept as a separate table. Reasons: (1) #162's `ProofStateDiagnostic`
-- already serializes losslessly to one JSON value (it wraps `LeanDiagnostic`
-- wholesale), so a separate table would just be this same JSON blob split
-- across columns with no query pattern that needs it split; (2) the existing
-- schema already has this exact convention -- `episode_proposal_attempts` /
-- `episode_review_proposals` etc. carry a `diagnostic_json TEXT` column
-- directly rather than a child table, and this group follows the same
-- pattern rather than inventing a second one; (3) a diagnostic is 1:1 with
-- the failed step that produced it (never shared across steps), so a child
-- table would carry a redundant `step_id` unique key and buy nothing a
-- nullable column pair doesn't already give for free. `diagnostics_hash` is
-- `crate::hashing::canonical_hash` over the same content
-- `crate::lean::observation::hash_diagnostic` would compute, so two
-- structurally-identical diagnostics remain comparable without a join.
CREATE TABLE IF NOT EXISTS interactive_proof_sessions (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
    obligation_id TEXT NOT NULL REFERENCES episode_obligations(id),
    backend_kind TEXT NOT NULL,
    backend_version TEXT,
    import_manifest_hash TEXT,
    environment_hash TEXT,
    state TEXT NOT NULL DEFAULT 'open',
    -- root_node_id / selected_final_node_id reference interactive_proof_nodes
    -- (defined below this table): SQLite resolves a REFERENCES target by name
    -- at DML time, not at CREATE TABLE time, so this forward reference (and
    -- interactive_proof_nodes.session_id referencing back up to this table)
    -- is safe. In practice a session row is inserted first with both NULL,
    -- then updated once its root node (and later, its selected final node)
    -- exist -- the same "create now, link later" shape
    -- `problem_versions.root_obligation_id` already uses.
    root_node_id TEXT REFERENCES interactive_proof_nodes(id),
    selected_final_node_id TEXT REFERENCES interactive_proof_nodes(id),
    reconstructed_script_hash TEXT,
    created_at TEXT NOT NULL,
    closed_at TEXT,
    -- Issue #161: proof_session_close accepts a finer-grained reason
    -- ('closed' | 'abandoned' | 'superseded') than the two-value `state`
    -- column above models. Rather than widen `state` itself (which
    -- `root_node_id`/`selected_final_node_id` writes and #160's own tests
    -- already key off 'open'/'closed'), this column records WHY a closed
    -- session was closed while `state` stays exactly the #160 vocabulary.
    -- NULL while open; non-NULL only once closed. Legacy DBs created before
    -- this column existed are backfilled by migrate_add_interactive_session_close_reason_column.
    close_reason TEXT,
    CHECK(state IN ('open', 'closed')),
    CHECK((state = 'open' AND closed_at IS NULL) OR (state = 'closed' AND closed_at IS NOT NULL)),
    CHECK(close_reason IS NULL OR (state = 'closed' AND close_reason IN ('closed', 'abandoned', 'superseded')))
);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_sessions_episode ON interactive_proof_sessions(episode_id);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_sessions_obligation ON interactive_proof_sessions(obligation_id);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_sessions_problem_version ON interactive_proof_sessions(problem_version_id);

-- One row per proof-state node in a session's tree (#159's
-- ProofStateSnapshot / #162's ProofStateObservation, persisted). Nodes are
-- APPEND-ONLY: a session can hold several sibling nodes reached from the same
-- parent by different tactics (branching from `apply_tactic`'s explicit
-- `parent_node` argument), and nothing in this schema ever deletes or
-- overwrites an existing node row -- see `interactive_proof_steps` for the
-- tactic edges that connect them.
CREATE TABLE IF NOT EXISTS interactive_proof_nodes (
    id TEXT PRIMARY KEY,
    session_id TEXT NOT NULL REFERENCES interactive_proof_sessions(id),
    parent_node_id TEXT REFERENCES interactive_proof_nodes(id),
    depth INTEGER NOT NULL,
    node_kind TEXT NOT NULL,
    -- #162 ProofStateHash.full_state_hash for this node.
    proof_state_hash TEXT NOT NULL,
    -- Canonical JSON serialization of #162's Vec<ProofGoal> (each entry
    -- already bundles its own target rendering AND local_context). Issue
    -- #160 suggests separate local_context_json/target_json columns; those
    -- are deliberately folded into this single goals_json column instead --
    -- splitting them out would only be lossless for a single-goal node, and
    -- would either duplicate goals_json's content or silently keep just one
    -- goal's context/target for a multi-goal node. selected_goal_index below
    -- covers "which one is focused" without needing a second representation.
    goals_json TEXT NOT NULL,
    -- Index into the goals_json array the session/UI currently has focused,
    -- mirroring #162's ProofStateObservation.selected_goal. NULL iff
    -- goals_json is an empty array (nothing to select).
    selected_goal_index INTEGER,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(node_kind IN ('root', 'tactic_result', 'failed_placeholder')),
    CHECK(status IN ('open', 'solved')),
    CHECK(depth >= 0),
    CHECK((node_kind = 'root' AND parent_node_id IS NULL) OR (node_kind <> 'root' AND parent_node_id IS NOT NULL)),
    CHECK(node_kind <> 'root' OR depth = 0)
);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_nodes_session ON interactive_proof_nodes(session_id);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_nodes_parent ON interactive_proof_nodes(parent_node_id);

-- One row per `apply_tactic` call (#159), whether it succeeded or failed.
-- Tactic-step edges are APPEND-ONLY and a failed step is NEVER deleted or
-- hidden -- it remains a normal, queryable row with outcome = 'failed'. That
-- is exactly what makes this table "search evidence" rather than a
-- scratchpad: a dead end is as much a first-class fact as a successful step,
-- and future search/training code can learn from `failed` rows precisely
-- because nothing here quietly drops them.
--
-- See the doc comment above `interactive_proof_sessions` for why diagnostic
-- detail (issue #160's proposed `interactive_proof_diagnostics` table) is
-- folded into this table's `diagnostic_json` / `diagnostics_hash` columns
-- instead of living in a separate table.
CREATE TABLE IF NOT EXISTS interactive_proof_steps (
    id TEXT PRIMARY KEY,
    session_id TEXT NOT NULL REFERENCES interactive_proof_sessions(id),
    parent_node_id TEXT NOT NULL REFERENCES interactive_proof_nodes(id),
    -- NULL iff outcome = 'failed' and the backend created no placeholder node
    -- for it -- #162's ProofStateDiagnostic.child_node_id doc: the only
    -- backend today (MockInteractiveGateway) always leaves this NULL on
    -- failure, but a future backend is allowed to populate one for replay.
    child_node_id TEXT REFERENCES interactive_proof_nodes(id),
    -- crate::lean::observation::hash_tactic_text output. Always present: a
    -- tactic-application call always has tactic text (the caller supplies
    -- it), whether it succeeds or fails.
    tactic_text_hash TEXT NOT NULL,
    -- Content-addressed pointer to the raw tactic text stored as a separate
    -- artifact, matching the *_artifact_hash convention used elsewhere
    -- (proof_source_artifact_hash, compiled_artifact_hash, ...). NULL means
    -- the raw text was not separately archived as an artifact.
    tactic_text_artifact_hash TEXT,
    -- Mirrors the machine-checkable proof_body_redacted marker #162 already
    -- carries on ProofStateObservation: 1 iff the tactic text captured for
    -- this step has been scrubbed before storage/export and must not be
    -- treated as proof-body-bearing evidence; 0 (default) means it is real
    -- tactic-body content.
    redacted_text INTEGER NOT NULL DEFAULT 0,
    outcome TEXT NOT NULL,
    -- Canonical JSON serialization of #162's ProofStateDiagnostic. NULL iff
    -- outcome = 'applied' (a successful step has no diagnostic to record).
    diagnostic_json TEXT,
    -- crate::hashing::canonical_hash over the same diagnostic content
    -- crate::lean::observation::hash_diagnostic computes. NULL exactly when
    -- diagnostic_json is NULL.
    diagnostics_hash TEXT,
    wall_time_ms INTEGER,
    created_at TEXT NOT NULL,
    CHECK(outcome IN ('applied', 'failed')),
    CHECK(outcome <> 'applied' OR child_node_id IS NOT NULL),
    CHECK(outcome <> 'applied' OR diagnostic_json IS NULL),
    CHECK(outcome <> 'failed' OR diagnostic_json IS NOT NULL),
    CHECK((diagnostic_json IS NULL) = (diagnostics_hash IS NULL))
);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_steps_session ON interactive_proof_steps(session_id);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_steps_parent_node ON interactive_proof_steps(parent_node_id);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_steps_child_node ON interactive_proof_steps(child_node_id);

-- A tactic script reconstructed from a root-to-selected-node path (#159's
-- ReconstructedScript, persisted). THE TRUST BOUNDARY LIVES HERE:
-- verified_attempt_id / verification_outcome are NULLABLE and this schema
-- never populates them at INSERT time -- a reconstructed script can exist,
-- be queried, and be handed to a UI/agent with both columns NULL, meaning
-- "reconstructed, not (yet, or ever) submitted for kernel verification."
-- Only a caller that separately resubmits the reconstructed `tactic_block`
-- through the EXISTING Solve/SubmitModule -> action_attempts verification
-- path (entirely unchanged by this migration), and then UPDATEs this row
-- with that action_attempts row's id and resulting status, may populate
-- them. No column on this table, and no trigger in this schema, can write
-- `episode_obligations.status` -- linking a script here never proves
-- anything by itself.
CREATE TABLE IF NOT EXISTS interactive_proof_reconstructed_scripts (
    id TEXT PRIMARY KEY,
    session_id TEXT NOT NULL REFERENCES interactive_proof_sessions(id),
    final_node_id TEXT NOT NULL REFERENCES interactive_proof_nodes(id),
    proof_format TEXT NOT NULL,
    proof_source_hash TEXT NOT NULL,
    proof_source_artifact_hash TEXT,
    -- #159 ReconstructedScript.reports_complete, persisted for parity: a
    -- claim about the SESSION's own internal state only, never proof
    -- authority by itself -- see the table doc above.
    reports_complete INTEGER NOT NULL DEFAULT 0,
    -- Issue #163: canonical JSON array of the root-to-final_node_id node ids
    -- (#159 ReconstructedScript.node_path, persisted). This was the one
    -- "artifact" field #163 found genuinely missing from this table --
    -- backend_kind/backend_version/environment_hash/import_manifest_hash are
    -- deliberately NOT duplicated here: this row's session_id already links
    -- 1:1 to a `interactive_proof_sessions` row that carries all four
    -- (a session's backend/environment does not change over its lifetime),
    -- so duplicating them here would be redundant columns with no query
    -- pattern that needs them split out, same reasoning #160's own doc
    -- comment already gives for folding diagnostics into interactive_proof_steps
    -- instead of a child table. generated_at is likewise just created_at
    -- below, not a separate column. proof_session_reconstruct's MCP response
    -- surfaces all of these (joined from the session) so a caller sees the
    -- full artifact field list without a second round trip.
    tactic_path_ids_json TEXT NOT NULL DEFAULT '[]',
    verified_attempt_id TEXT REFERENCES action_attempts(id),
    verification_outcome TEXT,
    created_at TEXT NOT NULL,
    CHECK(proof_format IN ('flat_tactic_sequence', 'raw_lean_block')),
    CHECK(verification_outcome IS NULL OR verification_outcome IN (
        'claimed', 'preflight_rejected', 'executing', 'verified', 'rejected',
        'committed', 'abandoned', 'expired', 'infrastructure_failed'
    )),
    -- A resolved outcome can only be recorded once an attempt is actually
    -- linked; the reverse (attempt linked, outcome not yet resolved) stays
    -- legal so a caller can record "submitted for verification, pending"
    -- before the linked action_attempts row settles.
    CHECK(verification_outcome IS NULL OR verified_attempt_id IS NOT NULL)
);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_reconstructed_scripts_session ON interactive_proof_reconstructed_scripts(session_id);
CREATE INDEX IF NOT EXISTS idx_interactive_proof_reconstructed_scripts_verified_attempt ON interactive_proof_reconstructed_scripts(verified_attempt_id);

-- Reconnaissance/reasoning trail (SOP, docs/sop-reasoning-logs.md): a
-- standardized, append-only form an agent fills out documenting its own
-- problem-solving process -- hypothesis, approach, expected vs actual
-- outcome, lessons learned -- for EACH episode_step submission (plan,
-- retry-after-failure, error diagnosis, or success retrospective). This is
-- deliberately NOT exposition_artifacts: exposition is human-readable
-- mathematical prose about the PROBLEM (proof strategy, key lemmas);
-- reasoning_logs is about the AGENT'S OWN process across attempts,
-- specifically so failed/dead-end iterations -- otherwise invisible outside
-- this environment, e.g. local scratch-file compilation before submission --
-- become real, permanent training data instead of being silently discarded.
-- episode_revision is the revision this entry pertains to (matching the
-- action_request/episode_step convention elsewhere); action_attempt_id is
-- nullable because reasoning can precede an attempt's existence (initial
-- planning before any submission at all). Append-only, like every other
-- ledger in this schema: a lesson learned from a mistake is not overwritten,
-- it is recorded alongside it.
CREATE TABLE IF NOT EXISTS reasoning_logs (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    episode_revision INTEGER NOT NULL,
    action_attempt_id TEXT REFERENCES action_attempts(id),
    reasoning_kind TEXT NOT NULL,
    hypothesis TEXT,
    approach_summary TEXT NOT NULL,
    expected_outcome TEXT,
    actual_outcome TEXT,
    lesson_learned TEXT,
    confidence TEXT,
    author TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(reasoning_kind IN ('initial_plan', 'retry_after_failure', 'strategy_pivot', 'error_diagnosis', 'success_retrospective', 'other')),
    CHECK(confidence IS NULL OR confidence IN ('low', 'medium', 'high'))
);
CREATE INDEX IF NOT EXISTS idx_reasoning_logs_episode ON reasoning_logs(episode_id, episode_revision);
CREATE INDEX IF NOT EXISTS idx_reasoning_logs_attempt ON reasoning_logs(action_attempt_id);

-- Issue #222: generic content-addressed binary artifacts. Uploads are staged
-- separately so a disconnected or invalid chunk stream can never create a
-- committed artifact. The hash is SHA-256 over the exact BLOB bytes.
CREATE TABLE IF NOT EXISTS content_artifacts (
    artifact_hash TEXT PRIMARY KEY,
    media_type TEXT NOT NULL,
    byte_size INTEGER NOT NULL,
    content BLOB NOT NULL,
    creator TEXT NOT NULL,
    environment_hash TEXT,
    created_at TEXT NOT NULL,
    CHECK(byte_size >= 0),
    CHECK(length(content) = byte_size)
);
CREATE INDEX IF NOT EXISTS idx_content_artifacts_created ON content_artifacts(created_at);

CREATE TABLE IF NOT EXISTS artifact_uploads (
    id TEXT PRIMARY KEY,
    media_type TEXT NOT NULL,
    expected_bytes INTEGER NOT NULL,
    expected_hash TEXT,
    creator TEXT NOT NULL,
    environment_hash TEXT,
    next_offset INTEGER NOT NULL DEFAULT 0,
    content BLOB NOT NULL DEFAULT X'',
    created_at TEXT NOT NULL,
    CHECK(expected_bytes >= 0),
    CHECK(next_offset >= 0),
    CHECK(length(content) = expected_bytes)
);

-- Issue #242 dev diary, slice 1: project-scoped campaign metadata joining
-- existing first-class evidence (problems, episodes, research dossiers,
-- formalization plans, empirical searches, candidate constructions,
-- verification layers, distilled strategies) into a chronological timeline.
-- Deliberately metadata-only, same trust posture as the Level 4 research
-- substrate above: no row here can mark anything proved, verified, or
-- certified, and attachments never alter the artifact they point at.
CREATE TABLE IF NOT EXISTS dev_diary_projects (
    id TEXT PRIMARY KEY,
    project_key TEXT NOT NULL UNIQUE,
    title TEXT NOT NULL,
    summary TEXT,
    audience TEXT,
    claim_policy TEXT,
    public_links_json TEXT,
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(status IN ('active', 'paused', 'completed', 'archived'))
);

-- Polymorphic link to an existing artifact, mirroring verification_layers'
-- target_kind/target_id shape. external_link/public_post have no existing
-- row to point at (a GitHub issue/PR URL, or a manually recorded public
-- post), so target_id is server-minted for those two kinds and external_url
-- carries the real reference instead.
CREATE TABLE IF NOT EXISTS dev_diary_attachments (
    id TEXT PRIMARY KEY,
    project_id TEXT NOT NULL REFERENCES dev_diary_projects(id),
    target_kind TEXT NOT NULL,
    target_id TEXT NOT NULL,
    external_url TEXT,
    label TEXT,
    notes TEXT,
    created_at TEXT NOT NULL,
    UNIQUE(project_id, target_kind, target_id),
    CHECK(target_kind IN (
        'problem_version', 'episode', 'research_dossier', 'formalization_plan',
        'empirical_search', 'candidate_construction', 'verification_layer',
        'distilled_strategy', 'external_link', 'public_post'
    )),
    CHECK(target_kind NOT IN ('external_link', 'public_post') OR external_url IS NOT NULL)
);
CREATE INDEX IF NOT EXISTS idx_dev_diary_attachments_project ON dev_diary_attachments(project_id);

-- checkpoint_number is assigned server-side (MAX+1 per project inside the
-- insert transaction), never caller-supplied, so chronological order is
-- guaranteed regardless of client behavior.
CREATE TABLE IF NOT EXISTS dev_diary_checkpoints (
    id TEXT PRIMARY KEY,
    project_id TEXT NOT NULL REFERENCES dev_diary_projects(id),
    checkpoint_number INTEGER NOT NULL,
    checkpoint_kind TEXT NOT NULL,
    note TEXT NOT NULL,
    referenced_attachment_id TEXT REFERENCES dev_diary_attachments(id),
    author TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(project_id, checkpoint_number),
    CHECK(checkpoint_kind IN (
        'campaign_started', 'candidate_found', 'proof_attempt_failed',
        'root_cause_identified', 'kernel_result', 'mathlib_gap',
        'method_exhausted', 'frontier_changed', 'claim_corrected',
        'infrastructure_issue_opened', 'public_update_posted', 'other'
    ))
);
CREATE INDEX IF NOT EXISTS idx_dev_diary_checkpoints_project ON dev_diary_checkpoints(project_id, checkpoint_number);

-- Issue #242 dev diary, slice 3: an immutable ledger of every generated
-- export. Records what was generated and against which cursor/limits, never
-- the generated prose itself (the external host owns that) — replayable
-- against source_hash if the same project state is queried again.
CREATE TABLE IF NOT EXISTS dev_diary_publications (
    id TEXT PRIMARY KEY,
    project_id TEXT NOT NULL REFERENCES dev_diary_projects(id),
    mode TEXT NOT NULL,
    since_checkpoint_id TEXT REFERENCES dev_diary_checkpoints(id),
    through_checkpoint_id TEXT REFERENCES dev_diary_checkpoints(id),
    x_tier TEXT,
    max_chars_per_post INTEGER,
    dry_run INTEGER NOT NULL,
    source_hash TEXT NOT NULL,
    generated_at TEXT NOT NULL,
    CHECK(mode IN ('structured_json', 'markdown_diary', 'x_thread_prompt', 'single_x_post_prompt', 'blog_prompt', 'institute_update_prompt')),
    CHECK(x_tier IS NULL OR x_tier IN ('free', 'premium')),
    CHECK(dry_run IN (0, 1))
);
CREATE INDEX IF NOT EXISTS idx_dev_diary_publications_project ON dev_diary_publications(project_id, generated_at);

-- Issue #236: append-only storage ledger for proofsearch_core::literature_lineage's
-- LiteratureLineage record (the pure record model + MCIP mapping already ship;
-- this is the remaining storage + MCP surface). One row per hash-pinned
-- lineage record built via LiteratureLineage::new(); the nested
-- search_queries/sources/idea_to_source_map trees are stored as JSON exactly
-- as that constructor produces them, so replay can reconstruct the real Rust
-- type and recompute lineage_hash to detect tampering. Evidence only: no
-- column here can confer proof authority.
CREATE TABLE IF NOT EXISTS literature_lineages (
    id TEXT PRIMARY KEY,
    lineage_hash TEXT NOT NULL UNIQUE,
    lineage_version TEXT NOT NULL,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    environment_hash TEXT NOT NULL,
    problem_version_id TEXT REFERENCES problem_versions(id),
    obligation_id TEXT REFERENCES episode_obligations(id),
    search_queries_json TEXT NOT NULL,
    sources_json TEXT NOT NULL,
    idea_to_source_map_json TEXT NOT NULL,
    all_model_visible INTEGER NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(all_model_visible IN (0, 1))
);
CREATE INDEX IF NOT EXISTS idx_literature_lineages_episode ON literature_lineages(episode_id);

-- Additional provenance links beyond the record's own direct
-- episode/problem_version/obligation fields -- issue #236 also asks for
-- links to research nodes, verified lemmas ("proof variants"), and verified
-- modules. Pure provenance: linking never alters the linked target.
CREATE TABLE IF NOT EXISTS literature_lineage_links (
    id TEXT PRIMARY KEY,
    lineage_id TEXT NOT NULL REFERENCES literature_lineages(id),
    target_kind TEXT NOT NULL,
    target_id TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(lineage_id, target_kind, target_id),
    CHECK(target_kind IN ('research_node', 'verified_lemma', 'verified_module'))
);
CREATE INDEX IF NOT EXISTS idx_literature_lineage_links_lineage ON literature_lineage_links(lineage_id);

-- Issue #237: the publication-review gate. Surfaces proofsearch_core::
-- publication_review's 6-layer model (kernel/certificate, statement-fidelity,
-- literature-completeness, citation-lineage, novelty-claim, exposition-
-- disclosure). One row per episode: layers_json is exactly ReviewLayers as
-- publication_review.rs serializes it, so the server can reconstruct the real
-- Rust type and recompute publication_status() deterministically. This is a
-- PUBLICATION gate over already-established truth, NEVER a proof authority:
-- no column here can mark a theorem proved, and a review outcome never changes
-- the kernel result (kernel_verified is read from the kernel_or_certificate
-- layer, independent of publication_status).
CREATE TABLE IF NOT EXISTS publication_reviews (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL UNIQUE REFERENCES episodes(id),
    review_version TEXT NOT NULL,
    contribution_type TEXT NOT NULL,
    layers_json TEXT NOT NULL,
    makes_strong_novelty_claim INTEGER NOT NULL,
    novelty_uncertain INTEGER NOT NULL,
    contribution_statement TEXT NOT NULL,
    known_prior_art_json TEXT NOT NULL,
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(makes_strong_novelty_claim IN (0, 1)),
    CHECK(novelty_uncertain IN (0, 1)),
    CHECK(contribution_type IN (
        'new_proof', 'independent_rediscovery', 'formalization', 'verification',
        'reconstruction', 'adaptation', 'literature_derived_synthesis'
    ))
);

-- Append-only ledger of every layer decision, so revoking/updating a layer is
-- an auditable event that updates publication status without altering kernel
-- truth or erasing the prior decision. Each event is reviewer-attributed,
-- timestamped, and bound to the proof/source hashes the decision rests on.
CREATE TABLE IF NOT EXISTS publication_review_events (
    id TEXT PRIMARY KEY,
    review_id TEXT NOT NULL REFERENCES publication_reviews(id),
    layer TEXT NOT NULL,
    status TEXT NOT NULL,
    reviewer TEXT NOT NULL,
    bound_hashes_json TEXT NOT NULL,
    notes TEXT,
    decided_at TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(layer IN (
        'kernel_or_certificate', 'statement_fidelity', 'literature_completeness',
        'citation_lineage', 'novelty_claim', 'exposition_disclosure'
    )),
    CHECK(status IN ('not_started', 'in_progress', 'complete', 'blocked_missing_attribution'))
);
CREATE INDEX IF NOT EXISTS idx_publication_review_events_review ON publication_review_events(review_id, created_at);

-- Issue #243: Verified Artifact Registry (VAR) foundation. Promotes a
-- KERNEL-BACKED episode_verified_lemma into a curated, immutable, versioned,
-- queryable research artifact with a lifecycle — distinct from an episode-local
-- helper, a canonical result, an unreviewed abstraction, a generalized reusable
-- lemma, or an upstream-ready Mathlib contribution. TRUST BOUNDARY: the registry
-- CURATES already-established kernel truth. Promotion never fabricates proof
-- authority — every version copies the origin's immutable kernel hashes verbatim
-- and no review or maturity change can alter them; no column here can mark a
-- theorem proved that the kernel did not.
CREATE TABLE IF NOT EXISTS verified_artifacts (
    id TEXT PRIMARY KEY,
    artifact_kind TEXT NOT NULL,
    canonical_name TEXT NOT NULL,
    informal_summary TEXT,
    source_campaign TEXT,
    -- The latest (MAX) version number; versions themselves are immutable rows.
    current_version INTEGER NOT NULL,
    maturity_status TEXT NOT NULL,
    review_status TEXT NOT NULL,
    candidate_for_mathlib INTEGER NOT NULL DEFAULT 0,
    -- Set when this artifact is superseded by another; the original stays navigable.
    superseded_by TEXT REFERENCES verified_artifacts(id),
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(artifact_kind IN (
        'helper_lemma', 'definition', 'theorem', 'abstraction', 'reduction',
        'classification', 'construction', 'negative_result', 'proof_module', 'tactic_recipe'
    )),
    CHECK(maturity_status IN (
        'discovered', 'kernel_verified_local', 'promoted', 'reused', 'generalized',
        'independently_reviewed', 'upstream_candidate', 'upstreamed', 'retained_local', 'superseded'
    )),
    CHECK(review_status IN (
        'unreviewed', 'in_review', 'reviewed_with_caveats', 'independently_reviewed', 'rejected'
    )),
    CHECK(candidate_for_mathlib IN (0, 1))
);

-- Immutable versioned snapshots — appended, never overwritten, so mathematical
-- history is preserved. Kernel hashes are copied verbatim from the promoted
-- lemma at promotion time and are the deterministic reconstruction anchors.
CREATE TABLE IF NOT EXISTS verified_artifact_versions (
    id TEXT PRIMARY KEY,
    artifact_id TEXT NOT NULL REFERENCES verified_artifacts(id),
    artifact_version INTEGER NOT NULL,
    canonical_name TEXT NOT NULL,
    formal_statement TEXT,
    statement_hash TEXT NOT NULL,
    proof_body_hash TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    kernel_result_hash TEXT NOT NULL,
    dependency_ids_json TEXT NOT NULL,
    promotion_reason TEXT,
    replay_status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(artifact_id, artifact_version)
);
CREATE INDEX IF NOT EXISTS idx_var_versions_artifact ON verified_artifact_versions(artifact_id, artifact_version);

-- Provenance: the kernel-backed origin each version was promoted from — a
-- deterministic path back to the source verification evidence.
CREATE TABLE IF NOT EXISTS verified_artifact_origins (
    id TEXT PRIMARY KEY,
    version_id TEXT NOT NULL REFERENCES verified_artifact_versions(id),
    origin_kind TEXT NOT NULL,
    origin_problem_version_id TEXT,
    origin_episode_id TEXT,
    origin_lemma_id TEXT,
    origin_module_item_id TEXT,
    created_at TEXT NOT NULL,
    CHECK(origin_kind IN ('episode_verified_lemma', 'episode_verified_module_item'))
);
CREATE INDEX IF NOT EXISTS idx_var_origins_version ON verified_artifact_origins(version_id);

-- Append-only maturity lifecycle events. A status change is a CURATION event,
-- recorded and never destructive; it never changes proof authority.
CREATE TABLE IF NOT EXISTS verified_artifact_status_events (
    id TEXT PRIMARY KEY,
    artifact_id TEXT NOT NULL REFERENCES verified_artifacts(id),
    from_status TEXT,
    to_status TEXT NOT NULL,
    reason TEXT,
    actor TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(to_status IN (
        'discovered', 'kernel_verified_local', 'promoted', 'reused', 'generalized',
        'independently_reviewed', 'upstream_candidate', 'upstreamed', 'retained_local', 'superseded'
    ))
);
CREATE INDEX IF NOT EXISTS idx_var_status_events_artifact ON verified_artifact_status_events(artifact_id, created_at);

-- Append-only reviews. A review records an assessment and can move review_status,
-- but can NEVER alter a version's kernel hashes or a theorem's proof authority.
CREATE TABLE IF NOT EXISTS verified_artifact_reviews (
    id TEXT PRIMARY KEY,
    artifact_id TEXT NOT NULL REFERENCES verified_artifacts(id),
    version_id TEXT REFERENCES verified_artifact_versions(id),
    review_status TEXT NOT NULL,
    reviewer TEXT NOT NULL,
    notes TEXT,
    created_at TEXT NOT NULL,
    CHECK(review_status IN (
        'unreviewed', 'in_review', 'reviewed_with_caveats', 'independently_reviewed', 'rejected'
    ))
);
CREATE INDEX IF NOT EXISTS idx_var_reviews_artifact ON verified_artifact_reviews(artifact_id, created_at);

-- Issue #250: the VAR dependency/usage graph. Typed edges between artifacts,
-- with an explicit `evidence_kind` that keeps verifier-backed FORMAL use
-- (actually used in a kernel-verified proof) separate from retrieval and
-- human-declared relationships. Popularity is NEVER proof authority: an edge is
-- provenance/impact metadata; no edge marks a theorem proved, and impact metrics
-- are recomputed from these rows, never stored as an assertion.
CREATE TABLE IF NOT EXISTS verified_artifact_edges (
    id TEXT PRIMARY KEY,
    from_artifact_id TEXT NOT NULL REFERENCES verified_artifacts(id),
    to_artifact_id TEXT NOT NULL REFERENCES verified_artifacts(id),
    edge_kind TEXT NOT NULL,
    -- verifier: backed by real kernel dependency evidence (the only kind that
    -- counts as formal use); retrieval: surfaced by search; declared: a
    -- human/agent-asserted relationship.
    evidence_kind TEXT NOT NULL,
    episode_id TEXT,
    campaign TEXT,
    notes TEXT,
    created_at TEXT NOT NULL,
    UNIQUE(from_artifact_id, to_artifact_id, edge_kind, evidence_kind),
    CHECK(edge_kind IN (
        'formally_depends_on', 'imported_by_generated_module', 'selected_as_retrieval_candidate',
        'retrieved_but_unused', 'actually_used_in_verified_proof', 'generalized_from',
        'equivalent_to', 'supersedes', 'applies_to_campaign', 'exported_as_mathcorpus_packet',
        'proposed_to_mathlib'
    )),
    CHECK(evidence_kind IN ('verifier', 'retrieval', 'declared'))
);
CREATE INDEX IF NOT EXISTS idx_var_edges_from ON verified_artifact_edges(from_artifact_id, edge_kind);
CREATE INDEX IF NOT EXISTS idx_var_edges_to ON verified_artifact_edges(to_artifact_id, edge_kind);

-- Issue #250: Mathlib upstream-readiness review metadata for an artifact. This is
-- REVIEW METADATA, never proof status — the status/checklist say nothing about
-- whether the theorem is proved (that is the kernel's, immutable).
CREATE TABLE IF NOT EXISTS verified_artifact_upstream_readiness (
    artifact_id TEXT PRIMARY KEY REFERENCES verified_artifacts(id),
    status TEXT NOT NULL,
    checklist_json TEXT NOT NULL,
    reviewer TEXT,
    notes TEXT,
    updated_at TEXT NOT NULL,
    CHECK(status IN (
        'not_candidate', 'needs_generalization', 'needs_deduplication', 'needs_style_review',
        'ready_for_pr', 'pr_open', 'accepted', 'rejected_or_retained_local'
    ))
);

-- Proactive retrieval packets (issue #248): an advisory, budget-aware,
-- reproducible record of a retrieval pass run at a formalization checkpoint
-- (plan item created, obligation created, repeated failure, before give-up, or
-- an explicit manual pass). The packet captures the DERIVED query features (the
-- agent never has to name candidates), the exact search/index versions, the
-- ranked candidates with per-source trust labels and environment compatibility,
-- and — after the agent chooses — which candidates it inspected/selected so that
-- retrieved-but-unused results stay distinguishable from actual verifier-backed
-- dependencies (verified_artifact_edges with evidence_kind='verifier').
--
-- TRUST BOUNDARY: a retrieval packet is advisory metadata only. It never adds an
-- import, alters a problem version, or marks an obligation proved; a high rank is
-- never applicability. `enabled = 0` records a pass that a controlled-evaluation
-- run envelope deliberately disabled (evaluation/benchmark/private_audit modes) —
-- the pass is still logged (with zero candidates) so the trajectory stays honest,
-- never silently skipped. `contamination_json` records benchmark exposure so a
-- benchmark-linked problem's retrieval can never be laundered out of the record.
--
-- The row is created append-only; record_selection UPDATEs only the advisory
-- selections_json / unused_json convenience columns (never any hash, outcome, or
-- proof-authority field), mirroring how other advisory ledgers keep a current
-- mirror over their append-only events.
CREATE TABLE IF NOT EXISTS retrieval_packets (
    id TEXT PRIMARY KEY,
    created_at TEXT NOT NULL,
    trigger_mode TEXT NOT NULL,
    scope_kind TEXT NOT NULL,
    scope_id TEXT,
    run_envelope_id TEXT REFERENCES run_envelopes(id),
    enabled INTEGER NOT NULL,
    query_features_json TEXT NOT NULL,
    search_version TEXT NOT NULL,
    sources_status_json TEXT NOT NULL,
    candidates_json TEXT NOT NULL,
    selections_json TEXT NOT NULL,
    unused_json TEXT NOT NULL,
    contamination_json TEXT NOT NULL,
    budget_json TEXT NOT NULL,
    CHECK(trigger_mode IN ('manual', 'plan_item_created', 'obligation_created', 'after_repeated_failure', 'before_give_up')),
    CHECK(scope_kind IN ('problem', 'plan_item', 'episode', 'freeform')),
    CHECK(enabled IN (0, 1))
);
CREATE INDEX IF NOT EXISTS idx_retrieval_packets_scope ON retrieval_packets(scope_kind, scope_id, created_at);

-- Portable Verified Artifact Registry bundle imports (issue #249): an
-- append-only ledger of every registry bundle imported INTO this instance from
-- another Proof Search instance. A registry hash/artifact id is not independent
-- evidence to another installation unless the exact canonical preimages travel
-- with it; a bundle carries the artifacts, immutable versions (with kernel
-- hashes + formal-statement preimages + optional proof-source bytes), origins,
-- edges, reviews, status events, and upstream readiness, plus a bundle_hash over
-- the canonical content so any tampering is detectable before a single row is
-- written. Import PRESERVES origin ids/hashes and NEVER translates an imported
-- review into local kernel authority — an imported artifact remains
-- source-distinguished from a locally produced one (origin_instance_id), and its
-- kernel hashes are inert data until re-verified against the pinned environment.
-- Each import records what was inserted, skipped as an exact duplicate, or
-- quarantined (a version/name conflict, or an unavailable/unreplayable
-- environment) so a partial or conflicting bundle produces quarantine records,
-- never a false verification. dry_run rows record a preview that wrote nothing.
CREATE TABLE IF NOT EXISTS artifact_bundle_imports (
    id TEXT PRIMARY KEY,
    origin_instance_id TEXT,
    bundle_version TEXT NOT NULL,
    bundle_hash TEXT NOT NULL,
    dry_run INTEGER NOT NULL,
    imported_at TEXT NOT NULL,
    summary_json TEXT NOT NULL,
    CHECK(dry_run IN (0, 1))
);
CREATE INDEX IF NOT EXISTS idx_artifact_bundle_imports_hash ON artifact_bundle_imports(bundle_hash, imported_at);

-- Generated shared Lean modules materialized from promoted registry artifacts
-- (issue #247): a deterministic, versioned library assembled from immutable
-- registry records so a reviewed promoted artifact becomes an actual reusable
-- Lean dependency instead of being copied/reconstructed by hand. The source is a
-- PURE FUNCTION of the ordered registry records, so rebuilding the same snapshot
-- reproduces identical bytes and source_hash (tamper-evident). The module never
-- carries unverified prose or a client-supplied proof body: a declaration's proof
-- is embedded ONLY when its kernel-verified source resolves from the content-
-- addressed store, otherwise the declaration is rendered as a signature-only
-- provenance comment and replay_status records that it is not yet self-contained.
--
-- TRUST BOUNDARY: materializing a module and planning an import are ADVISORY.
-- They never mutate an existing problem's immutable import manifest and never
-- confer proof authority; actual reuse still happens through problem_create with
-- an explicit manifest and a kernel-verified attempt. Environment compatibility
-- is enforced at materialization (a module mixes only artifacts sharing one
-- environment_hash) and dependencies among the selected artifacts are required to
-- be acyclic and topologically ordered.
CREATE TABLE IF NOT EXISTS generated_artifact_modules (
    id TEXT PRIMARY KEY,
    module_path TEXT NOT NULL,
    category TEXT NOT NULL,
    environment_hash TEXT NOT NULL,
    artifact_version_ids_json TEXT NOT NULL,
    source_text TEXT NOT NULL,
    source_hash TEXT NOT NULL,
    replay_status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(category IN ('NumberTheory', 'Combinatorics', 'GraphTheory', 'Analysis', 'Campaigns')),
    CHECK(replay_status IN ('self_contained_source', 'proof_source_unavailable'))
);
CREATE INDEX IF NOT EXISTS idx_generated_modules_hash ON generated_artifact_modules(source_hash);

-- Elaborated structural fingerprints for type-directed search (issue #245). Each
-- row is the normalized structural representation of a verified artifact version's
-- formal statement, produced by REAL Lean elaboration under the pinned
-- environment (never a parser approximation): the conclusion head symbol, the
-- binder count, the hypothesis head multiset, and the used-constant set, plus a
-- canonical fingerprint_hash for exact-type matching. Index identity is
-- (version_id, fingerprint_version) and the lean_toolchain is recorded, so a
-- record is invalidated/namespaced when the toolchain or the fingerprint
-- representation changes. Advisory: a fingerprint changes no proof state and no
-- imports, and confers no proof authority — it is a search key over
-- already-established statements.
CREATE TABLE IF NOT EXISTS verified_artifact_fingerprints (
    version_id TEXT NOT NULL REFERENCES verified_artifact_versions(id),
    fingerprint_version TEXT NOT NULL,
    lean_toolchain TEXT,
    binder_count INTEGER NOT NULL,
    conclusion_head TEXT NOT NULL,
    hypothesis_heads_json TEXT NOT NULL,
    constants_json TEXT NOT NULL,
    fingerprint_hash TEXT NOT NULL,
    computed_at TEXT NOT NULL,
    PRIMARY KEY (version_id, fingerprint_version)
);
CREATE INDEX IF NOT EXISTS idx_var_fingerprints_conclusion ON verified_artifact_fingerprints(conclusion_head, binder_count);
"#;

pub fn initialize_v1_db(conn: &Connection) -> rusqlite::Result<()> {
    // Foreign keys stay OFF for the whole init sequence: the constraint-vocabulary
    // migrations below drop and recreate tables that other tables reference (e.g.
    // problem_fidelity_reviews -> problem_versions, episode_obligations ->
    // episodes), which foreign-key enforcement would otherwise block. Turned back
    // on at the end so normal operation still enforces them.
    conn.execute("PRAGMA foreign_keys = OFF;", [])?;
    // Must run BEFORE the CREATE TABLE IF NOT EXISTS batch below: that statement
    // is a no-op on a `problem_versions` table that already exists (from a
    // pre-v0.2.3 database), so a DB created before the import-manifest columns
    // existed would otherwise be left permanently missing them, and the first
    // query touching them would fail with "no such column".
    migrate_add_import_manifest_columns(conn)?;
    migrate_add_mutual_group_column(conn)?;
    migrate_add_prover_ready_statement_columns(conn)?;
    migrate_add_benchmark_fidelity_basis_columns(conn)?;
    migrate_add_lean_result_bytes_column(conn)?;
    migrate_add_current_cost_observation_column(conn)?;
    migrate_add_benchmark_goal_class_columns(conn)?;
    migrate_add_plan_item_asymptotic_role_column(conn)?;
    migrate_add_interactive_session_close_reason_column(conn)?;
    migrate_add_reconstructed_script_tactic_path_column(conn)?;
    // CHECK constraints are baked into a table at creation and CREATE TABLE IF
    // NOT EXISTS cannot update them on a table that already exists — a database
    // that predates the fidelity-vocabulary rewrite (docs/fix_plan_playtest_02.md)
    // is otherwise left PERMANENTLY enforcing the old CHECK(fidelity_status IN
    // ('pending','approved','revoked')) / CHECK(outcome IN (...) — no
    // 'kernel_verified') constraints, silently rejecting every INSERT that uses
    // the current vocabulary. This is a harder failure than a missing column:
    // it's a deterministic, permanent rejection of the current code's writes,
    // not a one-time schema gap. See docs/fix_plan_playtest_05.md.
    migrate_fidelity_status_vocabulary(conn)?;
    migrate_expand_fidelity_status_benchmark_aligned(conn)?;
    migrate_episode_outcome_vocabulary(conn)?;
    migrate_ingested_document_nodes_backed_status_checks(conn)?;
    conn.execute_batch(V1_SCHEMA)?;
    seed_proof_patterns(conn)?;
    conn.execute("PRAGMA foreign_keys = ON;", [])?;
    Ok(())
}

/// Seeds `proof_patterns` with the reusable lessons documented in
/// `docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md` (issue #24).
/// `INSERT OR IGNORE` keyed on the UNIQUE `pattern_key`: a no-op on a database
/// that already has these rows (from a prior init), and additive on any other
/// database — never overwrites a pattern a user has since edited or
/// deprecated. Every seed pattern has `confidence = 'seed'` (hand-authored
/// from a documented lesson, not mined from local attempt data) and
/// `source_episode_id = NULL` (the originating episodes lived in a scratch
/// playtest database, not this one).
fn seed_proof_patterns(conn: &Connection) -> rusqlite::Result<()> {
    struct Seed {
        key: &'static str,
        title: &'static str,
        failure_signature: &'static str,
        recommended_repair: &'static str,
        applicable_when: &'static [&'static str],
        avoid_when: &'static [&'static str],
    }
    const SEEDS: &[Seed] = &[
        Seed {
            key: "mathlib_api_drift_renamed_lemma",
            title: "Mathlib API drift: lemma renamed in the pinned commit",
            failure_signature: "unknown identifier for a lemma name that plausibly existed under a similar/older name (e.g. `le_div_iff` failing where `le_div_iff₀` is expected)",
            recommended_repair: "Call lean_declaration_lookup on the exact name (deep_check=true if the fast path is inconclusive) before assuming a tactic-level fix is needed; renamed variants often add a `₀`/`'` suffix or move namespace",
            applicable_when: &["unknown_declaration diagnostic on a lemma name you're confident exists in Mathlib", "the name resembles a known lemma but with a different suffix/namespace"],
            avoid_when: &["the diagnostic is a genuine type mismatch or parse error, not an unresolved identifier"],
        },
        Seed {
            key: "def_wrapped_decidable_needs_unfold",
            title: "Def-wrapped decidable Prop: unfold before decide",
            failure_signature: "`decide` fails or times out on a goal stated in terms of a client-defined `def` wrapping a `Decidable` proposition",
            recommended_repair: "`unfold <def_name>` (or `simp only [<def_name>]`) before `decide`",
            applicable_when: &["the goal's head symbol is a local def, not a Mathlib primitive", "decide alone fails with no reduction progress"],
            avoid_when: &["the def is already reducible/marked @[reducible] and decide succeeds directly"],
        },
        Seed {
            key: "well_founded_recursion_needs_simp_not_rfl",
            title: "Well-founded recursion: rfl/decide may not reduce it — try simp [def_name]",
            failure_signature: "`rfl` or `decide` fails to reduce a call to a def whose recursion is not structural (e.g. divides its argument, like `n / 2`) even though the definition is correct",
            recommended_repair: "compiles to WellFounded.fix, not a structural fixpoint the kernel reduces through rfl/decide; try `simp [<def_name>]` to expose the auto-generated equation lemmas instead",
            applicable_when: &["the def's recursive call does not obviously decrease by a Nat.succ/structural pattern (division, subtraction, custom measure)"],
            avoid_when: &["the recursion is structural (matches on a constructor and recurses on a strict subterm) — rfl should already work there"],
        },
        Seed {
            key: "structural_recursion_rfl_closes_directly",
            title: "Structural (course-of-values) recursion: rfl closes it directly",
            failure_signature: "(not a failure — a confirmed-working pattern) uncertainty about whether rfl scales to deeper structural recursion calls",
            recommended_repair: "`rfl` closes course-of-values structural recursion (e.g. Fibonacci-style referencing n-1 and n-2) at both shallow and deeper call values — no special handling needed before trying it",
            applicable_when: &["the def is expressed as `fun n => match n with | ... => ...` with structural (constructor-decreasing) recursive calls"],
            avoid_when: &["the recursion is well-founded/division-based — see well_founded_recursion_needs_simp_not_rfl instead"],
        },
        Seed {
            key: "mutual_recursion_needs_mutual_group",
            title: "Mutual recursion: use MutualGroup, not two forward-referencing bare defs",
            failure_signature: "unknown identifier when a Def's body references another Def declared later in module_items (e.g. isEven referencing isOdd before isOdd is declared)",
            recommended_repair: "submit both as members of one LeanModuleItem::MutualGroup — module_items renders as a flat sequential list with no forward references, so a plain Def can only see declarations that came before it",
            applicable_when: &["two or more helper defs/theorems in a SubmitModule action must reference each other"],
            avoid_when: &["only one direction of reference is needed — reorder module_items instead of introducing a group"],
        },
        Seed {
            key: "real_inequality_needs_linarith_imports",
            title: "Real-number inequalities: import Linarith/Nlinarith and Real.Basic explicitly",
            failure_signature: "unknown tactic (nlinarith/linarith) or failed to synthesize an arithmetic instance on ℝ under the base import manifest",
            recommended_repair: "add Mathlib.Tactic.Linarith, Mathlib.Tactic.Nlinarith (as needed), and Mathlib.Data.Real.Basic via problem_create(problem_imports=[...]) — the base manifest is only Ring + NormNum",
            applicable_when: &["the root or a helper statement quantifies over ℝ and uses an inequality"],
            avoid_when: &["the goal is purely over ℕ/ℤ with no division — omega or the base manifest may already suffice"],
        },
        Seed {
            key: "unsafe_dev_attestation_caps_at_kernel_verified",
            title: "unsafe_dev_attestation is for fast iteration, not a shortcut to certified",
            failure_signature: "(not a failure — a boundary to remember) confusion about why a proved episode under a dev-attested problem never reaches outcome=certified",
            recommended_repair: "problem_create(unsafe_dev_attestation=true) sets fidelity_status='attested', which permanently caps every episode under that problem_version at kernel_verified and excludes it from default dataset exports (training_eligible=false) — use problem_submit_fidelity_review for a real, evidence-backed review if certified is needed",
            applicable_when: &["play-testing or exploratory proof-search iteration where fidelity review would slow down the loop"],
            avoid_when: &["the resulting proof needs to be certified or included in a default dataset export — create the problem_version through a real fidelity review instead"],
        },
    ];

    for seed in SEEDS {
        let applicable_when_json = serde_json::to_string(seed.applicable_when).unwrap();
        let avoid_when_json = serde_json::to_string(seed.avoid_when).unwrap();
        conn.execute(
            "INSERT OR IGNORE INTO proof_patterns (
                id, pattern_key, title, failure_signature, recommended_repair,
                applicable_when_json, avoid_when_json, source_episode_id,
                source_attempt_ids_json, confidence, status, created_at
            ) VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, NULL, '[]', 'seed', 'active', ?8)",
            (
                uuid::Uuid::new_v4().to_string(),
                seed.key,
                seed.title,
                seed.failure_signature,
                seed.recommended_repair,
                &applicable_when_json,
                &avoid_when_json,
                chrono::Utc::now().to_rfc3339(),
            ),
        )?;
    }
    Ok(())
}

/// Rebuilds `problem_versions` if it still carries the pre-fidelity-split CHECK
/// constraints (`fidelity_status IN ('pending','approved','revoked')`) — SQLite
/// has no `ALTER TABLE ... DROP CONSTRAINT`, so the only way to change a CHECK
/// is the standard create-copy-drop-rename sequence. No-op on a fresh database
/// or an already-migrated one (detected by checking whether the stored table
/// SQL already mentions the current vocabulary).
///
/// `'approved'` maps to `'verified'`, not `'attested'`: existing rows in state
/// `COMPLETE` already satisfy the (then-nonexistent) invariant "COMPLETE implies
/// verified" retroactively, and mapping to `'attested'` would make that INSERT
/// violate the current CHECK on the spot, failing the migration itself for any
/// database with a COMPLETE-state row.
fn migrate_fidelity_status_vocabulary(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='problem_versions'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let current_sql: String = conn.query_row(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name='problem_versions'",
        [],
        |row| row.get(0),
    )?;
    if current_sql.contains("'unreviewed'") {
        return Ok(());
    }

    conn.execute_batch(
        "CREATE TABLE problem_versions_migrating (
            id TEXT PRIMARY KEY,
            source_problem_text TEXT NOT NULL,
            source_problem_hash TEXT NOT NULL,
            source_metadata_json TEXT NOT NULL,
            root_formal_statement TEXT NOT NULL,
            root_statement_hash TEXT NOT NULL,
            normalized_root_rendering TEXT NOT NULL,
            environment_hash TEXT NOT NULL,
            import_manifest_json TEXT NOT NULL DEFAULT '[\"Mathlib.Tactic.Ring\",\"Mathlib.Tactic.NormNum\"]',
            import_manifest_hash TEXT NOT NULL DEFAULT '',
            fidelity_status TEXT NOT NULL,
            fidelity_method TEXT NOT NULL,
            fidelity_approval_id TEXT,
            root_obligation_id TEXT,
            state TEXT NOT NULL,
            created_at TEXT NOT NULL,
            CHECK(state NOT IN ('PROVING', 'ROOT_PROVED_COVERAGE_PENDING', 'ROOT_PROVED_COVERAGE_UNCONVERGED') OR fidelity_status IN ('verified', 'attested')),
            CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified'),
            CHECK(fidelity_status IN ('unreviewed', 'attested', 'verified', 'rejected', 'revoked'))
        );
        INSERT INTO problem_versions_migrating (
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, import_manifest_json, import_manifest_hash,
            fidelity_status, fidelity_method, fidelity_approval_id,
            root_obligation_id, state, created_at
        )
        SELECT
            id, source_problem_text, source_problem_hash, source_metadata_json,
            root_formal_statement, root_statement_hash, normalized_root_rendering,
            environment_hash, import_manifest_json, import_manifest_hash,
            CASE fidelity_status
                WHEN 'approved' THEN 'verified'
                WHEN 'pending' THEN 'unreviewed'
                WHEN 'revoked' THEN 'revoked'
                ELSE 'unreviewed'
            END,
            fidelity_method, fidelity_approval_id, root_obligation_id, state, created_at
        FROM problem_versions;
        DROP TABLE problem_versions;
        ALTER TABLE problem_versions_migrating RENAME TO problem_versions;",
    )?;
    Ok(())
}

/// Issue #43: expands the fidelity vocabulary to include `benchmark_aligned`
/// (problem_versions.fidelity_status and the proving-allowed CHECK) and the
/// review decision vocabulary (problem_fidelity_reviews.decision). Same
/// create-copy-drop-rename technique as `migrate_fidelity_status_vocabulary`,
/// for the same reason: a database that predates #43 would otherwise reject
/// every `benchmark_aligned` write forever. Strictly additive — every prior
/// value is preserved verbatim, and the load-bearing
/// `CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified')` guard is
/// carried over unchanged, so `benchmark_aligned` can never reach COMPLETE.
/// Idempotent: no-op once the stored CHECK text already mentions the value.
fn migrate_expand_fidelity_status_benchmark_aligned(conn: &Connection) -> rusqlite::Result<()> {
    let pv_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='problem_versions'",
        [], |row| row.get(0),
    )?;
    if pv_exists != 0 {
        let current_sql: String = conn.query_row(
            "SELECT sql FROM sqlite_master WHERE type='table' AND name='problem_versions'",
            [], |row| row.get(0),
        )?;
        // Only rebuild an already-current-vocabulary table (has 'unreviewed')
        // that hasn't yet gained 'benchmark_aligned'. A pre-'unreviewed' DB is
        // handled by migrate_fidelity_status_vocabulary running first.
        if current_sql.contains("'unreviewed'") && !current_sql.contains("'benchmark_aligned'") {
            conn.execute_batch(
                "CREATE TABLE problem_versions_ba_migrating (
                    id TEXT PRIMARY KEY,
                    source_problem_text TEXT NOT NULL,
                    source_problem_hash TEXT NOT NULL,
                    source_metadata_json TEXT NOT NULL,
                    root_formal_statement TEXT NOT NULL,
                    root_statement_hash TEXT NOT NULL,
                    normalized_root_rendering TEXT NOT NULL,
                    environment_hash TEXT NOT NULL,
                    import_manifest_json TEXT NOT NULL DEFAULT '[\"Mathlib.Tactic.Ring\",\"Mathlib.Tactic.NormNum\"]',
                    import_manifest_hash TEXT NOT NULL DEFAULT '',
                    fidelity_status TEXT NOT NULL,
                    fidelity_method TEXT NOT NULL,
                    fidelity_approval_id TEXT,
                    root_obligation_id TEXT,
                    state TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    CHECK(state NOT IN ('PROVING', 'ROOT_PROVED_COVERAGE_PENDING', 'ROOT_PROVED_COVERAGE_UNCONVERGED') OR fidelity_status IN ('verified', 'attested', 'benchmark_aligned')),
                    CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified'),
                    CHECK(fidelity_status IN ('unreviewed', 'attested', 'verified', 'rejected', 'revoked', 'benchmark_aligned'))
                );
                INSERT INTO problem_versions_ba_migrating (
                    id, source_problem_text, source_problem_hash, source_metadata_json,
                    root_formal_statement, root_statement_hash, normalized_root_rendering,
                    environment_hash, import_manifest_json, import_manifest_hash,
                    fidelity_status, fidelity_method, fidelity_approval_id,
                    root_obligation_id, state, created_at
                )
                SELECT
                    id, source_problem_text, source_problem_hash, source_metadata_json,
                    root_formal_statement, root_statement_hash, normalized_root_rendering,
                    environment_hash, import_manifest_json, import_manifest_hash,
                    fidelity_status, fidelity_method, fidelity_approval_id,
                    root_obligation_id, state, created_at
                FROM problem_versions;
                DROP TABLE problem_versions;
                ALTER TABLE problem_versions_ba_migrating RENAME TO problem_versions;",
            )?;
        }
    }

    let pfr_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='problem_fidelity_reviews'",
        [], |row| row.get(0),
    )?;
    if pfr_exists != 0 {
        let current_sql: String = conn.query_row(
            "SELECT sql FROM sqlite_master WHERE type='table' AND name='problem_fidelity_reviews'",
            [], |row| row.get(0),
        )?;
        if !current_sql.contains("'benchmark_aligned'") {
            conn.execute_batch(
                "CREATE TABLE problem_fidelity_reviews_ba_migrating (
                    id TEXT PRIMARY KEY,
                    problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
                    source_problem_hash TEXT NOT NULL,
                    root_statement_hash TEXT NOT NULL,
                    normalized_rendering_hash TEXT NOT NULL,
                    decision TEXT NOT NULL,
                    method TEXT NOT NULL,
                    approver_id TEXT NOT NULL,
                    rubric_version TEXT NOT NULL,
                    evidence_json TEXT NOT NULL,
                    notes TEXT,
                    signature TEXT,
                    created_at TEXT NOT NULL,
                    revoked_at TEXT,
                    CHECK(decision IN ('verified', 'rejected', 'benchmark_aligned'))
                );
                INSERT INTO problem_fidelity_reviews_ba_migrating
                SELECT id, problem_version_id, source_problem_hash, root_statement_hash,
                       normalized_rendering_hash, decision, method, approver_id, rubric_version,
                       evidence_json, notes, signature, created_at, revoked_at
                FROM problem_fidelity_reviews;
                DROP TABLE problem_fidelity_reviews;
                ALTER TABLE problem_fidelity_reviews_ba_migrating RENAME TO problem_fidelity_reviews;",
            )?;
        }
    }
    Ok(())
}

/// Rebuilds `episodes` if it still carries the pre-fidelity-split CHECK on
/// `outcome` (missing `'kernel_verified'`) — same create-copy-drop-rename
/// technique as `migrate_fidelity_status_vocabulary`, and for the same reason:
/// a database that predates the fidelity split would otherwise reject every
/// episode reaching the `kernel_verified` outcome forever. The column set and
/// order are unchanged by this migration (only the CHECK differs), so this is
/// a straight `SELECT *` copy, unlike the `problem_versions` migration.
fn migrate_episode_outcome_vocabulary(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='episodes'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let current_sql: String = conn.query_row(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name='episodes'",
        [],
        |row| row.get(0),
    )?;
    if current_sql.contains("'kernel_verified'") {
        return Ok(());
    }

    conn.execute_batch(
        "CREATE TABLE episodes_migrating (
            id TEXT PRIMARY KEY,
            problem_version_id TEXT NOT NULL REFERENCES problem_versions(id),
            task_id TEXT,
            task_revision INTEGER,
            environment_version TEXT,
            protocol_version TEXT,
            observation_schema_version TEXT,
            action_schema_version TEXT,
            reward_policy_version TEXT,
            verifier_version TEXT,
            lean_toolchain_version TEXT,
            seed INTEGER,
            state TEXT NOT NULL,
            current_revision INTEGER NOT NULL DEFAULT 0,
            initial_state_hash TEXT,
            current_state_hash TEXT,
            step_count INTEGER NOT NULL DEFAULT 0,
            max_steps INTEGER,
            token_budget INTEGER,
            cost_budget_micros INTEGER,
            wall_clock_deadline TEXT,
            invalid_action_count INTEGER NOT NULL DEFAULT 0,
            invalid_action_limit INTEGER,
            outcome TEXT,
            termination_reason TEXT,
            truncation_reason TEXT,
            run_id TEXT,
            parent_episode_id TEXT REFERENCES episodes(id),
            created_at TEXT NOT NULL,
            updated_at TEXT,
            completed_at TEXT,
            CHECK(state IN ('awaiting_external_action', 'executing_action', 'terminated', 'truncated')),
            CHECK(outcome IN ('certified', 'kernel_verified', 'refuted', 'gave_up', 'timeout', 'budget_exhausted', 'model_error', 'infrastructure_error') OR outcome IS NULL),
            CHECK((state = 'terminated' AND outcome IS NOT NULL AND termination_reason IS NOT NULL) OR state <> 'terminated'),
            CHECK((state = 'truncated' AND outcome IS NOT NULL AND truncation_reason IS NOT NULL) OR state <> 'truncated'),
            CHECK(NOT (state = 'terminated' AND truncation_reason IS NOT NULL)),
            CHECK(NOT (state = 'truncated' AND termination_reason IS NOT NULL))
        );
        INSERT INTO episodes_migrating SELECT * FROM episodes;
        DROP TABLE episodes;
        ALTER TABLE episodes_migrating RENAME TO episodes;",
    )?;
    Ok(())
}

/// Issue #27 (PR #58 review, blocker #2): rebuilds an `ingested_document_nodes`
/// table that was created before the three "backed status requires a real
/// forward link" CHECK constraints existed, so the structural guarantee holds
/// on every database, not only freshly-created ones. Same create-copy-drop-
/// rename technique as `migrate_fidelity_status_vocabulary`, for the same
/// reason: CREATE TABLE IF NOT EXISTS cannot add a CHECK to a table that
/// already exists, so without this a pre-existing local DB would keep enforcing
/// only the handler guard (layer 1) and a raw write could decouple a
/// citation_recorded / formalization_target_linked / linked_to_dossier_artifact
/// label from any real artifact.
///
/// Idempotent: no-op once the stored CHECK text is present. Only rebuilds a
/// table that already carries `linked_formalization_plan_item_id` (the column
/// that must exist for the copy's SELECT) — an even-older shape is a throwaway
/// mid-development DB that is already incompatible with the current node SELECT
/// and is left for a fresh create. Any legacy row that would violate the new
/// CHECKs (a backed status with no matching FK — reachable only through the
/// pre-fix free-form path) is sanitized back to its unbacked base value during
/// the copy, so the rebuild itself never fails on bad data.
fn migrate_ingested_document_nodes_backed_status_checks(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='ingested_document_nodes'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let current_sql: String = conn.query_row(
        "SELECT sql FROM sqlite_master WHERE type='table' AND name='ingested_document_nodes'",
        [],
        |row| row.get(0),
    )?;
    // Already migrated (the distinctive backed-status CHECK is present).
    if current_sql.contains("citation_status <> 'citation_recorded'") {
        return Ok(());
    }
    // Only a table already carrying every current column can be copied; an
    // older shape lacking linked_formalization_plan_item_id is an incompatible
    // dev throwaway — leave it for a fresh create rather than crash.
    if !current_sql.contains("linked_formalization_plan_item_id") {
        return Ok(());
    }

    // Table body kept byte-for-byte in sync with the CREATE TABLE above.
    conn.execute_batch(
        "CREATE TABLE ingested_document_nodes_migrating (
            id TEXT PRIMARY KEY,
            document_id TEXT NOT NULL REFERENCES ingested_documents(id),
            dossier_id TEXT REFERENCES research_dossiers(id),
            node_order INTEGER NOT NULL,
            node_kind TEXT NOT NULL,
            natural_language_text TEXT NOT NULL,
            source_span TEXT NOT NULL,
            confidence TEXT,
            formalization_status TEXT NOT NULL DEFAULT 'prose_only',
            citation_status TEXT NOT NULL DEFAULT 'uncited',
            review_status TEXT NOT NULL DEFAULT 'unreviewed_extraction',
            risk_flags_json TEXT NOT NULL DEFAULT '[]',
            linked_external_reference_id TEXT REFERENCES external_references(id),
            linked_external_theorem_claim_id TEXT REFERENCES external_theorem_claims(id),
            linked_research_node_id TEXT REFERENCES research_nodes(id),
            linked_formalization_plan_item_id TEXT REFERENCES formalization_plan_items(id),
            created_at TEXT NOT NULL,
            updated_at TEXT NOT NULL,
            UNIQUE(document_id, node_order),
            CHECK(node_kind IN (
                'abstract', 'main_theorem', 'definition', 'proposition', 'lemma',
                'proof_step', 'construction', 'remark', 'appendix_fact', 'reference', 'open_gap'
            )),
            CHECK(formalization_status IN ('prose_only', 'formalization_pending', 'formalization_target_linked')),
            CHECK(citation_status IN ('uncited', 'citation_recorded')),
            CHECK(confidence IS NULL OR confidence IN ('low', 'medium', 'high')),
            CHECK(review_status IN (
                'unreviewed_extraction',
                'machine_extracted',
                'human_reviewed_extraction',
                'rejected_extraction',
                'linked_to_dossier_artifact'
            )),
            CHECK(citation_status <> 'citation_recorded'
                  OR linked_external_reference_id IS NOT NULL
                  OR linked_external_theorem_claim_id IS NOT NULL),
            CHECK(formalization_status <> 'formalization_target_linked'
                  OR linked_research_node_id IS NOT NULL
                  OR linked_formalization_plan_item_id IS NOT NULL),
            CHECK(review_status <> 'linked_to_dossier_artifact'
                  OR linked_external_reference_id IS NOT NULL
                  OR linked_external_theorem_claim_id IS NOT NULL
                  OR linked_research_node_id IS NOT NULL
                  OR linked_formalization_plan_item_id IS NOT NULL)
        );
        INSERT INTO ingested_document_nodes_migrating (
            id, document_id, dossier_id, node_order, node_kind, natural_language_text,
            source_span, confidence, formalization_status, citation_status, review_status,
            risk_flags_json, linked_external_reference_id, linked_external_theorem_claim_id,
            linked_research_node_id, linked_formalization_plan_item_id, created_at, updated_at
        )
        SELECT
            id, document_id, dossier_id, node_order, node_kind, natural_language_text,
            source_span, confidence,
            CASE WHEN formalization_status = 'formalization_target_linked'
                      AND linked_research_node_id IS NULL
                      AND linked_formalization_plan_item_id IS NULL
                 THEN 'prose_only' ELSE formalization_status END,
            CASE WHEN citation_status = 'citation_recorded'
                      AND linked_external_reference_id IS NULL
                      AND linked_external_theorem_claim_id IS NULL
                 THEN 'uncited' ELSE citation_status END,
            CASE WHEN review_status = 'linked_to_dossier_artifact'
                      AND linked_external_reference_id IS NULL
                      AND linked_external_theorem_claim_id IS NULL
                      AND linked_research_node_id IS NULL
                      AND linked_formalization_plan_item_id IS NULL
                 THEN 'machine_extracted' ELSE review_status END,
            risk_flags_json, linked_external_reference_id, linked_external_theorem_claim_id,
            linked_research_node_id, linked_formalization_plan_item_id, created_at, updated_at
        FROM ingested_document_nodes;
        DROP TABLE ingested_document_nodes;
        ALTER TABLE ingested_document_nodes_migrating RENAME TO ingested_document_nodes;",
    )?;
    Ok(())
}

/// Adds `import_manifest_json`/`import_manifest_hash` to a `problem_versions`
/// table that predates them (pre-v0.2.3 databases). No-op on a fresh database
/// (table doesn't exist yet — CREATE TABLE below brings it up to the current
/// shape with these columns already) and on an already-migrated one.
fn migrate_add_import_manifest_columns(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='problem_versions'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }

    let has_manifest_column = conn
        .prepare("PRAGMA table_info(problem_versions)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .any(|name| name == "import_manifest_json");
    if has_manifest_column {
        return Ok(());
    }

    let default_manifest: Vec<String> = vec!["Mathlib.Tactic.Ring".to_string(), "Mathlib.Tactic.NormNum".to_string()];
    let default_manifest_json = serde_json::to_string(&default_manifest)
        .map_err(|e| rusqlite::Error::ToSqlConversionFailure(Box::new(e)))?;
    // Same value the base manifest constant hashes to at problem_create time —
    // pre-existing rows never had an explicit manifest, so this is the correct
    // (not merely default) backfill for what they were actually checked against.
    let default_manifest_hash = crate::hashing::canonical_hash(&default_manifest)
        .map_err(|e| rusqlite::Error::ToSqlConversionFailure(Box::new(std::io::Error::new(std::io::ErrorKind::Other, e))))?;

    conn.execute(
        &format!(
            "ALTER TABLE problem_versions ADD COLUMN import_manifest_json TEXT NOT NULL DEFAULT '{}'",
            default_manifest_json.replace('\'', "''")
        ),
        [],
    )?;
    conn.execute(
        "ALTER TABLE problem_versions ADD COLUMN import_manifest_hash TEXT NOT NULL DEFAULT ''",
        [],
    )?;
    conn.execute(
        "UPDATE problem_versions SET import_manifest_hash = ?1 WHERE import_manifest_hash = ''",
        [&default_manifest_hash],
    )?;
    Ok(())
}

/// Adds `mutual_group` to an `episode_verified_module_items` table that
/// predates it (pre-mutual-recursion-support databases, issue #19). No-op on a
/// fresh database (table doesn't exist yet — CREATE TABLE below brings it up
/// to the current shape with the column already present) and on an
/// already-migrated one. A plain nullable `ALTER TABLE ADD COLUMN` suffices —
/// unlike the CHECK-constraint migrations above, no existing row's meaning
/// changes (every pre-existing row simply has no mutual group, i.e. NULL).
fn migrate_add_mutual_group_column(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='episode_verified_module_items'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }

    let has_column = conn
        .prepare("PRAGMA table_info(episode_verified_module_items)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .any(|name| name == "mutual_group");
    if has_column {
        return Ok(());
    }

    conn.execute(
        "ALTER TABLE episode_verified_module_items ADD COLUMN mutual_group INTEGER",
        [],
    )?;
    Ok(())
}

/// Adds `benchmark_problems.prover_ready_statement`/`prover_ready_statement_hash`
/// (issue #29/#31) to a pre-existing `benchmark_problems` table. Plain
/// nullable `ALTER TABLE ADD COLUMN` — no existing row's meaning changes;
/// every pre-existing row simply has no prover-ready form recorded (NULL),
/// and `benchmark_result_record`'s cross-check falls back to
/// `root_statement_hash` when it's absent.
///
/// Exists because `root_formal_statement` is a benchmark suite's own
/// faithful catalog text — for PutnamBench, that's the raw named-binder
/// declaration syntax (`theorem NAME (a : A) (b : B) : C`), which Lean 4
/// treats as sugar for a Pi-type but which is NOT itself a valid standalone
/// type expression. `problem_create`/`SubmitModule` require a single
/// self-contained type (`∀ (a : A) (b : B), C`), so the text actually
/// submitted for proving is NECESSARILY a different string than the
/// catalog's `root_formal_statement` — and therefore hashes differently.
/// Comparing `root_statement_hash` directly (as #30's original
/// anti-fabrication check did) would reject every legitimate PutnamBench
/// result. `prover_ready_statement`/`_hash` lets an importer register the
/// SAME text a runner will actually submit, so the identity check compares
/// like with like without requiring `benchmark_result_record` (suite-
/// agnostic, generic enforcement) to know any suite-specific text
/// convention.
fn migrate_add_prover_ready_statement_columns(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='benchmark_problems'",
        [],
        |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }

    let existing_columns: Vec<String> = conn
        .prepare("PRAGMA table_info(benchmark_problems)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .collect();

    if !existing_columns.iter().any(|c| c == "prover_ready_statement") {
        conn.execute("ALTER TABLE benchmark_problems ADD COLUMN prover_ready_statement TEXT", [])?;
    }
    if !existing_columns.iter().any(|c| c == "prover_ready_statement_hash") {
        conn.execute("ALTER TABLE benchmark_problems ADD COLUMN prover_ready_statement_hash TEXT", [])?;
    }
    Ok(())
}

/// Adds `benchmark_suites.trusted_canonical_source` and
/// `benchmark_results.benchmark_fidelity_basis` (issue #38's fidelity-basis
/// policy) to pre-existing tables. Plain nullable/defaulted `ALTER TABLE ADD
/// COLUMN` — no existing row's meaning changes; every pre-existing suite
/// defaults to untrusted (0), and every pre-existing result simply has no
/// recorded fidelity basis (NULL) until re-recorded.
fn migrate_add_benchmark_fidelity_basis_columns(conn: &Connection) -> rusqlite::Result<()> {
    let suites_exist: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='benchmark_suites'",
        [], |row| row.get(0),
    )?;
    if suites_exist > 0 {
        let existing_columns: Vec<String> = conn
            .prepare("PRAGMA table_info(benchmark_suites)")?
            .query_map([], |row| row.get::<_, String>(1))?
            .filter_map(|r| r.ok())
            .collect();
        if !existing_columns.iter().any(|c| c == "trusted_canonical_source") {
            conn.execute("ALTER TABLE benchmark_suites ADD COLUMN trusted_canonical_source INTEGER NOT NULL DEFAULT 0", [])?;
        }
    }

    let results_exist: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='benchmark_results'",
        [], |row| row.get(0),
    )?;
    if results_exist > 0 {
        let existing_columns: Vec<String> = conn
            .prepare("PRAGMA table_info(benchmark_results)")?
            .query_map([], |row| row.get::<_, String>(1))?
            .filter_map(|r| r.ok())
            .collect();
        if !existing_columns.iter().any(|c| c == "benchmark_fidelity_basis") {
            conn.execute("ALTER TABLE benchmark_results ADD COLUMN benchmark_fidelity_basis TEXT", [])?;
        }
        // Issue #76: structured formalization-gap categories (nullable JSON
        // array of slugs) — pre-existing rows simply have none recorded.
        if !existing_columns.iter().any(|c| c == "gap_categories_json") {
            conn.execute("ALTER TABLE benchmark_results ADD COLUMN gap_categories_json TEXT", [])?;
        }
        // Issue #92: kit-aware reporting metadata (never proof authority) —
        // which kit lemmas the attempt used (client-reported JSON array) and
        // which kit route step a failure was missing (free text).
        if !existing_columns.iter().any(|c| c == "kit_lemmas_used_json") {
            conn.execute("ALTER TABLE benchmark_results ADD COLUMN kit_lemmas_used_json TEXT", [])?;
        }
        if !existing_columns.iter().any(|c| c == "missing_route_step") {
            conn.execute("ALTER TABLE benchmark_results ADD COLUMN missing_route_step TEXT", [])?;
        }
    }
    Ok(())
}

/// Adds `action_attempts.lean_result_bytes` (issue #38's storage-bytes
/// metric) to a pre-existing `action_attempts` table. Plain nullable `ALTER
/// TABLE ADD COLUMN` — every pre-existing row simply has no byte count
/// recorded (NULL) until re-verified. `mcp_call_metrics` is a brand-new
/// table (created via `CREATE TABLE IF NOT EXISTS` above for both fresh and
/// pre-existing databases), so it needs no separate migration.
fn migrate_add_lean_result_bytes_column(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='action_attempts'",
        [], |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let existing_columns: Vec<String> = conn
        .prepare("PRAGMA table_info(action_attempts)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .collect();
    if !existing_columns.iter().any(|c| c == "lean_result_bytes") {
        conn.execute("ALTER TABLE action_attempts ADD COLUMN lean_result_bytes INTEGER", [])?;
    }
    Ok(())
}

/// Issue #12: adds benchmark_problems.goal_class + brute_force_admissible to a
/// pre-existing DB. ALTER TABLE ADD COLUMN cannot re-add the cross-column CHECK
/// (asymptotic => not brute-force-admissible); that is enforced on fresh DBs by
/// the CREATE TABLE and at the MCP handler for legacy DBs — same pattern as
/// trusted_canonical_source.
fn migrate_add_benchmark_goal_class_columns(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='benchmark_problems'",
        [], |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let cols: Vec<String> = conn
        .prepare("PRAGMA table_info(benchmark_problems)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .collect();
    if !cols.iter().any(|c| c == "goal_class") {
        conn.execute("ALTER TABLE benchmark_problems ADD COLUMN goal_class TEXT NOT NULL DEFAULT 'finite_exact'", [])?;
    }
    if !cols.iter().any(|c| c == "brute_force_admissible") {
        conn.execute("ALTER TABLE benchmark_problems ADD COLUMN brute_force_admissible INTEGER NOT NULL DEFAULT 1", [])?;
    }
    Ok(())
}

/// Issue #161: adds interactive_proof_sessions.close_reason to a DB that was
/// initialized under #160's original (161-less) column list. A no-op on a
/// genuinely fresh DB (the CREATE TABLE above already declares the column and
/// its CHECK), and on a DB that predates the table entirely (table_exists
/// check below). ALTER TABLE ADD COLUMN cannot re-add the CHECK constraint —
/// same documented limitation as goal_class/brute_force_admissible below —
/// so a legacy DB's writes are validated by the MCP handler instead.
fn migrate_add_interactive_session_close_reason_column(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='interactive_proof_sessions'",
        [], |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let cols: Vec<String> = conn
        .prepare("PRAGMA table_info(interactive_proof_sessions)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .collect();
    if !cols.iter().any(|c| c == "close_reason") {
        conn.execute("ALTER TABLE interactive_proof_sessions ADD COLUMN close_reason TEXT", [])?;
    }
    Ok(())
}

/// Issue #163: adds interactive_proof_reconstructed_scripts.tactic_path_ids_json
/// to a DB that was initialized under #160/#161's original column list. A
/// no-op on a genuinely fresh DB (the CREATE TABLE above already declares
/// the column) and on a DB that predates the table entirely (table_exists
/// check below). Same guarded ALTER TABLE ADD COLUMN pattern as
/// `migrate_add_interactive_session_close_reason_column`.
fn migrate_add_reconstructed_script_tactic_path_column(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='interactive_proof_reconstructed_scripts'",
        [], |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let cols: Vec<String> = conn
        .prepare("PRAGMA table_info(interactive_proof_reconstructed_scripts)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .collect();
    if !cols.iter().any(|c| c == "tactic_path_ids_json") {
        conn.execute(
            "ALTER TABLE interactive_proof_reconstructed_scripts ADD COLUMN tactic_path_ids_json TEXT NOT NULL DEFAULT '[]'",
            [],
        )?;
    }
    Ok(())
}

/// Issue #12: adds formalization_plan_items.asymptotic_role to a pre-existing
/// DB. The CHECK is enforced on fresh DBs (CREATE TABLE) and by the MCP handler.
fn migrate_add_plan_item_asymptotic_role_column(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='formalization_plan_items'",
        [], |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let cols: Vec<String> = conn
        .prepare("PRAGMA table_info(formalization_plan_items)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .collect();
    if !cols.iter().any(|c| c == "asymptotic_role") {
        conn.execute("ALTER TABLE formalization_plan_items ADD COLUMN asymptotic_role TEXT", [])?;
    }
    Ok(())
}

/// Issue #46: run_envelopes needs a pointer to its CURRENT cost observation so
/// the append-only observation chain has a defined head. Added by guarded
/// migration (like the columns above) so a database predating the observation
/// model gains the column instead of failing on first query.
fn migrate_add_current_cost_observation_column(conn: &Connection) -> rusqlite::Result<()> {
    let table_exists: i64 = conn.query_row(
        "SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='run_envelopes'",
        [], |row| row.get(0),
    )?;
    if table_exists == 0 {
        return Ok(());
    }
    let existing_columns: Vec<String> = conn
        .prepare("PRAGMA table_info(run_envelopes)")?
        .query_map([], |row| row.get::<_, String>(1))?
        .filter_map(|r| r.ok())
        .collect();
    if !existing_columns.iter().any(|c| c == "current_cost_observation_id") {
        conn.execute("ALTER TABLE run_envelopes ADD COLUMN current_cost_observation_id TEXT", [])?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Issue #27 (PR #58 review, blocker #2): a database whose
    /// `ingested_document_nodes` table predates the backed-status CHECK
    /// constraints is rebuilt to enforce them, and any legacy row that violates
    /// the new invariant (a backed status with no matching forward link) is
    /// sanitized to its unbacked base value during the copy.
    #[test]
    fn migrate_ingested_backed_status_checks_rebuilds_and_sanitizes_legacy_db() {
        let conn = Connection::open_in_memory().unwrap();
        conn.execute("PRAGMA foreign_keys = OFF;", []).unwrap();
        // Old-shape table: all current columns (incl. linked_formalization_plan_item_id)
        // but WITHOUT the three backed-status CHECK constraints.
        conn.execute_batch(
            "CREATE TABLE ingested_document_nodes (
                id TEXT PRIMARY KEY,
                document_id TEXT NOT NULL,
                dossier_id TEXT,
                node_order INTEGER NOT NULL,
                node_kind TEXT NOT NULL,
                natural_language_text TEXT NOT NULL,
                source_span TEXT NOT NULL,
                confidence TEXT,
                formalization_status TEXT NOT NULL DEFAULT 'prose_only',
                citation_status TEXT NOT NULL DEFAULT 'uncited',
                review_status TEXT NOT NULL DEFAULT 'unreviewed_extraction',
                risk_flags_json TEXT NOT NULL DEFAULT '[]',
                linked_external_reference_id TEXT,
                linked_external_theorem_claim_id TEXT,
                linked_research_node_id TEXT,
                linked_formalization_plan_item_id TEXT,
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                UNIQUE(document_id, node_order)
            );",
        ).unwrap();
        // A violating legacy row: citation_recorded + formalization_target_linked
        // + linked_to_dossier_artifact, all with NULL forward links (only the
        // pre-fix free-form path could produce this).
        conn.execute(
            "INSERT INTO ingested_document_nodes (id, document_id, node_order, node_kind,
                natural_language_text, source_span, formalization_status, citation_status,
                review_status, risk_flags_json, created_at, updated_at)
             VALUES ('bad', 'd1', 0, 'lemma', 'L', 'p.1', 'formalization_target_linked',
                'citation_recorded', 'linked_to_dossier_artifact', '[]', 't', 't')",
            [],
        ).unwrap();
        // A clean legacy row that must survive verbatim.
        conn.execute(
            "INSERT INTO ingested_document_nodes (id, document_id, node_order, node_kind,
                natural_language_text, source_span, formalization_status, citation_status,
                review_status, risk_flags_json, created_at, updated_at)
             VALUES ('ok', 'd1', 1, 'remark', 'R', 'p.2', 'formalization_pending',
                'uncited', 'machine_extracted', '[]', 't', 't')",
            [],
        ).unwrap();

        migrate_ingested_document_nodes_backed_status_checks(&conn).unwrap();

        // The CHECK is now baked in.
        let sql: String = conn.query_row(
            "SELECT sql FROM sqlite_master WHERE type='table' AND name='ingested_document_nodes'",
            [], |r| r.get(0),
        ).unwrap();
        assert!(sql.contains("citation_status <> 'citation_recorded'"), "migration must add the backed-status CHECK");

        // Both rows survive; the violating one is sanitized to its base values.
        let count: i64 = conn.query_row("SELECT COUNT(*) FROM ingested_document_nodes", [], |r| r.get(0)).unwrap();
        assert_eq!(count, 2);
        let (cit, form, rev): (String, String, String) = conn.query_row(
            "SELECT citation_status, formalization_status, review_status FROM ingested_document_nodes WHERE id = 'bad'",
            [], |r| Ok((r.get(0)?, r.get(1)?, r.get(2)?)),
        ).unwrap();
        assert_eq!(cit, "uncited", "orphan citation_recorded must be sanitized");
        assert_eq!(form, "prose_only", "orphan formalization_target_linked must be sanitized");
        assert_eq!(rev, "machine_extracted", "orphan linked_to_dossier_artifact must be sanitized");
        let ok_cit: String = conn.query_row(
            "SELECT formalization_status FROM ingested_document_nodes WHERE id = 'ok'", [], |r| r.get(0),
        ).unwrap();
        assert_eq!(ok_cit, "formalization_pending", "clean rows are preserved verbatim");

        // The rebuilt table now structurally rejects a raw decoupled write.
        let raw = conn.execute(
            "UPDATE ingested_document_nodes SET citation_status = 'citation_recorded' WHERE id = 'ok'", [],
        );
        assert!(raw.is_err(), "post-migration CHECK must reject citation_recorded with no linked reference/claim");

        // Idempotent: a second run is a no-op.
        migrate_ingested_document_nodes_backed_status_checks(&conn).unwrap();
        let count2: i64 = conn.query_row("SELECT COUNT(*) FROM ingested_document_nodes", [], |r| r.get(0)).unwrap();
        assert_eq!(count2, 2);
    }
}
