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
    CHECK(state NOT IN ('PROVING', 'ROOT_PROVED_COVERAGE_PENDING', 'ROOT_PROVED_COVERAGE_UNCONVERGED') OR fidelity_status IN ('verified', 'attested')),
    CHECK(state <> 'COMPLETE' OR fidelity_status = 'verified'),
    CHECK(fidelity_status IN ('unreviewed', 'attested', 'verified', 'rejected', 'revoked'))
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
    CHECK(decision IN ('verified', 'rejected'))
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
-- see the regression test in chatdb-mcp's proof_pattern tests.
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
    status TEXT NOT NULL,
    created_at TEXT NOT NULL,
    UNIQUE(plan_id, item_order),
    CHECK(kind IN ('concept', 'missing_definition', 'missing_lemma', 'planned_module', 'external_citation')),
    CHECK(mathlib_coverage_status IN ('unknown', 'found', 'not_found', 'partial')),
    CHECK(status IN ('open', 'promoted', 'dropped'))
);

-- One row per extracted move within a draft, in the order the client
-- identified them. The server never infers these itself (no inference code
-- lives in ChatDB) — the external agent proposes structured moves the same
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

-- Run envelopes (issues #34 core concept + #38 cost-surface splitting): a
-- run envelope separates WHO/WHAT/WHY around a set of episodes from the
-- episodes themselves -- host identity, run mode (a plain dev/exploratory
-- episode vs. a frozen benchmark run like PutnamBench), and host-side cost
-- accounting ChatDB itself cannot observe (MCP-visible cost_micros/budget
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
    created_at TEXT NOT NULL,
    updated_at TEXT NOT NULL,
    CHECK(mode IN ('development', 'evaluation', 'benchmark', 'private_audit', 'public_report')),
    CHECK(host_cost_confidence IN ('exact_provider_receipt', 'exact_local_meter', 'estimated', 'attested', 'unknown'))
);

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
-- ChatDB never independently verifies it, same idiom as
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
    -- PutnamBench's named-binder declaration syntax vs. the Pi-type ChatDB's
    -- model requires as a single self-contained type expression). NULL when
    -- root_formal_statement is already directly usable as-is. See
    -- migrate_add_prover_ready_statement_columns for the full rationale.
    prover_ready_statement TEXT,
    prover_ready_statement_hash TEXT,
    UNIQUE(suite_id, upstream_problem_id),
    CHECK(status IN ('imported', 'skipped_ambiguous', 'deprecated'))
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
    chatdb_commit TEXT,
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
-- ChatDB evidence" principle applied concretely: a benchmark result cannot
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
    migrate_episode_outcome_vocabulary(conn)?;
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
