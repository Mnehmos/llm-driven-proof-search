# ChatDB capability levels and roadmap

This document defines what ChatDB currently does, what it does not yet do, and
what has to be built next — in that order, not the reverse. Each level is
defined operationally: by required artifacts, required tools, and a concrete
test of whether the level has actually been reached, not by aspiration.

**v0.3.1 is Level 2.** Everything below Level 2 is done. Level 3 and Level 4
are open issues, not shipped features — this doc exists so a PR that adds a
feature can say which level it's building toward, instead of drifting.

## Why levels, not just a feature list

A flat issue list makes every feature look equally load-bearing. It isn't.
`SubmitModule` (Level 2) had to exist before formalization planning (Level 3)
was even worth building, because a plan that can't be checked against a real
kernel is just prose. Level 4 (research workbench) needs Level 3's
formalization planning underneath it for the same reason: a research dossier
with no path to a checked module is a wiki page, not a workbench. The level
ordering is a dependency order, not a priority ranking imposed after the fact.

## The levels

### Level 0 — kernel checker

**Definition:** Lean 4 + Mathlib can check one theorem body given to it directly.

**Status:** Done (prerequisite of everything else in this repo).

**Does NOT count:** anything that isn't an actual `lake env lean` invocation
against the pinned toolchain. No self-assessment, no "looks right."

### Level 1 — audited proof episode

**Definition:** A single theorem attempt is wrapped in an episode: typed
actions (`Solve`/`Decompose`/`GiveUp`), CAS-guarded steps, hash-chained
trajectory events, replay, and reward — proof soundness and statement
fidelity tracked as independent claims (`kernel_verified` vs `certified`).

**Required artifacts:** `episodes`, `episode_obligations`,
`episode_verified_lemmas`, trajectory events, budget ledger.

**Required tools:** `problem_create`, `episode_create`, `episode_observe`,
`attempt_claim`, `episode_step` (`Solve`/`Decompose`/`GiveUp`),
`episode_status`, `episode_close`, `trajectory_export`, `episode_replay`,
`proof_export`.

**Status:** Done. This is the environment described in the original
`CHATDB_SPEC.md` two-phase-commit / hash-chain design.

**Does NOT count:** proving a theorem outside the episode/attempt state
machine (e.g. a bare Lean file with no attempt record, no CAS check, no
trajectory event) — there'd be nothing to replay or audit.

### Level 2 — small local Lean development *(current: v0.3.1)*

**Definition:** A proof attempt can be more than one theorem body — a small
local theory of helper `def`s and helper `theorem`s plus a root theorem,
assembled by the server into one namespaced module and verified as a unit,
including declarations that must forward-reference each other.

**Required artifacts:** `episode_verified_modules`,
`episode_verified_module_items`, `AssembledModule`/`AssembledItem` (see
`crates/chatdb-core/src/lean/module.rs`).

**Required tools/actions:** `SubmitModule` action
(`LeanModuleItem::Def`/`Theorem`/`MutualGroup`), staged (all-or-nothing)
verification, DB-lock-free Lean calls, `proof_export(format="lean")`
byte-for-byte replay of a verified module.

**Required schema:** immutable per-problem `import_manifest_json`/hash (real
compile-checked, not name-shape-checked).

**Required tests/playtests:** the v0.3.1 overnight module sprint (see
`docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md`) — algebraic
inequalities, structural and well-founded recursion, list predicates, and
mutual recursion, all `kernel_verified` against the real toolchain.

**Related issues:** #1, #2, #3, #4 (foundation — closed), #19 (mutual
recursion — closed), #5, #6, #7 (bridge issues, open — see below).

**Status:** Done for the core mechanic (`SubmitModule` + mutual groups +
persistence/replay/export). The three **bridge issues** (#5, #6, #7) are
still open and sit at the Level 2 → Level 3 seam:

- **#5** — a structural-math benchmark ladder for cases `native_decide`
  brute force can't handle, i.e. proof this Level 2 mechanism scales past toy
  examples.
- **#6** — module-aware statement fidelity: a module can be root-proof
  kernel-verified while helper definitions carry a prose-only bridge (integer
  encoding, bijection, domain restriction) that fidelity review has never
  looked at. This is the semantic-skeleton/backtranslation work.
- **#7** — human-readable exposition alongside verified Lean artifacts, so a
  verified module doesn't read as "a pile of correct Lean fragments" with no
  narrative.

**Does NOT count:** proving each helper as a *separate* episode/theorem with
no shared namespace or joint verification — that's still Level 1 done twice,
not a local theory.

### Level 3 — formalization assistant

**Definition:**

```text
informal problem/proof sketch
→ extracted mathematical claims
→ required definitions/concepts
→ Mathlib coverage map
→ missing lemmas
→ planned module skeletons
→ promoted obligations
```

Level 3 is translation and planning from informal math into formal
proof-development work. **It is not discovery** — it doesn't search for new
constructions or results, it structures a plan for formalizing ones a human
or external model already has in mind.

**Required artifacts (not yet built):**
- `drafts` / `draft_moves` — an explicitly untrusted informal-planning
  artifact (issue #23). A draft can never mark anything proved.
- `formalization_plans` / `formalization_plan_items` — required concepts,
  Mathlib coverage, missing definitions/lemmas, planned modules, planned
  obligations (issue #10).
- A Mathlib librarian index beyond exact-name lookup — search by
  type/namespace/usage example, always advisory (issue #25).
- `proof_patterns` / `proof_pattern_applications` — reusable repair doctrine
  mined from real attempts, always a hint, never a status change (issue #24).

**Required tools/actions (not yet built):** `draft_create`, `draft_observe`,
`draft_extract_moves`, `formalization_plan_create_from_draft`,
`formalization_plan_promote_module_skeleton`,
`formalization_plan_promote_obligations`, `mathlib_search_declarations`,
`mathlib_search_by_type`, `mathlib_import_suggest`.

**Required boundary:** every Level 3 artifact is advisory. A draft, a plan
item, a librarian hit, or a proof pattern can shape what a client tries next,
but none of them can mark an obligation proved, change fidelity status, or
affect certification — only a real Lean kernel pass can. This mirrors the
Level 2 trust boundary (model proposes, server assembles, Lean verifies) one
level up the stack: model/plan proposes, Level 3 structures, Lean still
verifies.

**Related issues:** #10, #23, #24, #25 (core), #6 (bridge, shared with Level
2 — module-aware fidelity is a prerequisite for planning around modules
honestly).

**Level 3 MVP** (in dependency order — revised from the original draft after
reading all four issue bodies closely: #24 has no dependency on drafts or
plans at all, since it hooks into data that already exists (episode
obligations, failure lessons, attempt history), so it doesn't need to come
last):
1. **#24 — Proof-pattern memory.** ✅ Shipped in v0.3.2. Fully independent of
   drafts/plans; a reusable failure_signature → recommended_repair library,
   seeded from the v0.3.1 overnight sprint, surfaced via
   `proof_pattern_search` and recorded via `proof_pattern_record_application`
   (insert-only — never touches proof/fidelity/certification status). See
   `docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md` for the
   seed provenance.
2. **#23 + #10 — Draft artifacts and formalization plans.** ✅ Shipped
   together in v0.3.3, exactly as flagged: both issues wanted to own a
   `formalization_plans`/`formalization_plan_items` schema
   (`formalization_plan_create_from_draft` vs. `formalization_plan_create`),
   so they were designed and implemented as one feature rather than two.
   `draft_create`/`draft_observe`/`draft_extract_moves` preserve informal
   reasoning and structured moves (construction, auxiliary_lemma, case_split,
   induction, reduction, bijection, counterexample_search, asymptotic_step,
   external_citation, unknown); `formalization_plan_create` (optionally
   seeded from selected draft moves)/`_observe`/`_update`/`_add_item`/
   `_attach_lookup` track planned concepts/definitions/lemmas/modules and
   their Mathlib coverage. `formalization_plan_promote_item_to_obligation`
   only records a metadata LINK to an obligation that already exists
   (created through a normal, budget-accounted `Decompose` action) — it
   never creates one itself, mirroring #24's advisory-layer boundary. The
   vestigial `episode_drafts`/`episode_formalization_candidates` tables from
   the original pre-SubmitModule spec were left untouched (still dead code,
   noted on issue #23) — this feature uses fresh `drafts`/`draft_moves`
   tables instead, since the old ones didn't fit either issue's shape.
4. **#25 — Mathlib librarian.** ✅ Shipped in v0.3.4. Scans the REAL pinned
   Mathlib source tree (not a precomputed/offline index — a live scan of
   ~111MB takes a fraction of a second) via `mathlib_search_declarations`,
   plus `mathlib_search_local_artifacts` (this instance's own verified
   precedents) and `formalization_plan_attach_librarian_result` (feeds
   directly into #10's coverage tracking). Found and fixed three real bugs
   via end-to-end testing against the actual Mathlib checkout, not just
   inspection: a char-count-vs-byte-index panic on Unicode declaration names
   (killed the server task silently — looked like a hang, not an error), a
   modifier/attribute-prefix blind spot affecting ~80% of real files (with a
   false-confidence failure mode, not just a coverage gap), and a
   trailing-dot query degrading into a match-everything scan. See
   `docs/librarian.md`.

5. **#35 — `readme_first`.** ✅ Shipped in v0.3.5. A dedicated, zero-argument,
   first-contact tool — registered first in `list_tools` — that returns the
   proof-search protocol (the loop, the trust boundary, Solve vs
   SubmitModule guidance, why an untracked proof check doesn't count as a
   valid attempt, and the cost/benchmark-mode boundary) as static JSON, so
   any agent host (not just this session) starts from the same grounding.
6. **#34 + #38 — Run envelopes (core).** ✅ Core shipped in v0.3.6, both
   issues remain open for their full scope. `run_envelope_create/_update/
   _attach_episode/_observe` track host/model identity, run mode
   (development/evaluation/benchmark/private_audit/public_report), and
   host-side cost — reusing the pre-existing, previously-unused
   `episodes.run_id` column as the link rather than adding a redundant one.
   Still open: #34's full tool-classification audit and enforcement gates
   (only the run-envelope data model exists so far); #38's multi-surface
   cost split (only `host_side_cost_micros` is tracked — environment_build,
   mcp_side, verifier, storage_export, and unknown_external costs are not).
7. **#29 + #30 — PutnamBench suite/problem/run/result schema.** ✅ Schema +
   5 tools shipped (v0.3.7): `benchmark_suite_create`,
   `benchmark_problem_register`, `benchmark_run_create`,
   `benchmark_result_record`, `benchmark_run_observe`. Designed jointly
   since both issues wanted overlapping schema. `benchmark_run_create`
   reads `lean_version`/`mathlib_commit` from the server's own detected
   environment, never the client. `benchmark_result_record` enforces
   issue #36's invariant concretely: if `episode_id` is given, the episode
   must have actually concluded, its claimed status must match the
   episode's real recorded outcome, AND the episode must have proved the
   SAME statement as the benchmark problem (root_statement_hash match) —
   an adversarial review caught that the first version of this check only
   verified "some real verification happened," not "this one." Metrics
   distinguish `solved_rate` (solved at all within budget) from
   `pass_at_1_rate` (genuine first-attempt success) — an earlier version
   conflated the two.
8. **#33 + #37 — Contamination policy and rich `proof_export` modes.** ✅
   Shipped in v0.3.8. Designed together since #33's redaction requirement
   needed #37's export-mode mechanism to exist first. `proof_export` gained
   an explicit `ExportMode` enum: `public_summary` (never includes the
   completed proof body, regardless of any flag — status, hashes, toolchain,
   obligation counts, and suite/problem identification if benchmark-linked),
   `audit_archive` (everything `markdown` has, labeled private),
   `training_export` (structured JSON records — wires up the existing but
   previously-unused `chatdb_proof_core::orchestrator::dataset::export_rl`,
   secret-scrubbed via the newly-public `trajectories::scrub_value`),
   `paper_dossier` (adds a deterministic, templated narrative section — not
   model-generated, this function has no model access), and
   `maintainer_submission` (same tier as `audit_archive`, packaged for
   private communication with a benchmark's own maintainers). Any mode that
   can expose the completed proof body requires `allow_putnambench_proof_export=true`
   when the episode's problem is linked to a tracked benchmark suite (matched
   via `root_statement_hash`, the same comparison #30's fix uses) — see
   `docs/benchmarks/putnambench.md`. `markdown`/`lean` are unchanged
   (existing callers keep working; the field is still named `format` on the
   wire).
9. **#28 — PutnamBench harness design doc.** ✅ Shipped, docs-only, no
   version bump. See `docs/benchmarks/putnambench.md`.
10. **#29 — PutnamBench importer.** ✅ Shipped in v0.3.9. A new
    `chatdb_proof_core::putnambench` module parses PutnamBench's Lean 4
    problem files (shared with the future #31 runner, which needs the same
    `has_solution_abbrev` classification), plus a new
    `examples/import_putnambench.rs` batch-import binary, following the same
    in-process-MCP-client pattern as `examples/playtest.rs`. Verified against
    the real 672-file corpus (commit `a23d8e6d4e9e3418fd78f76de7bfcb9414cbfd39`):
    100% parse success, 100% registration success, zero comment/spoiler
    leakage, zero `theorem_name`/`upstream_problem_id` mismatches. A real
    contamination finding caught and fixed before shipping: PutnamBench's
    own convention for its ~350 "find the answer" problems is an
    `abbrev X_solution := sorry` immediately followed by the actual answer
    as a `--` comment — PutnamBench's own extractor captures this verbatim;
    ChatDB's importer strips it (and doc-comments) so `root_formal_statement`
    never leaks the answer key. An adversarial review then caught two more
    real bugs: a colon-adjacent theorem line (`theorem NAME:` with no space)
    corrupting the extracted name via naive whitespace-splitting, and the
    importer being non-resumable (an unconditional `benchmark_suite_create`
    failed outright on any re-run against the same db, since suite names are
    unique) — both fixed and regression-tested.
11. **#31 — PutnamBench pass@k runner.** ✅ Shipped in v0.3.10.
    `examples/putnam_runner.rs` drives already-imported problems through
    `episode_create` → `attempt_claim` → `episode_step` →
    `benchmark_result_record`, never calling the Lean gateway directly
    (issue #36). Candidate proofs come from a caller-supplied attempts plan
    (ChatDB has no embedded model). Required a real supporting fix:
    PutnamBench's named-binder declarations aren't valid standalone Lean
    types, so `benchmark_problems` gained server-derived
    `prover_ready_statement`/`_hash` columns (via the new
    `chatdb_proof_core::putnambench::to_pi_form`, verified against 670/672
    real problems), and `benchmark_result_record`'s cross-check now
    COALESCEs to it. Verified against 22 real problems through the real
    Lean/Mathlib toolchain — zero panics, zero unexpected errors. An
    adversarial review caught two more real bugs before shipping: a severe
    fabrication-vector regression (the first version accepted
    `prover_ready_statement` from the client with no check it actually
    corresponded to `root_formal_statement` — closed by making it always
    server-derived, never client-supplied), and a crash that silently
    abandoned every other queued problem in a batch (an `attempt_claim`
    called before checking whether a planned attempt supplied what it
    needed, leaving the action request stuck `'claimed'` and the next claim
    call's error propagating out of `main()`). See
    `docs/benchmarks/putnambench.md` for full detail.
12. **#32 — PutnamBench smoke subset and golden fixtures.** ✅ Shipped in
    v0.3.11. `benchmarks/putnambench_smoke.json` — 5 real, embedded
    PutnamBench problems (import-fidelity fixtures, hash-verified stable
    over time) plus 3 deliberately synthetic canned-proof fixtures (one
    `solve_only` success, one `submit_module_allowed` success, one
    expected-failure) — embedded at compile time via `include_str!`, so
    `test_putnambench_smoke_import_fixtures_register_with_stable_hashes` and
    `test_putnambench_smoke_canned_proof_fixtures_produce_expected_status`
    run in every normal `cargo test` with no external clone needed. All 3
    canned-proof fixtures separately verified against the real Lean
    4.32.0-rc1 + Mathlib toolchain via `playtest.rs`.

**Status:** Level 3 MVP complete. #24 shipped (v0.3.2). #23 + #10 shipped
together (v0.3.3). #25 shipped (v0.3.4). #35 shipped (v0.3.5). #34+#38 core
shipped (v0.3.6). #29+#30 schema shipped (v0.3.7). #33+#37 shipped (v0.3.8).
#28 shipped, docs-only. #29 (importer) shipped (v0.3.9). #31 (runner) shipped
(v0.3.10). #32 (smoke fixtures) shipped (v0.3.11). #36 shipped (v0.3.12).
#34 partial shipped (v0.3.13). #38 partial (cost-completeness) shipped
(v0.3.14). #38 partial (real verifier_cost wiring) shipped (v0.3.15). #34
partial (bounded 13/42-tool classification audit, found and fixed a real
trajectory_export contamination gap) shipped (v0.3.16). #34 partial (14 more
tools classified, 27/42 total, found the model_call_leases cost-aggregation
gap and left it as an open design question) shipped (v0.3.17). #34's
tool-classification audit reached 42/42 COMPLETE (found the episode_observe
non-idempotence and problem_submit_fidelity_review/benchmark_results
staleness findings) shipped (v0.3.18). #41 (multi-line proof_term tactic-
block splicing, found via the playtest below) fixed at the source and
CLOSED, including a real gap an adversarial review caught in the first pass
(the SubmitModule root theorem was still exposed to the bug) shipped
(v0.3.19). The full PutnamBench sprint is complete, and the first real
playtest attempt has run: 12 real
problems, 1/12 (8.3%) pass@1 — see
`docs/playtests/2026-07-04-putnambench-first-attempt.md`. Zero infra errors,
zero panics, correct enforcement throughout; the constraint was genuine
mathematical effort per problem, not the environment. One real environment
finding from the attempt — a multi-line `proof_term` can silently break
tactic-block parsing with a misleading error — filed as issue #41.

**#41 — fix multi-line `proof_term` tactic-block splicing.** ✅ Shipped in
v0.3.19, CLOSED. Root cause (confirmed empirically against the real Lean
4.32.0-rc1 + Mathlib toolchain, both before and after): Lean 4's tactic-block
parser is whitespace-sensitive — every line at the SAME column as a block's
first tactic is a sequential sibling; a line indented MORE than that is
parsed as NESTED under the preceding tactic, not as its sibling.
`crates/chatdb-core/src/lean/mod.rs` (the `Solve` path) and
`crates/chatdb-core/src/lean/module.rs` (the `SubmitModule` path) both took a
client-supplied multi-line string and blindly prepended a fixed 2-space
indent to EVERY line regardless of the client's own per-line indentation —
so a naturally-formatted proof ("first tactic flush, rest indented" — a very
common human/LLM style) ended up with its later lines parsed as nested under
the first, not sequential after it, producing the exact misleading
"introN failed" error from the original report. A proof whose lines were
ALREADY uniformly indented worked fine even before this fix (uniform +
uniform offset stays uniform) — confirmed empirically as the control case.
Fix: a new `normalize_and_indent` function in `module.rs` — if a proof
term's lines already share one indentation level, preserve it exactly
(byte-for-byte identical to the old behavior for this case); otherwise,
flatten every line to one level before applying the base indent, since a
non-uniformly-indented multi-line term had a 0% success rate before this fix
regardless, so flattening can only ever help. The old `indent()` function is
deliberately kept for the ONE remaining call site that re-indents an
already-assembled, intentionally non-uniform multi-declaration `mutual`-group
block by a further structural level — applying the new normalization there
would wrongly flatten real, correct nesting. An adversarial review of the
first pass of this fix found a real, missed instance: `assemble_module`'s
root-theorem rendering still called the old, unfixed `indent()` directly
instead of going through `render_theorem`/`normalize_and_indent` like every
other item — meaning a `SubmitModule` action's root theorem (the actual goal
being proved) was still exposed to the bug. Fixed by routing it through
`render_theorem` like everything else, with a dedicated regression test
(`assemble_module_normalizes_root_theorem_proof_term_indentation`) added to
catch a repeat. Verified against the real toolchain for all three paths
(`Solve` repro, `Solve` uniform control, `SubmitModule` repro) via a new
checked-in fixture,
`crates/chatdb-mcp/examples/regression_scripts/issue41_multiline_proof_term.json` —
all three reach `kernel_verified`. 4 new unit tests directly exercise
`normalize_and_indent`'s uniform/non-uniform/single-line/blank-line
behavior. A second adversarial review pass, specifically re-checking the
root-theorem fix, confirmed it correct and independently re-ran the fixture
against the real toolchain.

**#36 — require measured proof attempts to flow through `episode_step`.** ✅
Shipped in v0.3.12. Found and closed a real gap while formalizing this
already-mostly-true invariant: `benchmark_result_record`'s anti-fabrication
checks (from #30) only ran when an `episode_id` happened to be supplied at
all — a caller claiming `kernel_verified`/`certified` with no `episode_id`
whatsoever skipped every check and was accepted with zero backing evidence.
Now rejected outright. Also added a static code-review guard
(`test_putnam_runner_never_references_lean_gateway_directly`) proving the
runner never calls `RealLeanGateway`/`verify_exact`/`verify_module`
directly, and a "Tracked vs. untracked verifier use" doc section in
`docs/benchmarks/putnambench.md`. The remaining acceptance criteria (a
run-mode field marking direct-gateway diagnostics dev-only, and
`training_incomplete`/`benchmark_invalid` run-marking) turned out to be
structurally unnecessary once the core gap closed: the gateway is never
exposed as an MCP tool at all (so no client-driven diagnostic can originate
outside `episode_step`), and a verified claim is now impossible to record
without a real backing episode, leaving nothing for a post-hoc marking
mechanism to catch.

**#34 (partial) — require a run envelope before a benchmark run.** ✅
Shipped in v0.3.13, one small bounded slice of #34's larger scope (the full
42-tool classification audit and benchmark-mode source-mutation guardrails
remain open — see below). `benchmark_run_create`'s `run_envelope_id` is now
a required field, not optional — enforced both in the wire schema
(`String`, not `Option<String>`) and by the handler still checking the
referenced envelope actually exists. `putnam_runner.rs` now calls
`run_envelope_create` (mode `"benchmark"`) once before creating its run.
Two independent adversarial reviews in a row (this fix and #36's) found no
real bugs — the first clean streak this session, plausible for smaller,
well-scoped changes building on already-established patterns.
Still open on #34: the full per-tool metadata classification (side effect,
trust level, cost surface, benchmark safety, replayability), and
benchmark-mode guardrails against source-code mutation (moot for ChatDB's
actual tool surface today — there is no MCP tool that edits source files —
but worth revisiting if one is ever added).

**#34 (partial, follow-up) — bounded tool-classification audit slice.** ✅
Shipped in v0.3.16: a genuine (not padded) per-tool classification, across
the issue's 8 dimensions (side_effect, trust_level, cost_surface,
benchmark_safety, replayability, source_code_impact, artifact_risk,
required_run_mode), for 13 of the 42 tools — surfaced in
`environment_describe`'s new `tool_classification` field, explicit that a
tool's absence from the map is "not yet classified," never "safe by
omission." Doing this analysis found and fixed a real, live bug:
`trajectory_export` returns each event's raw `payload_json`, which for a
`solve`/`submit_module` action includes the exact completed-proof-body
content issue #33's contamination policy gates in `proof_export` — but
`trajectory_export` had no equivalent gate at all, an ungated side channel
around that policy for any benchmark-linked episode. Fixed by adding the
same `allow_putnambench_proof_export` flag and the same
`benchmark_suite_name_for_episode` check `proof_export` already uses.
Verified against the real Lean 4.32.0-rc1 + Mathlib toolchain via
`playtest.rs`. An adversarial review found no code bugs and independently
confirmed two other findings recorded in the classification itself as open
questions rather than fixes: `benchmark_result_record` cross-checks
statement identity but not a problem's `fidelity_status`, and
`unsafe_dev_attestation`'s dev-only naming isn't actually enforced against a
run's declared mode — both deliberately left as documented, undecided
boundaries rather than silently patched. Still open on #34: 29 of 42 tools
remain unclassified, and the benchmark-mode source-mutation guardrail
remains moot as before.

**#34 (partial, second follow-up slice) — 14 more tools classified.** ✅
Shipped in v0.3.17: `model_call_reserve`, `model_call_settle`,
`run_envelope_update`, `run_envelope_attach_episode`, `run_envelope_observe`,
all 7 `formalization_plan_*` tools, and `mathlib_search_declarations`/
`mathlib_search_local_artifacts` — bringing the classified total from 13 to
27 of 42. This slice's most notable finding, deliberately left as a
documented `unresolved_design_question` rather than silently wired in:
`model_call_leases` (populated by `model_call_reserve`/`model_call_settle`)
already stores a granular, per-attempt, self-reported cost figure
(`reserved_cost_micros`/`actual_cost_micros`) that `benchmark_run_observe`'s
`cost_summary` never aggregates or surfaces at all today — structurally
similar to the `verifier_cost_ms` gap v0.3.15 fixed, but NOT the same kind of
fix: that data is `untrusted_input` (self-reported by the caller, never
measured by ChatDB), so folding it into `cost_summary` first requires
deciding how its trust tier interacts with `host_cost_confidence`'s existing
exact/estimated/attested/unknown vocabulary — a real design question, not a
mechanical copy of the verifier_cost pattern. Two more `NOT replayable in
the audit sense` findings noted (mirroring `run_envelope_update`'s from the
first slice): `formalization_plan_update` also overwrites title/status/
risk_flags in place with no history. The single giant `environment_describe`
`serde_json::json!` literal exceeded the default macro recursion limit once
this many tool entries were added — fixed with `#![recursion_limit = "512"]`
at the crate root (an adversarial review bisected the actual requirement at
128–192 and found 512 comfortably headroomed, not arbitrary, given the audit
isn't done growing this literal yet). The `environment_describe` test was
also strengthened from a 5-tool spot-check to asserting all 8 dimensions
non-empty across every classified entry. Verified against the real Lean
4.32.0-rc1 + Mathlib toolchain via `playtest.rs`. Adversarial review found no
code bugs and independently re-verified five of the new entries' claims
directly against handler/schema code. Still open on #34: 15 of 42 tools
remain unclassified, plus everything already noted as open from the first
slice.

**#34 — tool-classification audit: 42/42 COMPLETE.** ✅ Shipped in v0.3.18,
the third and final slice, classifying the remaining 15 tools: `readme_first`,
`environment_describe`, `problem_submit_fidelity_review`, `problem_list`,
`episode_reset`, `episode_observe`, `episode_status`, `episode_close`,
`proof_pattern_search`, `proof_pattern_record_application`, `draft_observe`,
`draft_extract_moves`, `benchmark_suite_create`, `benchmark_problem_register`,
`lean_declaration_lookup`. Every MCP tool ChatDB exposes now has a real,
grounded classification entry — `classified_tool_count`/`total_tool_count`
are both tied to the actual registered tool list (`list_res.tools.len()`),
not a hand-maintained figure that could silently drift. Two notable,
non-obvious findings from this slice: `episode_observe` is classified
`mutating`, not `read_only`, despite its name — it recovers expired attempt
claims/action requests and can mint a genuinely new action_request before
returning, so two consecutive calls aren't guaranteed to return the same
request id; and `problem_submit_fidelity_review` can retroactively upgrade
an already-terminal episode's outcome from `kernel_verified` to `certified`
(and the problem's state to `COMPLETE`) after the fact, which can leave a
previously-recorded `benchmark_results` row silently stale (still reporting
`kernel_verified` after the underlying episode was promoted to `certified`)
since `benchmark_result_record` has no mechanism to re-check a result once
recorded. Both independently confirmed by adversarial review, which found no
code bugs in this slice. Verified against the real Lean 4.32.0-rc1 + Mathlib
toolchain via `playtest.rs`.
**Note on what "complete" means here**: `classified_tool_count ==
total_tool_count` now, but classification is a snapshot, not a standing
guarantee — it needs re-checking as tools change, and several entries record
open design questions rather than closed answers (`unresolved_design_question`
fields on `benchmark_result_record`, `problem_create`, `run_envelope_attach_episode`,
`model_call_reserve`). Of #34's other acceptance criteria: the read-me-first
tool (`readme_first`) and the docs on trust boundary/cost surfaces were
already in place before this audit; the run-envelope requirement shipped in
v0.3.13; the benchmark-mode source-mutation guardrail remains moot (no MCP
tool edits source files); the cost accounting fields
(`host_side_cost`/`verifier_cost`/`mcp_side_cost`/`storage_cost`) are still
only partially wired (see #38 below) — full closure of #34 is still gated on
that cost-accounting work and a decision on the two lingering design
questions above.

**#38 (partial) — cost-completeness marking for benchmark reports.** ✅
Shipped in v0.3.14, one small bounded slice of #38's larger 7-bucket ask
(see `docs/benchmarks/putnambench.md`'s "Cost surfaces" section for the
full breakdown of what's tracked vs. not). `benchmark_run_observe` now
returns a `cost_summary` object: `host_side_cost_micros`/
`host_cost_confidence` (already-existing `run_envelopes` data), a derived
`cost_completeness` (`"host_cost_known"` only for `exact_provider_receipt`/
`exact_local_meter` confidence, else `"total_cost_incomplete"` — matching
the acceptance criterion's own "unless host-side cost is included or
*exact*" wording), and `mcp_side_cost_micros`/`verifier_cost_ms`/
`storage_export_cost_micros` explicitly reported as `null` (never
fabricated as zero) with a documented reason. An adversarial review caught
one real doc inaccuracy (a wrong table name in the explanation of why the
legacy orchestrator path can't be reused) but no code bugs.

**#38 (partial, follow-up) — real `verifier_cost_ms` wiring.** ✅ Shipped in
v0.3.15. v0.3.14 found that `RealLeanGateway` already computes real
`wall_time_ms`/`lean_cpu_time_ms` on every verification call, but the active
`step.rs`/`attempt_finalize` path discarded it before it reached anywhere
persistent — expected to need a signature change across `step.rs` and
`lib.rs`. That expectation turned out wrong once in the code:
`attempt_finalize` already receives the full `GatewayResponse`, so the real
result is now serialized and persisted onto the existing, previously-never-
written `action_attempts.lean_result_json` column entirely within the
existing function body, no signature change needed anywhere.
`benchmark_run_observe` sums `wall_time_ms` across every attempt on every
episode a run's results reference into `cost_summary.verifier_cost_ms` —
real data when present, `null` (never `0`) otherwise. Verified against the
real Lean 4.32.0-rc1 + Mathlib toolchain via `playtest.rs` (a real
`True`/`trivial` episode produced `verifier_cost_ms: 9482`, genuine
wall-clock milliseconds). An adversarial review found no code bugs — one
pre-existing, non-introduced modeling nuance noted (an episode's
`action_attempts` aren't scoped to a single run, so if the same episode were
ever referenced by results in two different runs, both would independently
report the full real time — deemed acceptable since it isn't fabrication,
just not run-exclusive, and isn't how episodes/runs are normally created).
Still open for #38: `mcp_side_cost`/`storage_export_cost` remain fully
uninstrumented, with no decided unit of measurement yet.

**Does NOT count:** an LLM freehand-writing a formalization plan in its
response text with no ChatDB-tracked artifact, no promotion path to a
`SubmitModule` skeleton, and no record of what Mathlib coverage was actually
checked versus assumed.

### Level 4 — research workbench

**Definition:**

```text
research dossier
candidate constructions
small-case / counterexample search
external theorem / citation boundaries
multi-layer proof status
expert review artifacts
```

Level 4 is a durable workspace where serious mathematical attempts (the kind
that span days, cite external results, and need small-case computational
search before anyone commits to a proof strategy) can be searched,
structured, reviewed, and partially formalized without losing provenance.
**It is not autonomous theorem discovery** — a human or external model still
drives the search; Level 4 makes sure that search leaves a durable, honest
trail instead of disappearing into chat scrollback.

**Required artifacts (not yet built):** research dossiers (#9), candidate
construction artifacts (#8), external theorem/citation/assumption boundary
records (#11), asymptotic statement support (#12), multi-layer verification
status (#13), expert-review artifacts and a role-separated ledger (#14),
empirical math lab for small-case/counterexample/construction search (#26),
paper/PDF ingestion with citation and gap tracking (#27).

**Required boundary:** an external citation is a tracked assumption, never a
substitute for a Lean proof of the cited fact — Level 4 must make clear which
parts of a research attempt are kernel-verified versus cited versus still
open, at all times, not just at the end.

**Related issues:** #8, #9, #11, #12, #13, #14, #26, #27 (core), #7 (bridge,
shared with Level 2 — exposition matters even more once a dossier spans
citations and partial results).

**Level 4 MVP:**
1. #8 — Candidate constructions
2. #9 — Research dossiers
3. #11 — Citation boundaries
4. #26 — Empirical math lab
5. #27 — Paper ingestion

**Serious research-grade version** (beyond MVP): #12 (asymptotics), #13
(multi-layer verification), #14 (expert review).

**Status:** Not started. Fully open, and blocked on Level 3's formalization
planning existing first — a research dossier with no formalization-planning
layer underneath it has no path from "candidate construction" to "checked
module."

**Does NOT count:** a research dossier that only stores prose notes with no
link to any Lean artifact, obligation, or formalization plan item — that's a
wiki, not a workbench.

### Level 5 — discovery loop

**Definition (forward-looking, not yet scoped into issues):** the system
proposes its own candidate constructions or conjectures, not just structures
ones a human/model already brought to it, and can run many candidates through
the Level 3/4 machinery to see which survive.

**Status:** Not scoped. No issues yet. Do not start building this before
Level 3 and Level 4 are real — a discovery loop generating plans that nothing
downstream can formalize or search around is pure motion.

### Level 6 — serious math collaborator

**Definition (forward-looking):** the full loop — discovery, formalization
planning, research-workbench provenance, and expert review — operating
together on genuinely open problems (the "tackle Putnam and Erdős problems"
goal), with every claim traceable back to either a Lean kernel pass or an
explicitly tracked, reviewed external citation.

**Status:** Not scoped. This is the destination the other levels are built
toward, not a near-term milestone.

## Issue-to-level map

| Level | Core issues | Bridge issues (shared with adjacent level) |
|---|---|---|
| 1 | #1–#4 (closed) | — |
| 2 | #19 (closed) | #5, #6, #7 (open) |
| 3 | #10, #23, #24, #25, #34, #35, #38 | #6 (shared with 2) |
| 4 | #8, #9, #11, #12, #13, #14, #26, #27 | #7 (shared with 2) |
| PutnamBench sprint | #28, #29, #30, #31, #32, #33, #36, #37 | #34, #38 (shared with 3) |
| docs/roadmap | #20, #21, #22 | — |

## What this roadmap is not

This is not a commitment to build every issue listed here in order, and it is
not a substitute for reading the individual issues before starting one — each
has its own acceptance criteria and required regression tests. It exists so
that before an agent or contributor starts a Level 3 or Level 4 feature, they
can check: does the thing underneath this already exist? If Level 2's
bridge issues (#5–#7) or the Level 3 MVP order above aren't satisfied yet,
that's a sign to build the prerequisite first, not to skip ahead.
