# PutnamBench

Repository: https://github.com/trishullab/PutnamBench
Paper: https://arxiv.org/abs/2407.11214

PutnamBench is a set of hand-built Lean 4 (also Isabelle, and a Coq/Rocq
subset) formalizations of Putnam competition problems — 1692+ formalizations
of 640 theorems at time of the paper. It sits between ChatDB's own toy
proof-development tests and genuinely hard, research-grade mathematics:
undergraduate-competition-level statements, real Mathlib-scale imports, and
(per the paper) a track record of existing systems solving only a handful.
That combination — hard enough to be a real yardstick, small enough to
attempt with a modest budget — is why it's the first external benchmark
suite ChatDB targets for Level 3/4 readiness.

## Harness design (issue #28)

### Why this fits ChatDB's existing pieces

ChatDB already has the primitives PutnamBench needs: real Lean kernel
verification, immutable per-problem import manifests, `Solve` (one-theorem
attempts) and `SubmitModule` (defs + helper theorems + root theorem),
proof/fidelity separation, module export/replay, and trajectory export. The
PutnamBench harness's job is to drive those primitives from real benchmark
problems, not to add new proving machinery.

### Data model (already shipped — #29/#30)

Every PutnamBench concept has a home in the schema shipped in v0.3.7:

| PutnamBench concept | ChatDB table/column |
|---|---|
| the benchmark itself | `benchmark_suites` row (name="PutnamBench", `upstream_url`, `upstream_commit` = the PutnamBench repo commit this import was taken from) |
| one Putnam problem's Lean formalization | `benchmark_problems` row (`upstream_problem_id` = PutnamBench's own problem id, e.g. `putnam_1988_a1`; `root_formal_statement` + server-computed `root_statement_hash`; `import_manifest_json` = the Lean imports the formalization needs) |
| one evaluation run's configuration | `benchmark_runs` row (`solve_mode`, `allowed_tools_json`, `attempt_budget`, `wall_clock_budget_ms`, `lean_timeout_ms`; `lean_version`/`mathlib_commit` auto-read from the server's own detected environment, never client-supplied; `run_envelope_id` for host/mode/cost tracking — **required** since issue #34: "a benchmark run should not start unless a run envelope exists") |
| one problem's outcome within a run | `benchmark_results` row (`status`, `outcome`, `pass_at`, `attempts_used`, `episode_id` linking back to the real proof-search episode, cross-checked against that episode's actual recorded outcome — issue #36) |

The still-open pieces below (#29's importer, #31's runner, #32's fixtures)
are about *populating and driving* this schema, not designing new schema.

### Import shape (#29 — shipped)

Built as `crates/chatdb-mcp/examples/import_putnambench.rs`, with the
parsing logic in the library at `chatdb_proof_core::putnambench` (shared
with the future #31 runner — see below).

```
cargo run --release --example import_putnambench -- <db_path> <putnambench_repo_path> [problem_name ...]
```

Per this session's established convention for external toolchains (the same
pattern already used for `lean-checker`): a local clone of
https://github.com/trishullab/PutnamBench is a documented, one-time
developer action, never vendored into this repo's own git history. The
importer reads from that local path and does not fetch anything itself.

Verified against the real corpus at commit
`a23d8e6d4e9e3418fd78f76de7bfcb9414cbfd39` (672 `lean4/src/*.lean` files):
every file is `import Mathlib` (the whole umbrella, not curated per-module
imports — so `import_manifest` is registered as `["Mathlib"]` for every
PutnamBench problem, not a fine-grained list), followed by an optional
`open ...` line, an optional docstring, an optional
`abbrev`/`noncomputable abbrev` declaration, and exactly one
`theorem NAME ... := sorry` (zero files have more than one `theorem`
declaration). 350/672 (52%) define a companion `_solution`-style abbrev the
theorem references — those need `SubmitModule` (the abbrev's real body plus
the theorem's proof), not a bare `Solve`, since the theorem's own type
still depends on an unresolved `sorry` otherwise. The importer classifies
this per problem (`has_solution_abbrev`) so a runner can pick the right
`solve_mode`.

**A real contamination finding, caught before it shipped:** PutnamBench's
own convention for those 350 "find the answer" problems is
`abbrev X_solution := sorry` immediately followed by a `-- <the actual
closed-form answer>` line — the correct answer, spelled out as a source
comment, right next to the placeholder the prover is supposed to fill in.
PutnamBench's own extractor (`lean4/scripts/extract_to_json.py`) captures
this comment verbatim into its `lean4_statement` field, since its regex has
no notion of Lean comment syntax. A first version of this importer mirrored
that regex faithfully and would have registered the answer key directly
into `benchmark_problems.root_formal_statement` for 356/672 files — handing
any prover reading it the answer for free, the opposite of what a benchmark
import should do. Fixed: `chatdb_proof_core::putnambench::parse_problem_file`
strips both `--` line comments and `/- ... -/` block/doc comments before
storing the statement, verified against all 672 real files with zero
comment leakage (one apparent leak on manual spot-check turned out to be a
false positive — the flagged phrase, `Real.pi / 2`, is coincidentally also
part of that problem's own legitimate hypothesis, not the stripped
comment). See `test_strips_answer_key_comment_and_docstring_from_solution_abbrev_problems`.

Deliberately **not** attempted by the importer: parsing or reusing
PutnamBench's own (always `sorry`-only) proof placeholders as anything but a
statement source, and importing the non-Lean (Isabelle/Coq) formalizations —
ChatDB only verifies Lean. Files that don't match the expected shape are
skipped and reported, never silently mis-registered (none of the 672 real
files were actually skipped, but the importer is written to handle a future
PutnamBench update that adds an unexpected shape without crashing or
mis-registering it).

Two more real bugs an independent adversarial review found before this
shipped, both fixed and regression-tested against the real corpus:

- **Name extraction on a colon-adjacent theorem line.** `putnam_1993_b5.lean`
  writes `theorem putnam_1993_b5:` with no space before the colon — a naive
  `split_whitespace()` extracted `"putnam_1993_b5:"` (colon included) as the
  theorem name, silently diverging from the file-stem-derived
  `upstream_problem_id`. Fixed by splitting on any non-identifier character
  (whitespace, `:`, `(`, `{`, `[`), not just whitespace. Verified: zero
  `upstream_problem_id`/`theorem_name` mismatches across all 672 real files
  after the fix (there was exactly one before it).
- **Non-resumable batch import.** `benchmark_suites.name` is `UNIQUE`
  server-side, and the importer unconditionally called
  `benchmark_suite_create` on every invocation — a second run against the
  same db (e.g. recovering from a crash partway through a 672-problem batch)
  failed immediately at suite creation, before ever reaching the per-problem
  loop where duplicates are already handled gracefully. Fixed: the importer
  now looks up an existing `benchmark_suites` row by name directly on the
  raw connection before standing up the MCP client, reusing that `suite_id`
  if found. Verified live: running the importer twice against the same db
  with disjoint problem subsets registers both subsets under the same suite,
  with no error.

### Evaluation protocol / run manifest

Everything the issue's proposed protocol asks for either already has a
column or is intentionally out of ChatDB's scope:

| Field | Where it lives |
|---|---|
| PutnamBench commit hash | `benchmark_suites.upstream_commit` |
| Lean/Mathlib toolchain hash | `benchmark_runs.lean_version` / `.mathlib_commit` (server-detected) |
| ChatDB commit hash | `benchmark_runs.chatdb_commit` (caller-supplied — the runner should stamp its own build's commit) |
| attempt/wall-clock/Lean-time budgets | `benchmark_runs.attempt_budget` / `.wall_clock_budget_ms` / `.lean_timeout_ms` |
| whether SubmitModule / Draft+planning / librarian were allowed | `benchmark_runs.solve_mode` + `.allowed_tools_json` |
| model/agent identity outside ChatDB, prompt template hash | **Not a ChatDB column.** ChatDB verifies proofs; it does not run or template a model. This is the calling agent/host's own record-keeping (e.g. in its own logs, or as free text in `run_envelopes.notes` if host-side attribution is wanted) — deliberately not duplicated into the benchmark schema. |

### Metrics

`benchmark_run_observe` (shipped) already computes `problems_attempted`,
`solved_count`, `solved_rate`, `pass_at_1_rate`, `kernel_verified_count`,
`certified_count`, and `average_attempts_per_result` directly from
`benchmark_results`. Not yet computed (needs #31's runner to exist first,
since these require aggregating across a real run's episodes, not just the
result rows): Lean-error-category breakdown, time-to-first-success as a
run-level aggregate (the column exists per-result; a run-level percentile
view doesn't yet), cost-per-success, repair-success-rate after a first
failure, and the Solve-vs-SubmitModule success split. These are additive —
they read from data the schema already stores (`final_diagnostic_category`,
`time_to_first_success_ms`, `cost_micros`, and the episode's own trajectory)
— so they don't require new columns, just a new aggregation tool once #31
exists to generate real runs to aggregate over.

### The runner (#31 — shipped)

Built as `crates/chatdb-mcp/examples/putnam_runner.rs`. Per issue #36's
invariant ("a proof attempt that bypasses the ledger is not part of ChatDB
evidence"), its proof-search loop for each problem is exactly:
`episode_create` → `attempt_claim` → `episode_step` (chained purely off each
response's own `next_action_request`, up to `attempt_budget`, stopping at
the first `kernel_verified`/`certified`) → a final `give_up` step if the
budget is exhausted without a terminal outcome → `benchmark_result_record`.
It never calls `RealLeanGateway`/`LeanGateway::verify_exact`/`verify_module`
directly.

The runner does not generate candidate proofs itself — ChatDB has no
embedded model (see `readme_first`). Candidate `proof_term`/`answer_value`
pairs come from a caller-supplied "attempts plan" JSON file, tried in order
per problem. `solve_mode=solve_only` skips (status `skipped`) any problem
needing `SubmitModule` (i.e. one with a solution abbrev).

**A real supporting fix this required**: PutnamBench's named-binder
declaration syntax (`theorem NAME (a : A) (b : B) : C`) is not itself a
valid standalone Lean type expression — `problem_create`/`SubmitModule`
require a single self-contained type (`∀ (a : A) (b : B), C`, Lean 4's own
desugaring). `chatdb_proof_core::putnambench::to_pi_form` performs this
conversion (bracket-depth-aware, not a naive first-colon split — binders
themselves contain colons and nest brackets arbitrarily deep). Verified
against the real 672-file corpus: 670/672 (99.7%) convert successfully; the
2 failures (`putnam_1997_b5`, `putnam_2025_a6`) use Lean's pattern-matching
equation syntax for recursive function definitions (`def f : T \n | pat =>
body`), a different declaration shape not yet handled — registered anyway,
loudly logged as unable to be attempted by a runner until fixed, not
silently mis-registered. Ran the runner against 22 total real, diverse
problems (multiple years, both abbrev and non-abbrev shapes) through the
real Lean 4.32.0-rc1 + Mathlib toolchain with deliberate `sorry` attempts —
zero panics, zero unexpected infra errors, every one correctly reached
`status: "failed"` via the real gateway's own `hasSorry` diagnostic,
confirming the Pi-type conversion produces genuinely well-formed Lean, not
just something that happens to parse in unit-test fixtures.

Because the catalog's faithful `root_formal_statement` and the Pi-type text
actually submitted to `problem_create` are necessarily different strings,
`benchmark_problems` gained two more columns: `prover_ready_statement`/
`_hash`, populated by the SERVER (never the client — same principle as
every other hash in this schema) via `to_pi_form` inside
`benchmark_problem_register` itself. `benchmark_result_record`'s episode
cross-check now compares against `COALESCE(prover_ready_statement_hash,
root_statement_hash)`, so it validates against whatever text a runner
actually submitted, falling back to the original behavior for any suite/
problem needing no conversion.

**Two real bugs an independent adversarial review found and this fixed**
before shipping:
- **A severe fabrication-vector regression.** The first version accepted
  `prover_ready_statement` directly as a client-supplied argument, with zero
  check that it actually corresponded to `root_formal_statement`. A caller
  could have registered a hard theorem's `root_formal_statement` alongside
  an arbitrary, trivially-easy `prover_ready_statement` (e.g. `"True"`),
  proven the trivial one, and had `benchmark_result_record` accept it as
  evidence for the hard one — precisely the fabrication scenario issue #30
  was built to prevent, reopened by this fix's own first draft. Closed by
  removing the client-supplied field entirely: `prover_ready_statement` is
  now always derived server-side from `root_formal_statement` via
  `to_pi_form`, exactly like `root_statement_hash`/`lean_version`/
  `mathlib_commit` elsewhere in this schema. Regression test:
  `test_benchmark_problem_register_ignores_any_client_supplied_prover_ready_statement`.
- **A crash that abandoned every other queued problem.** The runner
  originally called `attempt_claim` unconditionally, THEN checked whether
  the planned attempt supplied the `answer_value` a solution-abbrev problem
  needs — if missing, it skipped the attempt without ever calling
  `episode_step`, leaving that action request stuck in `'claimed'` state.
  The next `attempt_claim` call (on the next attempt, or the give-up
  cleanup) then failed outright against the still-claimed request, and that
  error propagated straight out of `main()`, silently abandoning every
  other problem still queued in the batch. Fixed by checking
  `answer_value`'s presence BEFORE claiming, so a skipped attempt leaves the
  request untouched and claimable by the next real attempt. Verified live:
  a plan with a missing-`answer_value` problem followed by another problem
  now completes both, instead of crashing after the first.

### Smoke vs. full suite (#32 — shipped)

`benchmarks/putnambench_smoke.json` — a small, checked-in fixture file (not
fetched from a live PutnamBench clone) — embedded at compile time via
`include_str!` in `crates/chatdb-mcp/src/lib.rs`, so the smoke tests run in
every normal `cargo test` with no `CHATDB_PUTNAM_BENCH_PATH` needed. Two
kinds of fixture, per the acceptance criteria:

- **`import_fixtures`** (5 real, embedded PutnamBench problems — commit
  `a23d8e6d4e9e3418fd78f76de7bfcb9414cbfd39` — mixing abbrev and non-abbrev
  shapes, various subject tags and informal difficulty tags): verifies the
  importer's hash computation (`root_statement_hash`, `prover_ready_statement_hash`)
  is stable over time against hand-verified expected values —
  `test_putnambench_smoke_import_fixtures_register_with_stable_hashes`.
- **`canned_proof_fixtures`** (one `solve_only` success, one
  `submit_module_allowed` success, one expected-failure): deliberately
  *synthetic*, not real Putnam problems — real Putnam problems require
  genuine multi-step mathematical argument, not a one-line tactic proof, so
  plumbing tests use simple, deterministic statements instead (real
  problem-solving is reserved for the actual playtest attempt, not test
  infrastructure). Each is driven through the real `episode_step` path and
  checked against its own `expected_status` —
  `test_putnambench_smoke_canned_proof_fixtures_produce_expected_status`.
  All 3 were also verified against the real Lean 4.32.0-rc1 + Mathlib
  toolchain via `playtest.rs` (not just the fast `MockGateway` used by the
  `cargo test` versions): the two success fixtures reach `kernel_verified`
  (`termination_reason: "root_proved"`), the failure fixture is correctly
  rejected with the real gateway's own `"declaration uses \`sorry\`"`
  diagnostic.

  An adversarial review caught a real bug in the expected-failure assertion
  before this shipped: the first version only checked `outcome !=
  "kernel_verified"`, but `outcome` is JSON `null` after ANY non-terminal
  step — a genuine kernel rejection, an infra hiccup, or a malformed action
  that still parsed would all satisfy that assertion identically, so the
  committed `cargo test` regression coverage for the failure case was
  effectively vacuous (the real-gateway rejection message check above only
  ran manually via `playtest.rs`, never automatically). Fixed by asserting
  `accepted == false` — the field that actually means the verification step
  ran and was rejected — plus excluding both `"kernel_verified"` and
  `"certified"` from the allowed outcome.

The full 672-theorem suite (`import_putnambench`/`putnam_runner` against a
real local clone) is a separate, explicitly-invoked mode — never run as part
of the normal `cargo test` suite.

## Cost surfaces (issue #38 — partial)

**The product principle:** "every dollar belongs to one bucket: build the
environment, run the agent, execute the harness, verify the proof,
store/export the artifact, or unknown." `benchmark_run_observe`'s response
now includes a `cost_summary` object — honest about which of those buckets
it can actually account for today, rather than implying a total that isn't
real:

```json
"cost_summary": {
  "host_side_cost_micros": 100,
  "host_cost_confidence": "exact_local_meter",
  "mcp_side_cost_micros": null,
  "verifier_cost_ms": null,
  "storage_export_cost_micros": null,
  "unknown_external_cost": "mcp_side_cost/verifier_cost/storage_export_cost are not yet instrumented — a known gap (issue #38), never silently reported as zero",
  "cost_completeness": "host_cost_known"
}
```

`cost_completeness` is `"host_cost_known"` only when `host_cost_confidence`
is `exact_provider_receipt`/`exact_local_meter` — deliberately conservative,
matching the acceptance criterion's own wording ("unless host-side cost is
included **or exact**"). `"estimated"`/`"attested"`/`"unknown"` (and no run
envelope at all) all report `"total_cost_incomplete"`, since those aren't
the same reliability tier as a real receipt or meter reading.

**A real, previously-undiscovered gap found while designing this**:
`RealLeanGateway::verify_exact`/`verify_module` already compute
`wall_time_ms`/`lean_cpu_time_ms` on every real verification call (see
`LeanVerificationResult`) — genuine, already-measured data for exactly what
`verifier_cost` needs. But `crates/chatdb-core/src/orchestrator/step.rs`'s
`attempt_finalize` — the real, active path `episode_step` uses — only
returns the bare `LeanVerificationOutcome` enum, discarding every other
field of the result, including this timing data, before it ever reaches
anywhere persistent. So `verifier_cost` cannot yet be wired up as "sum of
already-recorded timings" the way this session's other "vestigial data"
findings worked — the data is computed but never survives past the function
that measures it. (A separate, dead, pre-`step.rs` legacy `Orchestrator` in
`orchestrator/mod.rs` DOES persist this timing — into `proposal_attempts`
via `AttemptDiagnostic`/`db::insert_attempt`, not into
`episode_budget_ledger`, which despite being a real table in the schema is
never written to by anything, anywhere — but that whole `Orchestrator` is
only ever constructed from its own `#[cfg(all(test, feature = "legacy_tests"))]`
test module, confirmed by grepping the repo for `Orchestrator::new`; it
genuinely isn't exercised by the MCP path, so there's no working reference
implementation to adapt from there either.)

Wiring this up for real requires: extending `attempt_finalize`'s return
value (or adding an out-parameter) to surface the timing fields alongside
the outcome, propagating them through `run_step_post_processing`'s
`PostProcessing` struct in `crates/chatdb-mcp/src/lib.rs`, persisting them
somewhere durable (a new `action_attempts` column, or the trajectory
event's `payload_json`), and aggregating across an episode/run for
`verifier_cost_ms`. That's a real, moderate-sized change touching multiple
function signatures across two crates — scoped out of this pass
deliberately (matching how #34's remaining tool-classification audit was
scoped out) rather than force it in at the tail of an already long session.

`mcp_side_cost`/`storage_export_cost` have no instrumentation at all yet
(no code anywhere measures ChatDB's own action-processing time or
export/storage costs) — a larger, separate design question (what's even a
meaningful unit for "MCP-side cost" — wall-clock time in the handler? action
count? — needs its own decision, not just wiring existing data through).

`environment_build_cost` vs. `benchmark_episode_cost` is already available
via `run_envelopes.mode` (`"development"` vs. `"benchmark"`/`"evaluation"`)
— a report can group/filter by mode to get this split; no new schema
needed for that half of the ask.

## Tracked vs. untracked verifier use (issue #36)

**The product principle:** a proof attempt that bypasses the episode ledger
is not part of ChatDB evidence. A benchmark run must not test candidate
proofs through a side-channel checker and then submit only the winning one
— that loses every failed attempt, the verifier diagnostics, and the cost
signals, and turns the environment into a trophy case instead of a
proof-search ledger.

**Tracked path** (the only one that produces measurable evidence):
`episode_create` → `attempt_claim` → `episode_step` with `Solve` or
`SubmitModule`. Every candidate attempt this way is recorded as a
trajectory event (hash-chained, replayable via `episode_replay`), whether
it succeeds or fails.

**Untracked path**: calling `LeanGateway::verify_exact`/`verify_module` (or
constructing a `RealLeanGateway` directly) outside that flow. This is a
legitimate *internal* primitive — the orchestrator's own
`attempt_prepare`/`attempt_finalize` split (`crates/chatdb-core/src/orchestrator/step.rs`)
uses it to actually reach Lean, and unit tests/replay internals use it in
isolation deliberately — but it is never exposed as a callable MCP tool. A
client (including `putnam_runner.rs`) has no way to invoke it directly even
if it wanted to; the *only* path any client-driven proof attempt has to
reach Lean is `episode_step`. This is enforced by construction, not by a
runtime policy check, which is why the acceptance criterion asking for "a
run-mode field that marks direct-gateway diagnostics as development-only"
doesn't need a new mechanism here: there is no code path where a client
could produce a direct-gateway diagnostic in the first place.

**Enforced concretely, closing the one real gap this session's own review
found:** `benchmark_result_record`'s cross-checks (episode-outcome match,
statement-hash match) previously only ran when an `episode_id` happened to
be given at all — a caller claiming `kernel_verified`/`certified` with **no
episode_id whatsoever** skipped every check and was accepted with zero
backing evidence, which is a strictly worse gap than the mismatched-episode
bug #30 already fixed. `benchmark_result_record` now rejects any
`kernel_verified`/`certified` claim that doesn't reference an episode
outright — see `test_benchmark_result_record_rejects_verified_claims_with_no_episode`.
Since a verified claim is now structurally impossible without a real,
matching, concluded episode, there is nothing left for a
`training_incomplete`/`benchmark_invalid` marking to catch after the fact —
the bad state can no longer be recorded in the first place, which is a
stronger guarantee than detecting it post hoc.

**Code-review guard**: `test_putnam_runner_never_references_lean_gateway_directly`
(a static source-text check, embedded at compile time) fails immediately if
`putnam_runner.rs` ever references `RealLeanGateway`/`verify_exact`/
`verify_module` in actual code — not just as a doc-comment mention of the
invariant it upholds. Explicitly scoped to this one file, not a project-wide
policy: a future sibling benchmark-runner binary would need its own guard.

**Public benchmark reports**: `benchmark_run_observe`'s response and
`proof_export(format="public_summary")` are both built entirely from
`benchmark_results`/`episodes` rows that — per the enforcement above — can
only exist if every verified claim in them passed through `episode_step`.
That is the "statement that all measured proof attempts were tracked
through MCP" the acceptance criteria asks for: it's true by construction of
what can be written to those tables, not an additional printed disclaimer.

## Contamination policy (issue #33)

The rest of this document (below) covers the contamination/redaction policy
for PutnamBench results, shipped in v0.3.8 — independent of the harness
pieces above, since redaction applies to any benchmark-linked episode
regardless of how it was created.

### Why the redaction policy matters

PutnamBench's own README asks that public confirmation settings not include
proof solutions, and asks that people not write formal proofs for benchmark
problems in public without first engaging with the maintainers — this is
meant to protect the benchmark corpus from contamination (e.g. by future
model training runs scraping public completed proofs). Leaderboard
submissions should be accompanied by a preprint or publication, coordinated
with the maintainers, not published as a side effect of running an
evaluation.

ChatDB's benchmark-tracking tools (`benchmark_suite_create`,
`benchmark_problem_register`, `benchmark_run_create`, `benchmark_result_record`,
`benchmark_run_observe` — see the README's MCP Tools table) and its
`proof_export` tool must make it hard to *accidentally* violate that policy,
while still fully supporting private verification, replay, and
maintainer-coordinated submissions.

## Contamination policy, as enforced in code

`proof_export`'s `format` (see `ExportMode` in `crates/chatdb-mcp/src/lib.rs`)
has two tiers:

- **Never exposes the completed proof body, regardless of any flag:**
  `public_summary`. Safe to call and share unconditionally — status, hashes,
  toolchain, obligation counts, replay/integrity metadata, and (if the
  episode's problem is linked to a tracked benchmark suite) the suite name
  and upstream problem id. No proof term, no assembled Lean source, no
  verified-module source.
- **May expose the completed proof body:** `markdown` (default), `lean`,
  `audit_archive`, `training_export`, `paper_dossier`, `maintainer_submission`.
  If the episode being exported is linked to a tracked benchmark suite (its
  problem_version's `root_statement_hash` matches a registered
  `benchmark_problems` row — the same comparison `benchmark_result_record`
  uses to bind results to episodes), calling `proof_export` in one of these
  modes requires `allow_putnambench_proof_export=true`. Without it, the call
  is rejected with an error pointing back to this document. This is a
  deliberate speed bump, not a technical impossibility — the same discipline
  used everywhere else in ChatDB: make the safe path the default path.

So: full proof artifacts (`markdown`/`lean`/`audit_archive`/`paper_dossier`)
are private-by-default for any problem tied to a benchmark suite; a public or
automated report generator should use `public_summary`, which needs no flag
and never leaks a proof body no matter what.

`maintainer_submission` mode is the same content tier as `audit_archive`
(full proof source, every attempt including failures) but explicitly labeled
as a package for private, direct communication with a benchmark suite's own
maintainers — never for unilateral public posting. If you solved a
PutnamBench problem and want to report it upstream, use this mode, gate it
with `allow_putnambench_proof_export=true`, and reach out to the PutnamBench
maintainers directly rather than publishing the artifact yourself.

## What "public" safely includes

Aggregate metrics, problem identifiers (`upstream_problem_id`, `theorem_name`),
statuses (`kernel_verified`/`certified`/`failed`/...), diagnostic categories,
Lean/Mathlib toolchain hashes, and replay status are all safe for public
disclosure — this is exactly what `benchmark_run_observe` and
`proof_export(format="public_summary")` report. None of it includes a
completed proof body.

## What this does not cover yet

- A dedicated report-generation tool that reads directly from
  `benchmark_results` (today, disclosure-safe reporting is per-episode via
  `proof_export`; a batch/CSV export across a whole run is part of #31/#32).
- The importer, runner, and fixtures themselves — see "Harness design" above
  for what's designed but not yet built (#29, #31, #32).
