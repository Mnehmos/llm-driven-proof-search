# PutnamBench

Repository: https://github.com/trishullab/PutnamBench
Paper: https://arxiv.org/abs/2407.11214

PutnamBench is a set of hand-built Lean 4 (also Isabelle, and a Coq/Rocq
subset) formalizations of Putnam competition problems — 1692+ formalizations
of 640 theorems at time of the paper. It sits between LLM-Driven Proof Search Environment's own toy
proof-development tests and genuinely hard, research-grade mathematics:
undergraduate-competition-level statements, real Mathlib-scale imports, and
(per the paper) a track record of existing systems solving only a handful.
That combination — hard enough to be a real yardstick, small enough to
attempt with a modest budget — is why it's the first external benchmark
suite LLM-Driven Proof Search Environment targets for Level 3/4 readiness.

## Harness design (issue #28)

### Why this fits LLM-Driven Proof Search Environment's existing pieces

LLM-Driven Proof Search Environment already has the primitives PutnamBench needs: real Lean kernel
verification, immutable per-problem import manifests, `Solve` (one-theorem
attempts) and `SubmitModule` (defs + helper theorems + root theorem),
proof/fidelity separation, module export/replay, and trajectory export. The
PutnamBench harness's job is to drive those primitives from real benchmark
problems, not to add new proving machinery.

### Data model (already shipped — #29/#30)

Every PutnamBench concept has a home in the schema shipped in v0.3.7:

| PutnamBench concept | LLM-Driven Proof Search Environment table/column |
|---|---|
| the benchmark itself | `benchmark_suites` row (name="PutnamBench", `upstream_url`, `upstream_commit` = the PutnamBench repo commit this import was taken from) |
| one Putnam problem's Lean formalization | `benchmark_problems` row (`upstream_problem_id` = PutnamBench's own problem id, e.g. `putnam_1988_a1`; `root_formal_statement` + server-computed `root_statement_hash`; `import_manifest_json` = the Lean imports the formalization needs) |
| one evaluation run's configuration | `benchmark_runs` row (`solve_mode`, `allowed_tools_json`, `attempt_budget`, `wall_clock_budget_ms`, `lean_timeout_ms`; `lean_version`/`mathlib_commit` auto-read from the server's own detected environment, never client-supplied; `run_envelope_id` for host/mode/cost tracking — **required** since issue #34: "a benchmark run should not start unless a run envelope exists") |
| one problem's outcome within a run | `benchmark_results` row (`status`, `outcome`, `pass_at`, `attempts_used`, `episode_id` linking back to the real proof-search episode, cross-checked against that episode's actual recorded outcome — issue #36) |

The still-open pieces below (#29's importer, #31's runner, #32's fixtures)
are about *populating and driving* this schema, not designing new schema.

### Import shape (#29 — shipped)

Built as `crates/proofsearch-mcp/examples/import_putnambench.rs`, with the
parsing logic in the library at `proofsearch_core::putnambench` (shared
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
import should do. Fixed: `proofsearch_core::putnambench::parse_problem_file`
strips both `--` line comments and `/- ... -/` block/doc comments before
storing the statement, verified against all 672 real files with zero
comment leakage (one apparent leak on manual spot-check turned out to be a
false positive — the flagged phrase, `Real.pi / 2`, is coincidentally also
part of that problem's own legitimate hypothesis, not the stripped
comment). See `test_strips_answer_key_comment_and_docstring_from_solution_abbrev_problems`.

Deliberately **not** attempted by the importer: parsing or reusing
PutnamBench's own (always `sorry`-only) proof placeholders as anything but a
statement source, and importing the non-Lean (Isabelle/Coq) formalizations —
LLM-Driven Proof Search Environment only verifies Lean. Files that don't match the expected shape are
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
column or is intentionally out of LLM-Driven Proof Search Environment's scope:

| Field | Where it lives |
|---|---|
| PutnamBench commit hash | `benchmark_suites.upstream_commit` |
| Lean/Mathlib toolchain hash | `benchmark_runs.lean_version` / `.mathlib_commit` (server-detected) |
| LLM-Driven Proof Search Environment commit hash | `benchmark_runs.proofsearch_commit` (caller-supplied — the runner should stamp its own build's commit) |
| attempt/wall-clock/Lean-time budgets | `benchmark_runs.attempt_budget` / `.wall_clock_budget_ms` / `.lean_timeout_ms` |
| whether SubmitModule / Draft+planning / librarian were allowed | `benchmark_runs.solve_mode` + `.allowed_tools_json` |
| model/agent identity outside LLM-Driven Proof Search Environment, prompt template hash | **Not a LLM-Driven Proof Search Environment column.** LLM-Driven Proof Search Environment verifies proofs; it does not run or template a model. This is the calling agent/host's own record-keeping (e.g. in its own logs, or as free text in `run_envelopes.notes` if host-side attribution is wanted) — deliberately not duplicated into the benchmark schema. |

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

Built as `crates/proofsearch-mcp/examples/putnam_runner.rs`. Per issue #36's
invariant ("a proof attempt that bypasses the ledger is not part of LLM-Driven Proof Search Environment
evidence"), its proof-search loop for each problem is exactly:
`episode_create` → `attempt_claim` → `episode_step` (chained purely off each
response's own `next_action_request`, up to `attempt_budget`, stopping at
the first `kernel_verified`/`certified`) → a final `give_up` step if the
budget is exhausted without a terminal outcome → `benchmark_result_record`.
It never calls `RealLeanGateway`/`LeanGateway::verify_exact`/`verify_module`
directly.

The runner does not generate candidate proofs itself — LLM-Driven Proof Search Environment has no
embedded model (see `readme_first`). Candidate `proof_term`/`answer_value`
pairs come from a caller-supplied "attempts plan" JSON file, tried in order
per problem. `solve_mode=solve_only` skips (status `skipped`) any problem
needing `SubmitModule` (i.e. one with a solution abbrev).

**A real supporting fix this required**: PutnamBench's named-binder
declaration syntax (`theorem NAME (a : A) (b : B) : C`) is not itself a
valid standalone Lean type expression — `problem_create`/`SubmitModule`
require a single self-contained type (`∀ (a : A) (b : B), C`, Lean 4's own
desugaring). `proofsearch_core::putnambench::to_pi_form` performs this
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
`include_str!` in `crates/proofsearch-mcp/src/lib.rs`, so the smoke tests run in
every normal `cargo test` with no `PROOFSEARCH_PUTNAM_BENCH_PATH` needed. Two
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

## Cost surfaces (issue #38 — cost policy v2)

**The product principle, restated after real design direction (v0.3.20):**
metrics first, money second. Time/count/byte fields are real measurements
LLM-Driven Proof Search Environment attempts honestly regardless of whether any money is involved;
`*_cost_micros` fields are monetary and stay `null` unless real money data
(a provider receipt, a local meter, a self-report, or a rate card) actually
exists. `null` always means "not measured" — never `0`. `benchmark_run_observe`'s
response includes a `cost_summary` object with this full shape:

```json
"cost_summary": {
  "host_side_cost_micros": 1000,
  "host_cost_confidence": "exact_local_meter",
  "model_call_reported_cost_micros": 350,
  "model_call_cost_confidence": "attested",
  "verifier_wall_time_ms": 57245,
  "verifier_cpu_time_ms": 57245,
  "mcp_action_count": 1,
  "mcp_handler_wall_time_ms": 9620,
  "mcp_side_cost_micros": null,
  "storage_bytes_written": 568,
  "storage_export_bytes": 870,
  "storage_export_wall_time_ms": 0,
  "storage_export_cost_micros": null,
  "known_exact_cost_micros": 1000,
  "reported_attested_cost_micros": 350,
  "estimated_cost_micros": null,
  "unknown_cost_present": true,
  "cost_completeness": "reported_total_not_exact",
  "not_yet_instrumented": "mcp_side_cost_micros/storage_export_cost_micros are not yet instrumented — never reported as zero; there is no pricing/rate-card decision yet for either surface. mcp_handler_wall_time_ms/storage_bytes_written/storage_export_bytes/storage_export_wall_time_ms are now real, measured metrics — null only when this run genuinely has no correlated data yet, never fabricated as zero. model_call_reported_cost_micros is real per-attempt data from model_call_leases but always self-reported (attested), never independently measured by LLM-Driven Proof Search Environment."
}
```

**Field meanings, by unit:**

- `*_cost_micros` — money. `host_side_cost_micros`/`host_cost_confidence` come
  from `run_envelopes` (unchanged). `model_call_reported_cost_micros` is:
  real per-attempt cost data folded in from `model_call_leases` (reserved by
  `model_call_reserve`, settled or voided by `model_call_settle` or the
  same-attempt `episode_step` auto-settle path), summed only over `status='settled'
  AND actual_cost_micros IS NOT NULL` rows — a reserved-but-never-settled
  lease is still only a reservation and contributes nothing to reported actual
  cost, never a phantom `0`. A voided lease refunds its reservation and also
  contributes no actual cost. Settled actual costs are ALWAYS reported at
  `"attested"` confidence (`model_call_cost_confidence`), since they are entirely
  self-reported by the runner/host and never independently measured or
  receipted by LLM-Driven Proof Search Environment — they are never merged into an exact total.
  `mcp_side_cost_micros`/`storage_export_cost_micros` stay `null` until a real
  meter or an explicit rate card exists for LLM-Driven Proof Search Environment's own compute/storage —
  there is none today, and these two fields are the ONLY ones this policy
  never converts a metric into a dollar figure for (see "MCP/storage
  observability" below — the metrics ARE real now, the prices are not).
- `*_wall_time_ms`/`*_cpu_time_ms` — real time, not money.
  `verifier_wall_time_ms`/`verifier_cpu_time_ms` sum real
  `wall_time_ms`/`lean_cpu_time_ms` persisted on `action_attempts.lean_result_json`
  (see below) across every attempt on every episode a run's results
  reference — each tracked with its own "any data found" flag, since the
  `SubmitModule` path's result type has no cpu-time field at all.
  `mcp_handler_wall_time_ms`/`storage_export_wall_time_ms` are now real,
  measured metrics too (see below).
- `mcp_action_count` — a real count, never null (0 is a genuine count, not
  a stand-in for "unmeasured"): the number of `action_attempts` rows across
  the run's episodes.
- `*_bytes` — `storage_bytes_written`/`storage_export_bytes` are now real
  byte counts too (see below).

### MCP/storage observability (issue #38, v0.3.23)

The previously-deferred metrics (`mcp_handler_wall_time_ms`,
`storage_bytes_written`, `storage_export_bytes`, `storage_export_wall_time_ms`)
are now real, measured instrumentation — still metrics, never converted into
a dollar figure without a real pricing profile (there is none today, so
`mcp_side_cost_micros`/`storage_export_cost_micros` stay `null`, and
`cost_completeness` remains unable to reach `"total_cost_known"` regardless).

**How it works:** a new `mcp_call_metrics` table logs EVERY MCP tool call —
success or failure, since a genuine handler-time accounting must include
rejected/invalid calls too, not just clean successes — with real wall-clock
time, the real byte length of the returned content, and best-effort
correlation IDs (`episode_id`/`run_id`/`run_envelope_id`) duck-typed
generically out of whatever fields the specific tool's own args happen to
contain, with no per-tool special casing needed. `benchmark_run_observe`
aggregates `mcp_handler_wall_time_ms` across every logged call correlated to
a run (by episode, by run id, or by run envelope id — a call matching more
than one is still only counted once), and `storage_export_bytes`/
`storage_export_wall_time_ms` the same way but restricted to `proof_export`/
`trajectory_export` calls specifically. `storage_bytes_written` sums a new
`action_attempts.lean_result_bytes` column — the real byte length (Rust
`String::len()`, never SQLite's own character-counting `LENGTH()`, which
would undercount Lean/Mathlib's multi-byte math notation like `∀`/`≥`/`⟨⟩`)
of the same `lean_result_json` already persisted per attempt.

**A real, critical bug an adversarial review caught and a fix verified
against**: the metrics-logging code was originally wired to run after a
plain `match request.name.as_ref() { ... }` inside `call_tool` — but Rust's
`?` and `return Err(...)` inside a match arm target the nearest enclosing
*function*, not the match itself, so every arm using either (the vast
majority — argument-parsing failures, CAS mismatches, policy rejections, DB
errors) bypassed the metrics insert entirely, silently undercounting
`mcp_handler_wall_time_ms` for any run with even one rejected call. Fixed by
wrapping the entire match in its own `async move { ... }.await` block, which
gives every arm's early return a closer boundary to land on — zero changes
needed to any individual tool handler. Regression-tested directly: a
deliberately-rejected call (missing a required argument) is now confirmed,
via a direct query against the underlying connection, to still produce a
`mcp_call_metrics` row with `is_error=1`.

Verified against the real Lean 4.32.0-rc1 + Mathlib toolchain via
`playtest.rs`: a real episode + a real `proof_export` call produced
`mcp_handler_wall_time_ms: 9620`, `storage_bytes_written: 568`,
`storage_export_bytes: 870`, `storage_export_wall_time_ms: 0` (a pure
DB-read export with no Lean invocation completing in under a millisecond is
genuinely plausible, not a broken timer) — while `cost_completeness`
correctly stayed at `"reported_total_not_exact"`, never reaching
`"total_cost_known"`, exactly as the policy requires.

**The monetary rollup** (`known_exact_cost_micros`/`reported_attested_cost_micros`/
`estimated_cost_micros`/`unknown_cost_present`/`cost_completeness`) never
merges a self-reported or estimated figure into a claimed exact total:

- `known_exact_cost_micros` sums only `exact_provider_receipt`/`exact_local_meter`-confidence
  monetary amounts (currently only `host_side_cost_micros` can ever qualify).
- `reported_attested_cost_micros` sums `"attested"`-confidence amounts —
  `model_call_reported_cost_micros` always lands here, plus `host_side_cost_micros`
  if its OWN confidence is `"attested"`.
- `estimated_cost_micros` sums `"estimated"`-confidence amounts.
- Each bucket is `null`, never `0`, when nothing qualifies for it.
  `host_side_cost_micros` under `"unknown"` confidence (or unset) is excluded
  from all three buckets — its reliability is explicitly unvouched-for —
  though it still appears verbatim in the raw `host_side_cost_micros` field.
- `unknown_cost_present` is `true` whenever `mcp_side_cost_micros` or
  `storage_export_cost_micros` is null (always true today — zero
  instrumentation for either) or host cost confidence is `None`/`"unknown"`.
- `cost_completeness`: **`"total_cost_known"`** only if every material cost
  surface is exact — `!unknown_cost_present` AND no attested/estimated amount
  exists AND an exact amount does. Given `mcp_side_cost`/`storage_export_cost`
  have zero instrumentation, **this state is currently unreachable in
  practice** — the honest, intentional state until those surfaces are ever
  instrumented, not a bug. **`"reported_total_not_exact"`** whenever some real
  monetary signal exists (exact, attested, or estimated) but the report can't
  vouch for a complete exact total. **`"total_cost_incomplete"`** when no
  monetary signal exists at all.

**`verifier_wall_time_ms`/`verifier_cpu_time_ms` are real** (a follow-up to
the gap first found while designing this feature, later split into two
fields and renamed from the original single `verifier_cost_ms`):
`RealLeanGateway::verify_exact`/`verify_module` already computed
`wall_time_ms`/`lean_cpu_time_ms` on every real verification call (see
`LeanVerificationResult`), but `attempt_finalize` in
`crates/proofsearch-core/src/orchestrator/step.rs` originally discarded everything
except the bare `LeanVerificationOutcome` enum before this data ever reached
anywhere persistent. This turned out to need no signature change at all —
`attempt_finalize` already receives the full `GatewayResponse` parameter, so
the fix serializes the real result and persists it onto the existing,
previously-never-written `action_attempts.lean_result_json` column entirely
within the function body. Verified against the real Lean 4.32.0-rc1 +
Mathlib toolchain via `examples/playtest.rs` (a real `True`/`trivial` episode
with a settled model-call lease and an exact host cost produced
`verifier_wall_time_ms: 57245`, `verifier_cpu_time_ms: 57245`,
`known_exact_cost_micros: 1000`, `reported_attested_cost_micros: 350`,
`cost_completeness: "reported_total_not_exact"` — every figure genuine, not
fabricated) and covered by
`test_benchmark_run_observe_aggregates_real_verifier_cost_from_persisted_attempts`,
`test_benchmark_run_observe_folds_in_model_call_cost_as_attested`, and
`test_benchmark_run_observe_ignores_unsettled_model_call_leases`.

**A real, non-obvious behavior found while writing the "unsettled lease"
regression test**: calling `episode_step` for the SAME `(episode_id,
action_attempt_id)` a `model_call_leases` row is reserved against
auto-settles it, using that step's OWN `cost_micros` argument as
`actual_cost_micros` (`crates/proofsearch-mcp/src/lib.rs`'s `episode_step`
handler, a pre-existing, deliberate behavior, not a bug) — a lease is not
guaranteed to stay `'reserved'` until an explicit `model_call_settle` call;
the very next `episode_step` on that attempt settles it implicitly. It only
stays genuinely unsettled if that attempt is never stepped at all (e.g. the
episode is instead terminated via `episode_close`, which never touches
`model_call_leases`).

As of the budget-hardening pass for #47/#48, that implicit settlement uses the
same delta rule as explicit `model_call_settle`: lower actual cost refunds only
the reserved difference, higher actual cost must reserve only the extra delta,
and a failed delta reservation rolls the step preparation back before any Lean
gateway call.

(A separate, dead, pre-`step.rs` legacy `Orchestrator` in `orchestrator/mod.rs`
also persists timing — into `proposal_attempts` via
`AttemptDiagnostic`/`db::insert_attempt`, not into `episode_budget_ledger`,
which despite being a real table in the schema is never written to by
anything, anywhere — but that whole `Orchestrator` is only ever constructed
from its own `#[cfg(all(test, feature = "legacy_tests"))]` test module and
was never the reference for this fix; it genuinely isn't exercised by the
MCP path.)

`mcp_handler_wall_time_ms`/`storage_bytes_written`/`storage_export_bytes`/
`storage_export_wall_time_ms`/`mcp_side_cost_micros`/`storage_export_cost_micros`
still have no instrumentation at all yet — deferred to a future slice.

`environment_build_cost` vs. `benchmark_episode_cost` is already available
via `run_envelopes.mode` (`"development"` vs. `"benchmark"`/`"evaluation"`)
— a report can group/filter by mode to get this split; no new schema
needed for that half of the ask.

## Fidelity-basis policy (issue #38, v0.3.21)

**The gap:** `benchmark_result_record`'s anti-fabrication cross-checks (issue
#30/#36) validate that an episode's actually-recorded outcome and its
`problem_version`'s statement hash match what's claimed — but never checked
the backing `problem_version`'s own `fidelity_status` (whether a human ever
reviewed that the formal statement faithfully represents the *informal*
source problem). A result could be backed by an `unsafe_dev_attestation`
("attested", never independently reviewed) problem just as validly as a
`"verified"` one.

**The resolution, per explicit product direction:** two deliberately
separate concepts.

- `problem_versions.fidelity_status` (unchanged) — does this formal
  statement faithfully represent the *informal* source problem? An
  independent human-review question, set by `problem_submit_fidelity_review`
  or (capped, dev-only) `problem_create`'s `unsafe_dev_attestation=true`.
- `benchmark_results.benchmark_fidelity_basis` (new) — what evidence backs
  *this specific benchmark claim's* statement fidelity:
  `canonical_statement_hash_match` | `problem_fidelity_verified` | `none` |
  `mismatch` (the last is reserved/defensive — a real hash mismatch is
  rejected outright before any row is written, so it's never actually
  persisted).

**Enforcement, in `benchmark_result_record`:** for a `kernel_verified`/
`certified` claim (after the existing episode-outcome and statement-hash
checks pass), the referenced benchmark suite must be
`trusted_canonical_source=true` (basis becomes `canonical_statement_hash_match`
— sufficient on its own, no independent review required) **or** the backing
`problem_version`'s `fidelity_status` must already be `"verified"` (basis
becomes `problem_fidelity_verified`). Neither being true is now a hard
rejection, not a warning or a weaker recorded basis. For any non-proof-claiming
status (`failed`/`timeout`/`infra_error`/`formalization_gap`/`skipped`), or
when no `episode_id` is given at all, `benchmark_fidelity_basis` is `"none"`
— no proof claim, nothing to report a basis for.

`benchmark_suites.trusted_canonical_source` (new, defaults `false`) is set
at `benchmark_suite_create` time via the same param name — an honest,
**self-declared** trust assertion the caller makes, exactly like
`unsafe_dev_attestation`/`host_cost_confidence` elsewhere in this codebase.
LLM-Driven Proof Search Environment never independently verifies it. There is no tool that updates an
existing suite's `trusted_canonical_source` after creation — an untrusted
suite can never be retroactively "laundered" into looking trusted. Set it
true only for a suite you can vouch is a real, externally-curated corpus
(PutnamBench) whose own registered `root_formal_statement` is itself
sufficient fidelity evidence; leave it false for an arbitrary custom suite.

**Public-facing wording matters here**: describe a
`canonical_statement_hash_match` result as e.g. "matched the suite's own
canonical formal statement" — never as "statement-fidelity certified by
LLM-Driven Proof Search Environment." LLM-Driven Proof Search Environment performed a hash comparison against a self-declared-trusted
suite's catalog text in that case, not an independent fidelity review.

Verified against the real Lean 4.32.0-rc1 + Mathlib toolchain via
`playtest.rs`: a trusted suite + an `unsafe_dev_attestation` problem + a real
`True`/`trivial` proof produced `benchmark_fidelity_basis:
"canonical_statement_hash_match"`; the identical setup against an untrusted
suite was correctly rejected outright. Covered by
`test_benchmark_result_record_trusted_suite_accepts_hash_match_alone` and
`test_benchmark_result_record_rejects_untrusted_suite_without_independent_review`
(the latter also proves a real `problem_submit_fidelity_review` unblocks the
same untrusted suite, with basis `problem_fidelity_verified`).

## Mode-enforcement policy (issue #38, v0.3.22)

**The rule, per explicit product direction:** `unsafe_dev_attestation` means
development playtest — it should never be allowed into a *measured* claim.
`run_envelope_attach_episode` (a general-purpose tool with no suite/trust
concept of its own — it just tags any episode with any run envelope)
unconditionally rejects attaching an `"attested"`-fidelity episode to a
`benchmark`/`evaluation`/`public_report`-mode envelope; `development` is
always allowed; `private_audit` requires a new explicit
`allow_dev_attested=true` argument.

**A real conflict found while implementing this, and how it was resolved:**
taken completely literally (no exceptions), this rule would have broken the
real, already-shipped, real-toolchain-verified `putnam_runner.rs` — the
actual automated PutnamBench pass@k benchmark runner, which creates its run
envelope with `mode: "benchmark"` and calls `problem_create` with
`unsafe_dev_attestation: true` for every problem it imports (there is no
per-problem human fidelity review step for an automated import of ~600
problems). `benchmark_result_record`'s mode-enforcement therefore has an
exception: it is SKIPPED when the referenced suite is
`trusted_canonical_source=true` — that flag already means "this suite's own
hash-match is sufficient fidelity evidence, independent of mode," and was
independently verified (real toolchain) to preserve the actual PutnamBench
pipeline: a trusted suite + `unsafe_dev_attestation` problem + `benchmark`
mode still succeeds with `canonical_statement_hash_match`. An adversarial
review scrutinized this exception specifically (not just ordinary bugs) and
concluded it's a defensible, non-rationalized reading — a trusted suite's
hash-match already answers the concern the mode-enforcement rule exists for
("don't let uncertified dev-bypass content leak into a measured claim");
for an untrusted suite, the review confirmed the SEPARATE, pre-existing
fidelity-basis policy already unconditionally rejects `"attested"` claims
in every mode anyway, so `benchmark_result_record`'s mode-enforcement check
mostly changes rejection WORDING there (to the exact "boring" message this
policy specifies), not the accept/reject outcome — the real, new behavioral
restriction lives in `run_envelope_attach_episode`, which has no suite-trust
exception at all.

**Formalized as a named policy (v0.3.23), per explicit follow-up direction**
— not left as an inline, PutnamBench-shaped special case. The exact rule:
"`unsafe_dev_attestation` is forbidden in benchmark/evaluation/public_report
runs unless the problem belongs to a benchmark suite marked
`trusted_canonical_source` AND the resulting `benchmark_fidelity_basis` is
`canonical_statement_hash_match` against that suite's own registered
canonical/prover-ready formal statement." Extracted into its own function,
`trusted_canonical_hash_exemption_applies(suite_trusted: bool) -> bool`, with
an extensive doc comment justifying why `suite_trusted` alone is a sound,
complete proxy for "this claim's basis will be
`canonical_statement_hash_match`" (reaching the exemption check at all
already implies the statement-hash cross-check passed, and a trusted suite's
fidelity-basis logic assigns `canonical_statement_hash_match` unconditionally,
never falling through to `problem_fidelity_verified` even for an
independently-reviewed problem) — directly unit-tested
(`test_trusted_canonical_hash_exemption_applies`,
`test_enforce_dev_attestation_mode_policy`), not just incidentally exercised
through the larger integration tests.

**A known, deliberately-undecided limitation** the same adversarial review
caught: `BenchmarkResultRecordArgs.allow_dev_attested`'s doc comment
originally overclaimed that setting it true would let a `private_audit`-mode
claim succeed for an untrusted suite — it doesn't; the fidelity-basis policy
independently still rejects `"attested"` (not `"verified"`) content
regardless of this flag. Making the flag genuinely bypass that would need a
real design decision (e.g. a fifth `benchmark_fidelity_basis` value for an
explicitly-supervised private-audit override) — left undecided and
documented rather than guessed at. In practice this flag currently only has
a real effect for a *trusted* suite in `private_audit` mode.

Verified against the real Lean 4.32.0-rc1 + Mathlib toolchain via
`playtest.rs`: an `unsafe_dev_attestation` episode was correctly blocked
from `benchmark`/`evaluation`/`public_report`-mode envelopes, allowed
unconditionally for `development`, and blocked-then-allowed for
`private_audit` without/with `allow_dev_attested=true`. Covered by
`test_run_envelope_attach_episode_blocks_attested_episode_from_measured_modes`
and
`test_benchmark_result_record_reports_exact_mode_enforcement_message_for_untrusted_suite`.

## Tracked vs. untracked verifier use (issue #36)

**The product principle:** a proof attempt that bypasses the episode ledger
is not part of LLM-Driven Proof Search Environment evidence. A benchmark run must not test candidate
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
`attempt_prepare`/`attempt_finalize` split (`crates/proofsearch-core/src/orchestrator/step.rs`)
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

LLM-Driven Proof Search Environment's benchmark-tracking tools (`benchmark_suite_create`,
`benchmark_problem_register`, `benchmark_run_create`, `benchmark_result_record`,
`benchmark_run_observe` — see the README's MCP Tools table) and its
`proof_export` tool must make it hard to *accidentally* violate that policy,
while still fully supporting private verification, replay, and
maintainer-coordinated submissions.

## Contamination policy, as enforced in code

`proof_export`'s `format` (see `ExportMode` in `crates/proofsearch-mcp/src/lib.rs`)
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
  used everywhere else in LLM-Driven Proof Search Environment: make the safe path the default path.

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

**`trajectory_export` is gated the same way (issue #34 follow-up, v0.3.16).**
A real gap found while doing #34's tool-classification audit: `trajectory_export`
returns the raw, hash-chained event log for an episode, including each event's
full `payload_json` — which for a `solve` action's `proof_term` or a
`submit_module` action's `module_items` is exactly the completed-proof-body
content this policy exists to gate, but `trajectory_export` had no equivalent
check at all until now. It now requires `allow_putnambench_proof_export=true`
for a benchmark-linked episode, using the identical `benchmark_suite_name_for_episode`
lookup `proof_export` uses, and errors with the same guidance (use `proof_export`
with `format="public_summary"` for a disclosure-safe report instead).

The benchmark-link check keys on `COALESCE(prover_ready_statement_hash,
root_statement_hash)` — the same statement identity `benchmark_result_record`
uses — so an episode created from the prover-ready Pi-form (not the raw
named-binder declaration a suite catalogs) is still recognized as
benchmark-linked and cannot bypass the proof-body gate (#49).

## Fidelity basis: formal_benchmark_hash_alignment (issue #43)

A benchmark-imported problem no longer needs `unsafe_dev_attestation` to be
provable. Because a `trusted_canonical_source` suite (like PutnamBench) is an
externally-curated corpus, a problem whose server-computed `root_statement_hash`
equals the registered benchmark target hash — `COALESCE(prover_ready_statement_hash,
root_statement_hash)`, the same identity `benchmark_result_record` uses — is
admitted on the honestly-named basis **`formal_benchmark_hash_alignment`**, via
`problem_record_benchmark_alignment`. This sets `fidelity_status='benchmark_aligned'`
and unlocks proving.

This is **hash alignment to a curated target, not independent review.** It is
deliberately weaker than `verified`:

- It can reach `outcome=kernel_verified` but **never** `certified` / problem
  state `COMPLETE` — the DB-level `CHECK(state <> 'COMPLETE' OR fidelity_status
  = 'verified')` guard makes that structurally impossible.
- The server recomputes every hash; no client-supplied hash is accepted.
- An untrusted/custom suite is rejected and directed to a real
  `problem_submit_fidelity_review`.
- Training eligibility stays quarantined (`training_eligible` still requires
  `verified`).

`proof_export(format="public_summary")` reports the three independent claims
separately so a benchmark success is never conflated with a discovery claim:

- **`kernel_verified`** — Lean accepted a proof of the formal statement.
- **`formal_target_matched`** — the formal statement is a registered benchmark
  target (`benchmark_aligned`, or a recorded `canonical_statement_hash_match`).
- **`certified`** — statement fidelity was independently reviewed (`verified`).

`benchmark_success = kernel_verified + formal_target_matched`;
`discovery_claim = kernel_verified + certified + independent_review`.

## Stored result vs current episode outcome (issue #50)

A benchmark result is a **historical report** — `benchmark_results.status` is
recorded at result time and never rewritten. But `problem_submit_fidelity_review`
can retroactively promote the referenced episode `kernel_verified` → `certified`
*after* that row was recorded. To surface this without silently mutating
history, `benchmark_run_observe` reports, per result:

- `stored_result_status` — the status recorded at result time (also mirrored as
  `status` for back-compat), never rewritten.
- `current_episode_outcome` — the referenced episode's live outcome (e.g. after
  a retroactive fidelity-review promotion).
- `stale_result` — `true` when the two diverge within the proof vocabulary
  (`kernel_verified` vs `certified`). Benign differences (a non-proof status
  vs some other outcome) are never flagged.

Aggregate metrics (`solved_count`, `pass_at_1_rate`, `kernel_verified_count`,
`certified_count`, …) remain computed from `stored_result_status` — see the
`aggregate_basis` field in the metrics block — so a run's reported numbers are
stable even as individual episodes are later promoted.

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
