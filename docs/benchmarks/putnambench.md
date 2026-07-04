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
| one evaluation run's configuration | `benchmark_runs` row (`solve_mode`, `allowed_tools_json`, `attempt_budget`, `wall_clock_budget_ms`, `lean_timeout_ms`; `lean_version`/`mathlib_commit` auto-read from the server's own detected environment, never client-supplied; optional `run_envelope_id` for host/cost tracking) |
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

### The runner (#31 — not yet built, must satisfy #36)

Per issue #36's invariant ("a proof attempt that bypasses the ledger is not
part of ChatDB evidence"), the runner's proof-search loop for each imported
problem MUST be: `episode_create` → `episode_observe`/read
`next_action_request` → `attempt_claim` → `episode_step` (repeat until
terminated or budget exhausted) → `benchmark_result_record`. It must never
call `RealLeanGateway`/`LeanGateway::verify_exact`/`verify_module` directly
to pre-screen a candidate proof before submitting it through `episode_step`
— that would let a "measured" attempt count that Lean never actually
verified through the tracked path count as evidence. Declaration lookups
during the search (checking whether a lemma name exists before trying it) are
fine through the existing MCP lookup tools (`lean_declaration_lookup`,
`mathlib_search_declarations`) — those aren't proof attempts.

### Smoke vs. full suite (#32 — not yet built)

A small (5–10 problem) fixture subset, checked into this repo's own test
fixtures (not fetched from the live PutnamBench clone), lets CI and local
dev exercise the full harness pipeline (`benchmark_suite_create` →
`benchmark_problem_register` × N → `benchmark_run_create` → the runner loop
→ `benchmark_result_record` → `benchmark_run_observe`) without needing
`PUTNAM_BENCH_PATH` set up or without spending a full-suite Lean-verification
budget. The full 640-theorem suite is a separate, explicitly-invoked mode —
never run as part of the normal `cargo test` suite.

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
