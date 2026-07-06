# PutnamBench genuine attempt — playtest report

**Date:** 2026-07-06 (session started from the 2026-07-05 rebuild; filename kept per plan)
**Toolchain:** `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (pinned)
**Harness:** Claude Code (claude-fable-5) as the *MCP host and prover*, driving `chatdb-mcp` v0.3.23 directly through `mcp__chatdb-proof-search__*` tool calls — no putnam_runner, no bash driving of the server. Every proof attempt went through the tracked `episode_create → episode_observe → attempt_claim → episode_step` loop against the real `RealLeanGateway`.
**Fidelity mode:** per-problem `problem_submit_fidelity_review` (see finding 3 — the prescribed `problem_record_benchmark_alignment` was unavailable because the suite import left `trusted_canonical_source=0`). No `unsafe_dev_attestation` anywhere. Successes therefore reach `certified` rather than last run's `kernel_verified` ceiling — with the caveat that the reviewer was the same LLM host (see "Honest calibration").
**Run:** `benchmark_run_observe` run id `8942c216-9daa-4423-a8bb-82eb4400c32d`, envelope `55122f8e-8513-4136-ab25-28bae7f7f924`, `solve_mode=submit_module_allowed`, `attempt_budget=4`.

## Why this report exists

The 2026-07-04 baseline (`docs/playtests/2026-07-04-putnambench-first-attempt.md`) scored **1/12 pass@1** with deliberate `sorry`-placeholder attempts — it measured the plumbing, not the math. This run is the promised follow-up: genuine mathematical effort on the same 12 problems, worked out before formalizing, with the host as a first-class MCP client. It is also the first time a spec-compliant external MCP host (Claude Code) has driven the server at all — which surfaced a serious bug before the first tool call could even be made (finding 1).

## Results

`benchmark_run_observe` metrics: `solved_count: 6`, `solved_rate: 0.5`, `pass_at_1_rate: 0.25`, `certified_count: 6`, `kernel_verified_count: 0` (all six went straight to `certified`), `average_attempts_per_result: 1.58`. Verifier wall time 381 s across 24 tracked MCP actions.

| Problem | Shape | Result | Attempts | Notes |
|---|---|---|---|---|
| `putnam_1988_b1` | Solve | **certified** | pass@1 | re-proved; witnesses `x=a−1, y=b−1, z=1`, `ring` |
| `putnam_1966_a1` | SubmitModule (helpers) | **certified** | pass@2 | f(n)=⌊n²/4⌋; closed form `4·Σ = n²−n%2` by `Int.leInduction`; the problem the baseline ran out of time on |
| `putnam_1968_a1` | Solve | **certified** | pass@3 | the 22/7−π integral; explicit antiderivative `x⁷/7−2x⁶/3+x⁵−4x³/3+4x−4·arctan x` + FTC |
| `putnam_1972_a1` | Solve | **certified** | pass@1 | no 4 binomials in AP; `(n−2r−2)²=n+2` and shift ⇒ `n=2r+3` ⇒ `r=−2`; `linear_combination` + `linarith` |
| `putnam_1990_b1` | SubmitModule (find-the-set) | **certified** | pass@4 | answer `{±√1990·eˣ}`; forward: FTC-1 + `HasDerivAt.unique` ⇒ 2ff′=f²+f′² ⇒ f′=f ⇒ f·e⁻ˣ const |
| `putnam_2000_a1` | SubmitModule (find-the-set) | **certified** | pass@1 | answer `Ioo 0 (A²)`; forward via xⱼ<A strict comparison of tsums; backward via geometric xⱼ=A(1−r)rʲ, r=(A²−S)/(A²+S) |
| `putnam_1962_a1` | Solve | failed | 1 | Happy-Ending k=4; stateable, but synthetic convex-position case analysis exceeded remaining budget |
| `putnam_1970_a1` | Solve (+`ball` alias) | failed | 2 | math solved on paper (θ/π rational dichotomy) but needs power-series-coefficient uniqueness machinery; statement elaborates fine with a Set-valued `ball := Metric.ball` module def |
| `putnam_1963_b1` | SubmitModule (a=2) | **formalization_gap** | 1 | `X`,`C` aliases can't compile (`Polynomial` noncomputable); everything else in the attempt elaborated — see finding 6 |
| `putnam_2016_a1` | SubmitModule (j=8) | **formalization_gap** | 1 | `ℤ[X]` is scoped notation → parses as `getElem`! `derivative` auto-binds as an implicit — see finding 5 |
| `putnam_1965_a1` | SubmitModule (α=π/15) | **formalization_gap** | 1 | double-blocked: `∠`/`π` scoped tokens don't parse AND `Real.pi/15` def is noncomputable |
| `putnam_1962_a3` | Solve (+`volume` alias) | **formalization_gap** | 1 | `Measure`-valued alias def is noncomputable (statement itself elaborated around it) |

**6/12 (50%) solved, all kernel-checked and certified, vs 1/12 (8.3%) baseline.** Three of the six remaining are environment-blocked with the math solved or solvable (1963_b1: a=2 with the full degree-11 quotient computed and cross-checked; 2016_a1: j=8 with a complete Lean proof plan through `iterate_derivative_eq_sum` + `Nat.factorial_dvd_descFactorial`; 1965_a1: α=π/15 derived from the two isoceles external-bisector equations β=3π/4−α/4 and α=(π−β)/4). Two failed on genuine mathematical formalization difficulty, honestly recorded after real attempts.

## Environment findings (ordered by severity)

### 1. The server never advertised the `tools` capability — invisible to every spec-compliant MCP host (fixed this session)
`ServerHandler::get_info` returned `ServerCapabilities::default()` (i.e. `"capabilities": {}`), so Claude Code — correctly following the MCP spec — never called `tools/list` and the server registered zero tools. Every prior playtest used in-house clients that call `tools/list` unconditionally, which is why this was never seen. One-line fix applied and verified this session ([crates/chatdb-mcp/src/lib.rs](../../crates/chatdb-mcp/src/lib.rs): `ServerCapabilities::builder().enable_tools().build()`); uncommitted in the working tree.

### 2. Registered benchmark statements do not elaborate in the assembled-module context (scoped notation / open-context loss)
Upstream PutnamBench files carry `open Polynomial Real EuclideanGeometry Metric MeasureTheory ...` preambles. The importer keeps only the statement text; `assemble_module` emits imports + `namespace ChatDB.P_<id>` with **no `open` lines**. Consequences observed live:
- `ℤ[X]` (scoped in `Polynomial`) parses as the *global `getElem` indexing notation* — the kernel error for 2016_a1 shows `⊢ ?m.29 j ℤ X` with `X : ?m.1` auto-bound.
- Unknown lowercase identifiers (`derivative`) get **auto-bound as implicit arguments** — the statement can elaborate to something entirely different from the intended mathematics without failing. This is worse than a parse error.
- `∠` and `π` are unparseable tokens (1965_a1).
Affected: 2016_a1, 1963_b1, 1965_a1, 1962_a3, 1970_a1 (5 of 12). Fix options: capture upstream `open` lines in the import manifest and emit them in the assembled module, or qualify names at import time.

### 3. SubmitModule `def` items cannot be `noncomputable` — blocks most real-analysis/geometry solution defs
`render_def` always emits plain `def`. Anything whose value lives in `Polynomial ℤ`, `ℝ` (e.g. `Real.pi/15`, even `Real.sqrt 1990` if bound as a bare value), or `Measure α` fails with "failed to compile definition, consider marking it as 'noncomputable'". Set-valued defs (`Set (ℝ → ℝ)`, `ℝ → Set ℝ`, `ball := Metric.ball`) compile fine because `Prop`-valued data is erased — which is exactly why 1990_b1/2000_a1 succeeded and 1963_b1/1965_a1/1962_a3 could not. **Recommended fix: emit `noncomputable section` after the set_options in `assemble_module`** — harmless for theorems, unblocks all of these.

### 4. Name-capture soundness gap: module defs can bind free identifiers in the hash-pinned root statement
The root-statement hash check pins the *text*, but a statement like 1963_b1's (`X^2 - X + C a ∣ ...`) contains free identifiers that resolve against whatever the module defines. I used honest aliases (`X := Polynomial.X`), but a dishonest module could define `C := fun _ => 0` and prove a trivially different proposition under the same hash. The alias defs are visible in the verified module manifest, so this is auditable — but nothing *enforces* it. Suggested policy: reject module defs whose names shadow identifiers occurring in the root statement, except the declared solution abbrev name.

### 5. `problem_record_benchmark_alignment` was unusable: the suite import left `trusted_canonical_source=0` and no suite-update tool exists
The 2026-07-06 re-import of the 12 problems did not set the trust flag (`benchmark_suite_create` only accepts it at creation). Fallback used: per-problem `problem_submit_fidelity_review` with byte-comparison evidence against the registered row + upstream provenance, as the server's own error message directs. Side effect: successes record as `certified` (fidelity basis `problem_fidelity_verified`) rather than `benchmark_aligned`/`kernel_verified`.

### 6. `problem_create`'s 45 s import-validation timeout cannot survive a cold Mathlib cache
Cold `import Mathlib` on this machine: 2 m 07 s; warm: 15 s. The first two `problem_create` calls of the session failed with "Lean invocation timed out after 45 seconds" until a manual warm-up compile. Fix: raise the validation timeout, or pre-warm at server start, or cache validation by manifest hash (the same manifest was re-validated 10 times this run).

### 7. No MCP tool reads back a registered benchmark problem
`prover_ready_statement` + `import_manifest_json` had to be fetched by a read-only SQLite query — the only non-MCP data access in the run (input retrieval only, no proof surface). A `benchmark_problem_observe`/`benchmark_suite_observe` tool would close the loop.

### 8. Flattened helper proofs: an inline `by` swallows the rest of the tactic chain
In `flat_tactic_sequence` (mandatory for helper theorems), `have k : T := by omega; have k2 : ...` parses everything after `by` as one block — the next tactic runs inside the closed sub-proof and dies with "No goals to be solved", while the outer goal is silently unsolved. Cost me one attempt on 1966_a1 before diagnosing. Workaround: always parenthesize `(by tac)`. Worth documenting in the `episode_step` schema next to the issue-#41 note.

### 9. Things that worked notably well
- **Issue #41 fix held up**: `raw_lean_block` transported six large multi-line, bullet-structured proofs byte-perfectly; zero formatting casualties.
- **Diagnostics quality**: line-precise spans, full goal states, and multiple errors per attempt made 1-attempt repairs routine (1968_a1's `π = 4*(π/4)` residual, 1990_b1's three successive single-error fixes).
- **`sorry` policy**: rejected pre-Lean with a clear message when I tried to use it as an elaboration probe (correctly — the probe was replaced with a sorry-free failing proof).
- **The tracked loop**: 24 actions, zero infra errors, zero panics, idempotent claims, correct revision checks, honest pass@k accounting throughout.
- **`mathlib_search_declarations`** (librarian) caught two would-be attempt-wasters before submission: `Int.le_induction` is deprecated for `Int.leInduction` in this snapshot, and the ℝ order-tsum lemmas moved to `Summable.*`/`to_additive`-generated names (`Summable.tsum_pos`, `Summable.sum_le_tsum`, `Summable.tsum_lt_tsum_of_nonneg`).

## Honest calibration

- Every success was preceded by the math being worked out in full (construction, closed form, quotient polynomial, coefficient bounds, ODE argument, geometric-series parametrization) before any Lean was written; lemma names were verified against the pinned Mathlib source (read-only) rather than guessed, per `readme_first`'s own guidance.
- The `certified` label rests on fidelity reviews performed by the same LLM host that proved the theorems. The evidence (byte-match to the upstream-imported target + provenance) is recorded in each review, but a self-review is a weaker basis than an independent one — if the maintainer prefers, the suite trust flag + `benchmark_alignment` path (or an independent reviewer) would put these on the intended `benchmark_aligned` basis instead. Flagged rather than hidden.
- The two `failed` entries (1962_a1, 1970_a1) are genuine mathematical-effort failures under the session budget, not environment artifacts: both statements elaborate, and 1970_a1's paper solution is complete but needs power-series-coefficient-uniqueness infrastructure that would dominate the session.
- The four `formalization_gap` entries are environment-blocked, not math-blocked; three of the four have complete or near-complete solutions in hand. Fixing findings 2+3 would likely raise this sample's ceiling to 9–10/12.
- Host-side reasoning cost is not represented in `cost_micros` (all zero) — `cost_completeness: total_cost_incomplete` in the envelope is accurate.

## Boundaries respected

Maintainer-approved local playtest. No proof publishing; `allow_putnambench_proof_export` remained `false` for every export-capable surface (no proof-body exports were made at all); artifacts are private (this repo). Nothing committed or pushed — the capabilities fix from finding 1 and this report are left in the working tree.
