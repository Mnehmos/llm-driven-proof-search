# PutnamBench retry (the six unsolved) — playtest report

**Date:** 2026-07-06
**Toolchain:** `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56` (pinned)
**Harness:** Claude Code (claude-fable-5) as MCP host and prover, driving **proofsearch-mcp v0.3.24** (89 tools) through `mcp__proofsearch__*` — first run after issues #61–#67 landed. Handoff executed: `docs/playtests/handoff-2026-07-06-putnam-retry-six.md`.
**Fidelity mode:** `benchmark_suite_set_trust` granted PutnamBench `trusted_canonical_source` (audit row `390bf09c-e90c-4e5d-8820-8ea579c98cc5`, provenance in notes), then **`problem_record_benchmark_alignment` per problem** — the intended `benchmark_aligned` basis. No `unsafe_dev_attestation`, no LLM self-reviews. Successes therefore record as `kernel_verified` (alignment never reaches `certified`) — correct by design.
**Run:** id `76619de7-ce90-4f47-9cfa-5f8c4f457b98`, envelope `3564a2c7-3c9c-4c2f-bd48-5000c8761164`, `solve_mode=submit_module_allowed`, `attempt_budget=4`.

## Why this report exists

Run `8942c216` (2026-07-04→06, 6/12 certified) left six problems unsolved: four blocked by environment gaps (scoped notation lost, noncomputable defs unsupported) and two by genuine math difficulty. Issues #61–#67 fixed the environment side. This run retries exactly those six — it is simultaneously a genuine proving attempt and the **acceptance test for #62/#63/#65/#66**.

## Results

`benchmark_run_observe`: `solved_count: 2` of 6, `kernel_verified_count: 2`, `pass_at_1_rate: 0.167`, avg 1.83 attempts. Combined with the prior run's six certified successes, the 12-problem sample now stands at **8/12 solved (67%)**, up from 1/12 (baseline) and 6/12 (first genuine attempt).

| Problem | prior status | this run | attempts | notes |
|---|---|---|---|---|
| `putnam_2016_a1` | formalization_gap | **kernel_verified** | pass@1 | j = 8; `ℤ[X]`/`derivative` elaborated via `open Polynomial` manifest entry; prepared proof landed unchanged |
| `putnam_1963_b1` | formalization_gap | **kernel_verified** | pass@3 | a = 2; no alias defs needed (or allowed — #64); explicit degree-11 quotient + eval-at-{0,1,−1,−2} case analysis |
| `putnam_1965_a1` | formalization_gap | failed (math) | 2 | **statement now elaborates** (`∠`, `π` via `open Real EuclideanGeometry`) and `Real.pi / 15` solution def **compiles** (#63); synthetic-geometry betweenness case analysis remains out of budget |
| `putnam_1962_a3` | formalization_gap | failed (math) | 2 | **statement now elaborates** (`volume` via `open MeasureTheory`); Routh-type area computation remains out of reach (no Mathlib support) |
| `putnam_1970_a1` | failed (math) | failed (math) | 2 | `ball` now resolves natively via `open Metric` (no alias def); power-series coefficient-uniqueness wall unchanged |
| `putnam_1962_a1` | failed (math) | failed (math) | 1 | statement fine both runs; Happy-Ending k=4 case analysis unformalized |

## Acceptance verdicts for the #61–#67 work (the run's real question)

- **#61 (capabilities):** all 89 tools registered in a spec-compliant host session; the run happened at all.
- **#62 (open context): CONFIRMED.** All four `open`-directive manifests (`open Polynomial`, `open Real EuclideanGeometry`, `open MeasureTheory`, `open Metric`) validated at `problem_create` and made previously-garbage statements elaborate to the intended mathematics. Two of the four turned directly into kernel-verified proofs; the other two now fail honestly on math instead of on parsing. **Zero `formalization_gap` statuses this run.**
- **#63 (noncomputable section): CONFIRMED.** `putnam_1965_a1_solution : ℝ := Real.pi / 15` — the exact def shape that failed compilation last run — compiled inside the assembled module.
- **#64 (shadow guard):** respected implicitly — 1963_b1 was proved with **no** `X`/`C` alias defs (the open context makes them unnecessary, which is the design intent). No false-positive rejections: the `_solution` slots passed in both solved problems.
- **#65 (observe/trust tools): CONFIRMED.** Every statement fetched byte-exact via `benchmark_problem_observe` (no SQL side channel anywhere in this run); trust granted through the audited `benchmark_suite_set_trust` path, unlocking `problem_record_benchmark_alignment` for all six problems — the honest fidelity basis the last run had to substitute self-reviews for.
- **#66 (import validation):** the first novel manifest validated within the raised timeout; the identical-manifest case (1963_b1 after 2016_a1) returned instantly via the manifest-hash skip.
- **#67 (inline `by`):** the guidance is live in `readme_first`/`episode_step`; and this run still paid a related tax (see finding 1) — the *sibling* trap, not the documented one.

## Environment findings (new this run)

1. **Multi-location `norm_num at h1 h2 h3` errors with "No goals to be solved" when an early hypothesis closes the goal** (1963_b1 attempt 1). Same family as #67's inline-`by` trap and the prior run's `at ... ⊢` variant: a location list is processed left-to-right and the tactic errors if the goal is already gone before the list is exhausted. Cost one attempt. Candidate doc/guard follow-up: recommend one-hypothesis-per-case bullets (which is what worked) in the same `readme_first` entry.
2. **`omega` ignores `∣` hypotheses whose divisor is an unevaluated literal sum** (`2 + -1 ∣ 88` after `interval_cases` substitution) — "No usable constraints found" (1963_b1 attempt 2). Not a bug, but worth knowing: normalize divisors (or use `norm_num`) before expecting omega to use divisibility facts.
3. **`nlinarith` over `EuclideanGeometry.angle` atoms can hit the 200k-heartbeat deterministic timeout** (1965_a1) rather than failing fast — budget accordingly when probing geometry goals.
4. No regressions observed: alignment, hash cross-checks, claim/revision discipline, and result recording all behaved; 11 tracked MCP actions, zero infra errors.

## The two new proofs, in brief

- **putnam_2016_a1** (least j with 2016 ∣ every j-th derivative value; answer 8): membership via `iterate_derivative_eq_sum` + `eval_finset_sum` + `Finset.dvd_sum`, with `2016 ∣ 8!` by `decide` and `Nat.factorial_dvd_descFactorial`; minimality via `P = X^j` at `k = 1`, `iterate_derivative_X_pow_eq_C_mul` + `descFactorial_self` reducing membership to `2016 ∣ j!`, killed by `j ≤ 7 → j! ∣ 5040` + `decide`.
- **putnam_1963_b1** (x²−x+a ∣ x¹³+x+90 iff a = 2): forward by `Polynomial.eval_dvd` at 0, 1, −1, −2 giving `a ∣ 90`, `a ∣ 92` → `a ∣ 2`, then `interval_cases` with one contradicting divisibility per case; backward by the explicit quotient `X¹¹+X¹⁰−X⁹−3X⁸−X⁷+5X⁶+7X⁵−3X⁴−17X³−11X²+23X+45` and `ring` after `map_ofNat`.

## Honest calibration

The two solves were exactly the two the handoff predicted (complete proof plans prepared from already-solved math); the four failures were honestly closed after budget-boxed genuine attempts, with the math walls named precisely (betweenness configuration analysis, Routh area machinery, power-series coefficient uniqueness, convex-position combinatorics). Those four would each need a dedicated session (or new Mathlib infrastructure) rather than more attempts. The remaining honest ceiling of this 12-problem sample under current Mathlib support is, in my judgment, the current 8/12 — the last four are research-effort formalizations, not iteration targets.

Note on labels across runs: the prior run's six successes say `certified` (fidelity self-review basis, flagged there); this run's two say `kernel_verified` (alignment basis). The alignment basis is the weaker *claim* but the stronger *process* — if consistency matters for any future aggregate, the trust flag now makes re-running the prior six under alignment straightforward.

## Boundaries respected

Maintainer-approved local playtest. No proof publishing, no proof-body exports (`allow_putnambench_proof_export` untouched/false), private artifacts only, nothing committed or pushed.
