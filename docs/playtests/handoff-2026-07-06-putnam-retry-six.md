# Handoff: retry the 6 unsolved PutnamBench problems on proofsearch-mcp v0.3.24

You are the MCP host and the prover. Drive the `proofsearch` server **through its MCP tools only** (`mcp__proofsearch__*`) — no bash driving of the server, no putnam_runner, no SQL side channel (you no longer need one; see the new observe tools). If the proofsearch tools are not in your tool list, STOP and say so.

## Context you inherit

Two prior runs against the same 12-problem PutnamBench sample (suite `PutnamBench`, `suite_id = ea562051-8d69-4fb4-a5b2-c6865a94c4c3`, upstream commit `a23d8e6d4e9e3418fd78f76de7bfcb9414cbfd39`):

- 2026-07-04 baseline: 1/12 (placeholder attempts) — `docs/playtests/2026-07-04-putnambench-first-attempt.md`.
- 2026-07-06 genuine attempt: **6/12 certified** (run `8942c216-9daa-4423-a8bb-82eb4400c32d`) — `docs/playtests/2026-07-05-putnam-genuine-attempt.md`. Read it. Its six failures are your six targets.

Since that run, issues #61–#67 were implemented and the server was rebuilt: **v0.3.24, 89 tools** (`target/release/proofsearch-mcp.exe`). Four of your six targets failed on environment gaps that are now fixed; your run is both a genuine proving attempt and the acceptance test for those fixes. Do not redo the import; do not touch the old run's results — create a **new** envelope + run and record into that.

What changed that you must actually use:

1. **`open` directives in import manifests (#62).** `problem_create`'s `problem_imports` now accepts entries like `"open Polynomial"` / `"open scoped BigOperators"` alongside module paths. They render inside the assembled namespace, so statements using scoped notation (`ℤ[X]`, `∠`, `π`) or unqualified names (`derivative`, `volume`, `ball`) finally elaborate to the intended mathematics. This replaces the alias-def trick from the last run — which is now **rejected** (see 3).
2. **`noncomputable section` wrapping (#63).** SubmitModule `def`s may now hold noncomputable values (`ℝ`, `Polynomial ℤ`, `Real.pi / 15`). The two "noncomputable def" gaps are gone.
3. **Shadow guard (#64).** For a statement registered in a benchmark suite, the module may not declare any name occurring free in the root statement — **except** the `*_solution` slot. So: never name a helper `X`, `C`, `P`, or any identifier from the statement; get library names via the open context instead.
4. **`benchmark_suite_observe` / `benchmark_problem_observe` (#65).** Fetch each problem's `prover_ready_statement` (byte-exact) and metadata through these — no DB reads.
5. **`benchmark_suite_set_trust` (#65).** FIRST ORDER OF BUSINESS after the run is created: the suite still has `trusted_canonical_source = false`, which last run forced LLM self-reviews. Set it true (approver: your host name; notes must cite the upstream repo + commit above), then use **`problem_record_benchmark_alignment`** per problem — the honest fidelity basis. Your successes will record as `kernel_verified` (alignment basis never reaches `certified`); that is correct and expected — do not "upgrade" via self-review.
6. **Import validation (#66).** First `problem_create` with a fresh manifest may take up to ~4 min cold (timeout is now 240s and known manifests are skipped). Be patient; don't retry while it runs.
7. **Inline `by` trap is documented (#67)** — but still real: in any flattened/semicolon chain, write `(by tac)` with parentheses unless the `by` is the final element. Helper theorem proofs are ALWAYS flattened; only the root theorem may use `proof_format: "raw_lean_block"` (use it — bullets/indentation survive).

## Protocol (same as last run)

1. `readme_first`, then `environment_describe` (expect `environment_version: 0.3.24`, lean gateway ready, toolchain `v4.32.0-rc1 + mathlib@360da6fa…`).
2. `run_envelope_create` (mode `benchmark`, host_name of your choosing, benchmark_suite_name `PutnamBench`) → `benchmark_run_create` (suite_id above, `solve_mode: "submit_module_allowed"`, attempt_budget 4).
3. `benchmark_suite_set_trust` (see item 5 above) — record the returned `trust_review_id` in your report.
4. Per problem: `benchmark_problem_observe` → `problem_create` with `root_formal_statement` = the row's **prover_ready_statement byte-for-byte** and `problem_imports` per the table below → `problem_record_benchmark_alignment` (problem_version_id + benchmark_problem_id + approver_id) → `episode_create` → tracked loop `episode_observe → attempt_claim → episode_step`.
5. Close every episode honestly (`give_up` if beaten), then `benchmark_result_record` for all six (run_id, benchmark_problem_id, problem_version_id, episode_id, status, pass_at, attempts_used). Statuses: `kernel_verified` on success; `failed` for genuine math defeat; `formalization_gap` ONLY if the environment still can't state the problem (that would be a regression in #62/#63 — report it loudly).
6. `benchmark_run_observe` → write the report to `docs/playtests/2026-07-06-putnam-retry-six.md` (same style as the prior two). Do NOT commit or push anything.

## The six targets

| upstream id | benchmark_problem_id | last status | problem_imports to use |
|---|---|---|---|
| putnam_2016_a1 | `72675726-9044-4e74-b9cd-23aaa437e7e6` | formalization_gap | `["Mathlib", "open Polynomial"]` |
| putnam_1963_b1 | `cb562a8d-64ae-4b1d-8d26-d03854b7e1fe` | formalization_gap | `["Mathlib", "open Polynomial"]` |
| putnam_1965_a1 | `d2fe8b2c-bf2d-43ea-8040-0ce001a287ce` | formalization_gap | `["Mathlib", "open Real EuclideanGeometry"]` |
| putnam_1962_a3 | `3533123a-6475-4544-802c-34e93dc807fe` | formalization_gap | `["Mathlib", "open MeasureTheory"]` |
| putnam_1970_a1 | `f8c40775-3023-4852-8906-79bc695b11bd` | failed (math) | `["Mathlib", "open Metric"]` |
| putnam_1962_a1 | `cd80e61b-1047-45c9-b869-c6149124aff3` | failed (math) | `["Mathlib"]` |

Work them in that order — the first two have complete proof plans below and should land; the middle two have the answer/derivation done but hard formalization; the last two are the hardest and it is honest to fail them after real attempts.

### putnam_2016_a1 — answer: 8 (high confidence; full plan ready)

Least positive j with `2016 ∣ (derivative^[j] P).eval k` for all `P : ℤ[X]`, `k : ℤ`. Math: the j-th derivative's values are always divisible by j! (falling-factorial coefficients), and `P = X^j` at `k = 1` gives exactly j!; so membership ⟺ `2016 ∣ j!`; `2016 ∤ 7! = 5040`, `2016 ∣ 8! = 40320`.

Module (all verified to exist in this Mathlib snapshot):
- `def putnam_2016_a1_solution : ℕ := 8`
- helper `mem_eight : ∀ (P : Polynomial ℤ) (k : ℤ), 2016 ∣ (Polynomial.derivative^[8] P).eval k` — proof: `intro P k; rw [Polynomial.iterate_derivative_eq_sum, Polynomial.eval_finset_sum]; refine Finset.dvd_sum ?_; intro i hi; rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, nsmul_eq_mul]; have h1 : (2016 : ℤ) ∣ (((i + 8).descFactorial 8 : ℕ) : ℤ) := (by exact_mod_cast dvd_trans (by decide : (2016 : ℕ) ∣ Nat.factorial 8) (Nat.factorial_dvd_descFactorial (i + 8) 8)); exact (h1.mul_right _).mul_right _`
- helper `lower_bound : ∀ j : ℕ, 0 < j → (∀ P : Polynomial ℤ, ∀ k : ℤ, 2016 ∣ (Polynomial.derivative^[j] P).eval k) → 8 ≤ j` — proof: `intro j hj0 hall; by_contra hlt; push_neg at hlt; have h := hall (Polynomial.X ^ j) 1; rw [Polynomial.iterate_derivative_X_pow_eq_C_mul j j, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, Polynomial.eval_C] at h; have hn : (2016 : ℕ) ∣ Nat.factorial j := (by exact_mod_cast h); have h7 : (2016 : ℕ) ∣ Nat.factorial 7 := dvd_trans hn (Nat.factorial_dvd_factorial (by omega)); exact absurd h7 (by decide)`
- root proof: `exact ⟨⟨by decide, fun P k => mem_eight P k⟩, fun j hj => lower_bound j hj.1 hj.2⟩`

These helper proofs are untested (last run died at statement elaboration before reaching them) — expect to iterate within budget.

### putnam_1963_b1 — answer: a = 2 (verified three ways; full plan ready)

`(X^2 - X + C a) ∣ (X^13 + X + C 90) ↔ a = 2`. With `open Polynomial` you need **no alias defs** (and the shadow guard would reject them). Module: `def putnam_1963_b1_solution : ℤ := 2` + root proof (raw_lean_block):

- **Forward:** `simp only [putnam_1963_b1_solution]` early so the goal is `a = 2` (the def is opaque to norm_num otherwise). Then `Polynomial.eval_dvd (x := t) h` at t = 0, 1, −1, −2 (+ `simp` at each) gives `a ∣ 90`, `a ∣ 92`, `2 + a ∣ 88`, `6 + a ∣ -8104`. `dvd_sub hB hA` + `norm_num` → `a ∣ 2`; bounds via `Int.le_of_dvd` (+ `neg_dvd` for the lower side); `interval_cases a <;> first | rfl | norm_num at hA hB hC2 hD` (do NOT put `⊢` in the norm_num location list — the four contradiction cases close from a hypothesis and a trailing `⊢` then errors "no goals"; that exact mistake burned an attempt last run).
- **Backward:** `subst`; witness quotient `X^11 + X^10 - X^9 - 3*X^8 - X^7 + 5*X^6 + 7*X^5 - 3*X^4 - 17*X^3 - 11*X^2 + 23*X + 45` (checked at x = 1, −1, 2: 2·46=92, 4·22=88, 4·2071=8284); then `simp only [putnam_1963_b1_solution, map_ofNat]` (turns `C 90`, `C 2` into literals) and `ring`.

### putnam_1965_a1 — answer: π/15 (derived; formalization genuinely hard)

Derivation to include in your reasoning: with α = ∠CAB, β = ∠ABC, the isoceles external-bisector conditions give ∠ABX = π/4 + α/4 = π − β (so β = 3π/4 − α/4) and ∠YAB = (π − β)/4 = α, hence 15α = π; consistency check α=12°, γ=36°, β=132° satisfies α < γ < 90° < β. `def putnam_1965_a1_solution : ℝ := Real.pi / 15` now **compiles** (#63), and `∠`/`π` now **parse** (#62 with `open Real EuclideanGeometry`). The remaining wall is the synthetic-geometry proof (angle arithmetic in `EuclideanGeometry.angle` with collinearity side conditions — Mathlib support is thin). Spend real attempts (angle-sum lemmas: search `angle_add_angle_add_angle_eq_pi`, `EuclideanGeometry.angle` API via `mathlib_search_declarations` first); `failed` after genuine effort is an acceptable outcome. Do not name helpers `A B C X Y` (shadow guard).

### putnam_1962_a3 — Routh-type area ratio (formalization very hard)

Statement now elaborates with `open MeasureTheory`. The math is a coordinates/affine computation (areas of cevian intersections; ratio `(k−1)²/(k²+k+1)`), but Mathlib has no Routh's theorem and `volume (convexHull …)` triangle-area computations are heavy. Try `Decompose` to isolate sub-obligations if you see a viable path; otherwise one or two honest attempts and `give_up` → `failed` (NOT formalization_gap — the statement now parses; verify that it does and note it in the report as the #62 acceptance evidence even if the math defeats you).

### putnam_1970_a1 — dichotomy of zero coefficients (math failed last time)

With `open Metric`, no alias def needed. Math: p n = rⁿcos(nθ)/n! with θ = arctan(b/a) ∈ (0, π/2); cos(nθ) = 0 has either no solutions (θ/π irrational) or an arithmetic progression of them (θ/π rational) — so S = ∅ or infinite. The formalization wall is extracting `p n = …` from the raw `∑' (p n)·xⁿ = f x on ball 0 c` hypothesis: you need uniqueness of power-series coefficients (`HasFPowerSeriesAt` + `FormalMultilinearSeries` machinery — search `hasFPowerSeriesAt_iff`, `HasFPowerSeriesAt.eq_pow_smul_coeff` / `taylor` lemmas). Budget your effort: if coefficient extraction doesn't fall within 2 attempts' worth of exploration, `give_up` honestly.

### putnam_1962_a1 — 5 points, 4 in convex position (math failed last time)

Statement elaborates as-is. Happy-Ending k=4: case analysis on the convex hull of the 5 points (hull size 5 or 4 → immediate; size 3 → two interior points' line splits a triangle edge pair). No Mathlib support for convex-position combinatorics; radon/caratheodory lemmas exist (`radon_partition`, `Convex.combo…`) but the case analysis is large. Same policy: real attempt(s), then honest `failed`.

## Traps carried over from the last run (all still apply)

- **Byte-exact statements**: `problem_create.root_formal_statement` and the SubmitModule `root_theorem.statement` must equal the `prover_ready_statement` from `benchmark_problem_observe` byte-for-byte (hash-checked).
- **This Mathlib snapshot renames**: `Int.le_induction` → `Int.leInduction` (cases `base`/`succ`); ℝ order-tsum lemmas live under `Summable.*` (`Summable.tsum_pos`, `Summable.sum_le_tsum`, `Summable.tsum_lt_tsum_of_nonneg`); `ContDiff.differentiable` takes `(hn : n ≠ 0)` (use `one_ne_zero`), `ContDiff.continuous_deriv_one` exists; `hasDerivAt_neg' x` takes explicit `x`; `hasDerivAt_id'`'s dot-notation misresolves — apply lemmas by full name when dot notation errors mention `Function.…`.
- **Verify names before spending attempts**: `mathlib_search_declarations` / `lean_declaration_lookup` (deep_check only when needed, 15–40s+). Check `proof_pattern_search` before repeating a failure.
- **`decide` is fine** for small numeric facts (`2016 ∣ 8!`); `native_decide` is banned.
- **`sorry` is policy-rejected pre-Lean** — for an elaboration probe use a real failing tactic (e.g. end with `norm_num`), whose diagnostic shows whether the statement parsed.
- **HasDerivAt function shapes**: `simpa` across `f ^ 2` / `-id` Pi-shapes hits instance mismatches; prefer `HasDerivAt.congr_deriv` + `Filter.Eventually.of_forall` with `pow_two`, and explicit lemmas with the right lambda shape.
- Real checks take ~15s warm / minutes cold; never resubmit while one is running; claim tokens are per-attempt (`attempt_claim` before every `episode_step`, `expected_revision` from the latest action_request).

## Boundaries

Maintainer-approved local playtest. No proof publishing, `allow_putnambench_proof_export` stays false, private artifacts only, no commit/push. Report honest numbers — the interesting outputs are (a) whether #62/#63 turned the four gaps into provable problems, (b) any NEW environment finding, filed with the same specificity as the last two reports, and (c) real solve/fail statuses for the math-hard pair.
