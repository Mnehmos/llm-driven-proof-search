/-
Erdős Problem #858 — §5.4 log-harmonic transfer, rung 5 / assembly (Chojecki 2026).

`diagonal two-limit squeeze`: let `W : ℕ → ℕ → ℝ`, `R : ℕ → ℝ`, `L : ℝ`, `A : ℕ → ℝ`.
If
  (i)   for each `K`, `(fun N => W K N) → R K`   (the fixed-K limit),
  (ii)  `R K → L` as `K → ∞`,
  (iii) for every `ε > 0`, eventually in `K`, eventually in `N`, `|A N − W K N| ≤ ε`
        (a uniform-in-`N`, `K`-controllable error),
then `A N → L` as `N → ∞`.

This is the ε/3 diagonal argument that completes the log-harmonic transfer:
`A N = (1/log N) Σ_{1<a≤N} f(u_a)/a` (the true normalized sum), `W K N =` the fixed-K
weighted block sum (`→ R K = R_K(f)` by rung 3, #100), `R K = R_K(f) → ∫₀¹ f` by the
durable Riemann-sum theorem (#97), and (iii) is the aggregation error (rung 4, #101)
after normalizing by `log N`. With those three plugged in, this lemma yields
`(1/log N) Σ_{1<a≤N} f(u_a)/a → ∫₀¹ f`.

Proof (ε/3): choose `K` with `|R K − L| < ε/3` (from (ii)) and, simultaneously, the
error hypothesis (iii) at `ε/3` (common witness via `Eventually.and .exists`); for that
`K`, (i) gives `|W K N − R K| < ε/3` eventually in `N`; the triangle inequality
`|A N − L| ≤ |A N − W K N| + |W K N − R K| + |R K − L| < ε` closes it. Working in the
ε-`N` form (`Metric.tendsto_atTop` / `Filter.eventually_atTop`) keeps everything on
`dist`/`abs` and avoids nhds/ball unification. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode c675fe0a-d0be-46b7-a555-544507b5a9d4,
  problem_version_id 153e5a12-0b28-4d14-973c-151d26fd7b8f.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 8830ae5e0b76b4856d1d563c0ba2c2e5cbb61e10494a75d4ec101e51a0b57c80.
-/
import Mathlib

namespace Erdos858

/-- Log-harmonic transfer rung 5 / assembly (diagonal two-limit squeeze): fixed-K
limits `W K · → R K`, outer limit `R K → L`, and a uniform-in-N controllable error
`|A N − W K N| ≤ ε` imply `A N → L`. The keystone that combines rung 3 (#100, → R_K),
the durable Riemann-sum theorem (#97, R_K → ∫), and rung 4 (#101, aggregation error).
Proof: ε/3 diagonal argument in the ε-N form + triangle inequality (`abs_sub_le`). -/
theorem erdos858_diagonal_squeeze :
    ∀ (W : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (L : ℝ) (A : ℕ → ℝ),
      (∀ K : ℕ, Filter.Tendsto (fun N => W K N) Filter.atTop (nhds (R K))) →
      Filter.Tendsto R Filter.atTop (nhds L) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
      Filter.Tendsto A Filter.atTop (nhds L) := by
  intro W R L A hW hR herr
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0:ℝ) < ε / 3 := by linarith
  have hRK : ∀ᶠ K in Filter.atTop, dist (R K) L < ε / 3 :=
    Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp hR (ε / 3) hε3)
  obtain ⟨K, hRL, hAW⟩ := (hRK.and (herr (ε / 3) hε3)).exists
  rw [Real.dist_eq] at hRL
  obtain ⟨Nb, hNb⟩ := Metric.tendsto_atTop.mp (hW K) (ε / 3) hε3
  obtain ⟨Na, hNa⟩ := Filter.eventually_atTop.mp hAW
  refine ⟨max Na Nb, fun N hN => ?_⟩
  have he1 : |A N - W K N| ≤ ε / 3 := hNa N (le_of_max_le_left hN)
  have he2 : dist (W K N) (R K) < ε / 3 := hNb N (le_of_max_le_right hN)
  rw [Real.dist_eq] at he2 ⊢
  linarith [abs_sub_le (A N) (W K N) L, abs_sub_le (W K N) (R K) L, he1, he2, hRL]

end Erdos858
