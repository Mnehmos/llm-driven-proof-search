/-
Erdős Problem #858 — Theorem 1.2 assembly, A6-herr discharge (Chojecki 2026).

`interval transfer error → herr`: the `herr` input of the interval log-harmonic
transfer capstone A6, via the generic mass-normalized herr atom #140. With
  - `mass_N = (Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} 1/a)/log N → t − s ≥ 0`  (from #99);
  - the fine-scale aggregation `∀ η>0, ∀ᶠ K, ∀ N, |A_N − W_KN| ≤ η·mass_N`
    (from the arithmetic-block oscillation of `f` with block width → 0),
#140 yields the herr hypothesis of A6:
  `∀ ε>0, ∀ᶠ K, ∀ᶠ N, |A_N − W_KN| ≤ ε`,
where `A_N = (Σ f(log a/log N)/a)/log N`, `W_KN = (Σ_j f(v_j)·(harmonic mass))/log N`.

Proof: direct #140 application at the concrete log-harmonic `A`/`W`/`mass` with
`L = t − s` (mirror of the §5.3 herr #146).

Kernel-verified via the proofsearch MCP:
  episode 7f227c5c-e5b2-45eb-a5bb-99bde37704ca,
  problem_version_id 4ecdc836-75bf-4d92-b3e3-8dbbad1972a1.
Outcome: kernel_verified / root_kernel_verified (v2, 1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7be377203f2efc75fff7cac3a23539631e7a3430b3c31fce34eb948c20b7c6a0.

**Lean lesson** (v1 fail → v2): the recurring `∀ᶠ N` binder-inference bug — a bare
`(N:ℝ)` under `∀ᶠ N in atTop` in the conclusion lets Lean infer `N : ℝ`, mismatching
#140's `N : ℕ` output. Fix (as in #141 v2): annotate `∀ᶠ (N : ℕ)` in the conclusion.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6-herr discharge: from #140 (mass-normalized herr) + the total-mass
limit (`→ t−s`, #99) + the aggregation, the herr hypothesis of the interval transfer
capstone A6: `∀ ε>0, ∀ᶠ K, ∀ᶠ (N:ℕ), |A_N − W_KN| ≤ ε`. Direct #140 application. -/
theorem erdos858_thm12_a6_herr :
    ∀ (f : ℝ → ℝ) (s t : ℝ), s ≤ t →
      (∀ (A : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (mass : ℕ → ℝ) (L : ℝ),
        0 ≤ L → Filter.Tendsto mass Filter.atTop (nhds L) →
        (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ, |A N - W K N| ≤ η * mass N) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
      Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, 1/(a:ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds (t - s)) →
      (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)|
        ≤ η * ((∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, 1/(a:ℝ)) / Real.log (N:ℝ))) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ (N : ℕ) in Filter.atTop,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)|
        ≤ ε := by
  intro f s t hst h140 hmasslim hAgg
  exact h140 (fun N => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) (fun K N => (∑ j ∈ Finset.range K, f (s + ((j:ℝ)/(K:ℝ))*(t-s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ)+1)/(K:ℝ))*(t-s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ)/(K:ℝ))*(t-s))⌋₊ : ℝ))) / Real.log (N:ℝ)) (fun N => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, 1/(a:ℝ)) / Real.log (N:ℝ)) (t - s) (by linarith) hmasslim hAgg

end Erdos858
