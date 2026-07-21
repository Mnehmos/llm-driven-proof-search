/-
Erdős Problem #858 — §5.3 prime-harmonic transfer CAPSTONE (Lemma 5.3, Chojecki 2026).

`prime-harmonic Riemann-sum transfer` (Lemma 5.3, conditional assembly): the
prime analogue of the §5.4 log-harmonic transfer (#111). Given
  - h102: the diagonal two-limit squeeze (#102, generic in A,W,R,L);
  - hW:   the fixed-K weighted-block-sum limit (each K, as N→∞, the geometric
          block step-sum → R_K)  — discharged from #100 + the geometric per-block
          prime mass limits #139;
  - hR:   the Riemann-Stieltjes step-sum limit R_K → L  — discharged from #138
          (hR bridge) via the durable #97 pullback at φ(x)=log(t/s)·G(s·(t/s)^x);
  - herr: the eventual transfer error (∀ε>0, ∀ᶠK, ∀ᶠN, |A_N − W_KN| ≤ ε)  —
          discharged from #140 (mass-normalized) + #136 aggregation + #134/#135
          mesh + #129 total mass;
conclude the prime-harmonic sum over the geometric block range converges:

  `Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} G(log a/log N)·[a prime]/a  →  L`.

With `L = ∫₀¹ log(t/s)·G(s·(t/s)^x) dx = ∫_s^t G(v)/v dv` (geometric change of
variables), this is the paper's Lemma 5.3 — the prime-harmonic Riemann-sum
theorem, the prime analogue of §5.4. The Meissel–Mertens constant cancels in the
interval form (as in #129), so this rides entirely on elementary Abel summation
plus the durable Riemann-sum→∫ engine (#92–#97) and the generic diagonal squeeze
(#102), with NO sharp-constant Mertens.

The concrete quantities passed to #102:
  W K N = Σ_{j<K} G(s·(t/s)^{j/K}) · (Σ_{a∈(⌊N^{v_j}⌋,⌊N^{v_{j+1}}⌋]} [a prime]/a),
  R K   = Σ_{j<K} G(s·(t/s)^{j/K}) · (log(t/s)/K),
  A N   = Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} G(log a/log N) · [a prime]/a,
  v_j   = s·(t/s)^{j/K}  (geometric grid, log-equispaced, constant block mass).

Proof: `intro G s t L h102 hW hR herr; exact h102 W R L A hW hR herr` with W/R/A
the explicit geometric lambdas — β-defeq unifies hW/hR/herr against #102's
expected hypothesis shapes.

Kernel-verified via the proofsearch MCP:
  episode 1cf150d2-95fe-4efd-8d6d-a7690e7ee5dd,
  problem_version_id 6da92549-46ff-438f-848e-964916a5f265.
Outcome: kernel_verified / root_kernel_verified (1st submission of v2).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 8333c9c8e72f09575fa94044248f5eec5aaadce3b90bdffe99e277820291fcaa.

**Lean lesson** (v1 kernel_fail → v2 fix): in the `herr` hypothesis a bare
`(N:ℝ)` coercion under a `∀ᶠ N in Filter.atTop` lets Lean infer `N : ℝ` (atTop on
ℝ, coercion becomes identity), while the conclusion's `fun N : ℕ` fixes `N : ℕ`.
The two `A` shapes then differ (ℝ- vs ℕ-indexed atTop), so the #102 application
fails to unify `herr` against the conclusion's `A`. Fix: annotate the binder
`∀ᶠ (N : ℕ) in Filter.atTop` in the herr hypothesis so every quantity carries
`N : ℕ` and #102 β-unifies. The discharge atoms (#140 etc.) all produce N:ℕ shapes.
-/
import Mathlib

namespace Erdos858

/-- §5.3 prime-harmonic transfer CAPSTONE (Lemma 5.3, conditional): from the
diagonal squeeze (#102), the fixed-K block-sum limit (hW), the Riemann-Stieltjes
limit (hR), and the eventual transfer error (herr), the prime-harmonic sum over
the geometric block range `(⌊N^s⌋,⌊N^t⌋]` converges to `L`. Prime analogue of the
§5.4 capstone #111. `intro … ; exact h102 W R L A hW hR herr`. -/
theorem erdos858_prime_harmonic_transfer_capstone :
    ∀ (G : ℝ → ℝ) (s t L : ℝ),
      (∀ (W : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (L' : ℝ) (A : ℕ → ℝ),
        (∀ K : ℕ, Filter.Tendsto (fun N => W K N) Filter.atTop (nhds (R K))) →
        Filter.Tendsto R Filter.atTop (nhds L') →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
        Filter.Tendsto A Filter.atTop (nhds L')) →
      (∀ K : ℕ, Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) Filter.atTop (nhds (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (Real.log (t/s) / (K:ℝ))))) →
      Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (Real.log (t/s) / (K:ℝ))) Filter.atTop (nhds L) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ (N : ℕ) in Filter.atTop, |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) - (∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0)))| ≤ ε) →
      Filter.Tendsto (fun N : ℕ => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) Filter.atTop (nhds L) := by
  intro G s t L h102 hW hR herr
  exact h102 (fun K N => ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^(s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊ ⌊(N:ℝ)^(s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))⌋₊, (if a.Prime then (1:ℝ)/(a:ℝ) else 0))) (fun K => ∑ j ∈ Finset.range K, G (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * (Real.log (t/s) / (K:ℝ))) L (fun N => ∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, G (Real.log (a:ℝ) / Real.log (N:ℝ)) * (if a.Prime then (1:ℝ)/(a:ℝ) else 0)) hW hR herr

end Erdos858
