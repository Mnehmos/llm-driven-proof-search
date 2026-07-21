/-
Erdős Problem #858 — Theorem 1.2 assembly, atom A6 (interval log-harmonic transfer, Chojecki 2026).

`interval log-harmonic Riemann transfer` (Lemma 5.4, general interval `[s,t]`):
given the diagonal two-limit squeeze (#102), the fixed-K weighted-block-sum limits
`hW` (the normalized harmonic-weighted block sum over the ARITHMETIC blocks
`v_j = s + (j/K)(t−s)` tends to the step-sum `Σ_j f(v_j)·((t−s)/K)`), the
Riemann step-sum limit `hR` (`Σ_j f(v_j)·((t−s)/K) → L`, the right-Riemann sum for
`∫_s^t f`), and the eventual transfer error `herr`, we conclude

  `(Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} f(log a/log N)/a) / log N  →  L`.

With `L = ∫_s^t f`, this is Chojecki's Lemma 5.4 on the general interval `[s,t]` —
the interval analogue of the verified full-range capstone #111 (which is `[0,1]`).
It is the transport engine for the tail Riemann sum
`Σ_{K*<a≤√N}(1−Φ)/a / log N → ∫_{α₂}^{1/2}(1−Φ) = I`, the last analytic input of the
Theorem 1.2 capstone A7. The Lebesgue measure (`(t−s)/K` per block, arithmetic
blocks, harmonic-difference masses `→ (t−s)/K`) is what makes the limit `∫_s^t f dv`
rather than the `dv/v` of the prime transfer (#141).

Proof: direct #102 application at the interval `A`/`W`/`R` quantities — exactly as
#111 (the generic diagonal squeeze is block-shape- and measure-agnostic).

Kernel-verified via the proofsearch MCP:
  episode 8b473e95-b22c-4714-95d9-c799b4369ad4,
  problem_version_id cedc4a2e-33a2-476e-b824-887988396dbc.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c6955bc901e1cb75e1775695793ef81f1c72ddd7b25f550de9402e7669b1ed9f.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 atom A6 (interval log-harmonic transfer, Lemma 5.4 on `[s,t]`): from
#102 + `hW` (harmonic-weighted block sum → step-sum, arithmetic blocks
`v_j=s+(j/K)(t−s)`) + `hR` (step-sum `Σ_j f(v_j)·((t−s)/K) → L`) + `herr`,
`(Σ_{a∈(⌊N^s⌋,⌊N^t⌋]} f(log a/log N)/a)/log N → L`. Interval analogue of #111
(`[0,1]`). Direct #102 application. -/
theorem erdos858_thm12_interval_transfer :
    ∀ (f : ℝ → ℝ) (s t L : ℝ),
      (∀ (W : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (L' : ℝ) (A : ℕ → ℝ),
        (∀ K : ℕ, Filter.Tendsto (fun N => W K N) Filter.atTop (nhds (R K))) →
        Filter.Tendsto R Filter.atTop (nhds L') →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
        Filter.Tendsto A Filter.atTop (nhds L')) →
      (∀ K : ℕ, Filter.Tendsto (fun N : ℕ => (∑ j ∈ Finset.range K, f (s + ((j:ℝ) / (K:ℝ)) * (t - s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ) + 1) / (K:ℝ)) * (t - s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ) / (K:ℝ)) * (t - s))⌋₊ : ℝ))) / Real.log (N:ℝ)) Filter.atTop (nhds (∑ j ∈ Finset.range K, f (s + ((j:ℝ) / (K:ℝ)) * (t - s)) * ((t - s) / (K:ℝ))))) →
      Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, f (s + ((j:ℝ) / (K:ℝ)) * (t - s)) * ((t - s) / (K:ℝ))) Filter.atTop (nhds L) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in Filter.atTop, ∀ᶠ N : ℕ in Filter.atTop,
        |(∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f (s + ((j:ℝ) / (K:ℝ)) * (t - s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ) + 1) / (K:ℝ)) * (t - s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ) / (K:ℝ)) * (t - s))⌋₊ : ℝ))) / Real.log (N:ℝ)| ≤ ε) →
      Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds L) := by
  intro f s t L h102 hW hR herr
  exact h102 (fun K N => (∑ j ∈ Finset.range K, f (s + ((j:ℝ) / (K:ℝ)) * (t - s)) * ((harmonic ⌊(N:ℝ) ^ (s + (((j:ℝ) + 1) / (K:ℝ)) * (t - s))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ (s + ((j:ℝ) / (K:ℝ)) * (t - s))⌋₊ : ℝ))) / Real.log (N:ℝ)) (fun K => ∑ j ∈ Finset.range K, f (s + ((j:ℝ) / (K:ℝ)) * (t - s)) * ((t - s) / (K:ℝ))) L (fun N => (∑ a ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) hW hR herr

end Erdos858
