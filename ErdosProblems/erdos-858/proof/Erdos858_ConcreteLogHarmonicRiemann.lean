/-
Erdős Problem #858 — §5.4 CAPSTONE: the concrete log-harmonic Riemann theorem
(Chojecki 2026, Lemma 5.4 in fixed-endpoint form).

`concrete log-harmonic Riemann theorem` (conditional assembly): given
  (i)   the diagonal two-limit squeeze (#102),
  (ii)  the fixed-K limit family `hW` — the normalized weighted block sum
        `(Σ_{j<K} f(j/K)·m_j(N))/log N` tends to the step-sum `Σ_{j<K} f(j/K)·(1/K)`
        (to be discharged from #98/#99/#100-style block-mass limits),
  (iii) the durable Riemann-sum limit (#97's conclusion: `(1/K)Σ_{j<K} f(j/K) → L`),
  (iv)  the eventual transfer error (#110's conclusion),
we conclude the transfer itself:

  `(Σ_{1<a≤N} f(log a/log N)/a) / log N  →  L`.

With `L = ∫₀¹ f`, this is the paper's Lemma 5.4 — the log-harmonic analogue of
the Riemann-sum theorem, carrying the normalized harmonic-weighted sum onto the
interval integral: the analytic transport engine for the asymptotic law
Theorem 1.2 (routed through §6 eventual frontier exactness). The full ladder
behind it, all kernel-verified in this campaign: the from-scratch pure
Riemann-sum theorem #92–#97, the abstract transfer engine #98–#102, and the
concrete assembly #103–#110.

Internal content: the `R_K`-form bridge `(1/K)·Σ_j f(j/K) = Σ_j f(j/K)·(1/K)`
(`Finset.sum_mul` + `ring`), transported along `Tendsto.congr'` with
`Filter.Eventually.of_forall`; then the squeeze applies directly (beta-defeq).

Kernel-verified via the proofsearch MCP:
  episode 754b73e8-1cba-4477-9a61-f8d28904e090,
  problem_version_id 161b53de-c21d-4e45-be2c-82673e20a15e.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 6bf04a07524df30ae82e4311c20e2f29374b8f13dbe249f286830d1c8beca48a.
-/
import Mathlib

namespace Erdos858

/-- §5.4 CAPSTONE (concrete log-harmonic Riemann theorem, conditional assembly):
given the diagonal squeeze (#102), the fixed-K weighted-block-sum limits (hW),
the durable Riemann-sum limit (#97), and the eventual transfer error (#110),
`(Σ_{1<a≤N} f(log a/log N)/a)/log N → L`. With `L = ∫₀¹ f` this is the paper's
Lemma 5.4 — the transport engine for Theorem 1.2. -/
theorem erdos858_concrete_log_harmonic_riemann :
    ∀ (f : ℝ → ℝ) (L : ℝ),
      (∀ (W : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (L' : ℝ) (A : ℕ → ℝ),
        (∀ K : ℕ, Filter.Tendsto (fun N => W K N) Filter.atTop (nhds (R K))) →
        Filter.Tendsto R Filter.atTop (nhds L') →
        (∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε) →
        Filter.Tendsto A Filter.atTop (nhds L')) →
      (∀ K : ℕ, Filter.Tendsto (fun N : ℕ => (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) / Real.log (N:ℝ)) Filter.atTop (nhds (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * (1 / (K:ℝ))))) →
      Filter.Tendsto (fun K : ℕ => (1 / (K:ℝ)) * ∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ))) Filter.atTop (nhds L) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in Filter.atTop, ∀ᶠ N : ℕ in Filter.atTop,
        |(∑ a ∈ Finset.Ioc 1 N, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)
          - (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) / Real.log (N:ℝ)| ≤ ε) →
      Filter.Tendsto (fun N : ℕ => (∑ a ∈ Finset.Ioc 1 N, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds L) := by
  intro f L h102 hW h97R herr
  have hReq : ∀ K : ℕ, (1 / (K:ℝ)) * ∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) = ∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * (1 / (K:ℝ)) := fun K => by rw [← Finset.sum_mul]; ring
  have hR' : Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * (1 / (K:ℝ))) Filter.atTop (nhds L) := h97R.congr' (Filter.Eventually.of_forall hReq)
  exact h102 (fun K N => (∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * ((harmonic ⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℝ) - (harmonic ⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℝ))) / Real.log (N:ℝ)) (fun K => ∑ j ∈ Finset.range K, f ((j:ℝ) / (K:ℝ)) * (1 / (K:ℝ))) L (fun N => (∑ a ∈ Finset.Ioc 1 N, f (Real.log (a:ℝ) / Real.log (N:ℝ)) / (a:ℝ)) / Real.log (N:ℝ)) hW hR' herr

end Erdos858
