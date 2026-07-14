/-
Erdős Problem #858 — §5.4 Riemann-sum ladder, DURABLE THEOREM rung D (Chojecki 2026).

`left_uniform_sum_tendsto_intervalIntegral`: **for every continuous `f` on `[0,1]`,
the equispaced left-endpoint Riemann sums converge to the interval integral**:
  `R_K(f) = (1/K) Σ_{j=0}^{K-1} f(j/K)  →  ∫₀¹ f`   as `K → ∞`.

This is the reusable, campaign-independent core of the logarithmic Riemann-sum
theorem (the log-harmonic weighting is layered on next, toward Theorem 1.2). It is
built ENTIRELY FROM SCRATCH: the pinned Mathlib has no equispaced-Riemann-sum →
integral lemma for continuous `f` (only the heavy `BoxIntegral` machinery). The
proof is specialized and ε-first (no general Riemann/tagged-partition theory).

Conditional on the two kernel-verified atoms (taken as hypotheses because
problem_versions cannot cross-reference):
  • rung A `erdos858_intervalIntegral_eq_sum_unit_partition` (#93):
      `∫₀¹f = Σ_j ∫_{j/K}^{(j+1)/K} f`;
  • rung C′ `erdos858_block_var_fixedK_error` (#96):
      block-variation `≤ ε'` ⟹ `|∫₀¹f − R_K(f)| ≤ ε'`.

Proof (ε-first): `f` is uniformly continuous on the compact `[0,1]`
(`isCompact_Icc.uniformContinuousOn_of_continuous`), giving `δ` for `ε/2`; choose
`K₀` with `1/K₀ < δ` (`exists_nat_gt`); for `K ≥ max 1 K₀` the block width `1/K < δ`
forces the variation `|f x − f(j/K)| ≤ ε/2` on each block (via the `δ`-modulus, both
`x` and `j/K` in `[0,1]`); rung C′ then gives `|∫₀¹f − R_K| ≤ ε/2 < ε`, i.e.
`dist(R_K, ∫₀¹f) < ε` (`Metric.tendsto_atTop`). Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 08999b32-dd97-4b87-8101-21b54657a28e,
  problem_version_id 6098e0c1-f2b8-418c-a6e4-8ae22ca1016c.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash fc8532d113501a639067477ebd4bf979a7f7a7d9d5b668d8eadc41f866bc0358.
-/
import Mathlib

namespace Erdos858

/-- **Durable theorem** (left uniform Riemann sums → integral): for continuous `f`
on `[0,1]`, `R_K(f) = (1/K) Σ_{j=0}^{K-1} f(j/K) → ∫₀¹ f`. Built from scratch
(specialized, ε-first), conditional on the verified partition identity (#93) and
block-variation⟹error assembly (#96). The reusable core of the §5.4 logarithmic
Riemann-sum theorem toward Theorem 1.2. -/
theorem erdos858_left_uniform_sum_tendsto_intervalIntegral :
    ∀ f : ℝ → ℝ, ContinuousOn f (Set.Icc (0:ℝ) 1) →
      (∀ (K:ℕ), 0 < K → (∫ x in (0:ℝ)..1, f x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) →
      (∀ (K:ℕ) (ε':ℝ), 0 < K → 0 ≤ ε' → ((∫ x in (0:ℝ)..1, f x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) →
        (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f x - f ((j:ℝ)/K)| ≤ ε') →
        |(∫ x in (0:ℝ)..1, f x) - (1/K) * ∑ j ∈ Finset.range K, f ((j:ℝ)/K)| ≤ ε') →
      Filter.Tendsto (fun K : ℕ => (1/(K:ℝ)) * ∑ j ∈ Finset.range K, f ((j:ℝ)/K)) Filter.atTop (nhds (∫ x in (0:ℝ)..1, f x)) := by
  intro f hcont hpart hCprime
  have hunif : UniformContinuousOn f (Set.Icc (0:ℝ) 1) := isCompact_Icc.uniformContinuousOn_of_continuous hcont
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨δ, hδ0, hδ⟩ := hunif (ε/2) (by linarith)
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (1/δ)
  refine ⟨max 1 K₀, fun K hK => ?_⟩
  have hKpos : 0 < K := le_trans (le_max_left 1 K₀) hK
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
  have hKK₀ : (K₀:ℝ) ≤ (K:ℝ) := by exact_mod_cast (le_trans (le_max_right 1 K₀) hK)
  have hinvK : 1/(K:ℝ) < δ := by
    have h1 : (1:ℝ)/δ < K := lt_of_lt_of_le hK₀ hKK₀
    rw [div_lt_iff₀ hδ0] at h1
    rw [div_lt_iff₀ hKR]
    linarith [h1, mul_comm (K:ℝ) δ]
  have hvar : ∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f x - f ((j:ℝ)/K)| ≤ ε/2 := by
    intro j hj x hx
    rw [Finset.mem_range] at hj
    have h0jK : (0:ℝ) ≤ (j:ℝ)/K := by positivity
    have hxmem : x ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨by linarith [hx.1], ?_⟩
      have hub : ((j:ℝ)+1)/K ≤ 1 := by rw [div_le_one hKR]; exact_mod_cast hj
      linarith [hx.2]
    have hjmem : (j:ℝ)/K ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨h0jK, ?_⟩
      rw [div_le_one hKR]; exact_mod_cast hj.le
    have h1K : (0:ℝ) < 1/K := by positivity
    have hxj : |x - (j:ℝ)/K| ≤ 1/K := by
      rw [abs_le]
      refine ⟨by linarith [hx.1, h1K], ?_⟩
      have hw : ((j:ℝ)+1)/K = (j:ℝ)/K + 1/K := by ring
      have hx2 := hx.2
      rw [hw] at hx2
      linarith
    have hdist : dist x ((j:ℝ)/K) < δ := by rw [Real.dist_eq]; exact lt_of_le_of_lt hxj hinvK
    have hfd := hδ x hxmem ((j:ℝ)/K) hjmem hdist
    rw [Real.dist_eq] at hfd
    exact le_of_lt hfd
  have hbound := hCprime K (ε/2) hKpos (by linarith) (hpart K hKpos) hvar
  rw [Real.dist_eq, abs_sub_comm]
  linarith [hbound]

end Erdos858
