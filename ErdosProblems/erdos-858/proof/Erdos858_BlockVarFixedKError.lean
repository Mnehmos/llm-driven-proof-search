/-
Erdős Problem #858 — §5.4 Riemann-sum ladder, assembly rung C′ (Chojecki 2026).

Block-variation ⟹ fixed-K error. Given `f` continuous on `[0,1]`, the uniform
partition identity `∫₀¹f = Σ_j ∫_{j/K}^{(j+1)/K}f` (rung A, hypothesis), and the
block variation `|f x − f(j/K)| ≤ ε` for `x` in the `j`-th block (supplied by uniform
continuity in rung D), the left-endpoint Riemann sum `R_K(f) = (1/K) Σ_j f(j/K)`
satisfies `|∫₀¹f − R_K(f)| ≤ ε`.

This inlines rung B (per-block rectangle error, each block width `1/K`, so
`|∫_block f − (1/K)f(j/K)| ≤ ε/K`) and rung C (the Finset triangle sum `Σ (ε/K) = ε`).
It is the key assembly converting a variation bound into the fixed-K error, so the
durable convergence theorem (rung D) needs only uniform continuity on top. Elementary,
no PNT.

Kernel-verified via the proofsearch MCP:
  episode fb1d47f0-ba61-4f0c-b3a0-afdfe44453b2,
  problem_version_id 2bf46596-ea3b-4a5f-a236-8290b0babb1c.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bcf237155799c1ade023cd5ad8f8314b6ed4c83069de12b03f06734af646ddbd.
-/
import Mathlib

namespace Erdos858

/-- Ladder rung C′ (block-variation ⟹ fixed-K error): given `f` continuous on `[0,1]`,
the partition identity, and `|f x − f(j/K)| ≤ ε` on each block, the left-endpoint
Riemann sum satisfies `|∫₀¹f − (1/K)Σ_j f(j/K)| ≤ ε`. Inlines the block rectangle
error (rung B) and the Finset triangle sum (rung C). -/
theorem erdos858_block_var_fixedK_error :
    ∀ (f : ℝ → ℝ) (K : ℕ) (ε : ℝ), 0 < K → 0 ≤ ε → ContinuousOn f (Set.Icc (0:ℝ) 1) →
      ((∫ x in (0:ℝ)..1, f x) = ∑ j ∈ Finset.range K, ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) →
      (∀ j ∈ Finset.range K, ∀ x ∈ Set.Icc ((j:ℝ)/K) (((j:ℝ)+1)/K), |f x - f ((j:ℝ)/K)| ≤ ε) →
      |(∫ x in (0:ℝ)..1, f x) - (1/K) * ∑ j ∈ Finset.range K, f ((j:ℝ)/K)| ≤ ε := by
  intro f K ε hK hε hcont hpart hvar
  have hle : (0:ℝ) ≤ 1 := zero_le_one
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hKR' : (K:ℝ) ≠ 0 := ne_of_gt hKR
  have hcont' : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by rwa [Set.uIcc_of_le hle]
  have hblock : ∀ j ∈ Finset.range K, |(∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) - (1/K) * f ((j:ℝ)/K)| ≤ ε/K := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hmono : (j:ℝ)/K ≤ ((j:ℝ)+1)/K := (div_le_div_iff_of_pos_right hKR).mpr (by linarith)
    have hsub : Set.uIcc ((j:ℝ)/K) (((j:ℝ)+1)/K) ⊆ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le hmono, Set.uIcc_of_le hle]
      apply Set.Icc_subset_Icc
      · positivity
      · rw [div_le_one hKR]; exact_mod_cast hj
    have hintblock : IntervalIntegrable f MeasureTheory.volume ((j:ℝ)/K) (((j:ℝ)+1)/K) := (hcont'.mono hsub).intervalIntegrable
    have hc_int : IntervalIntegrable (fun _ : ℝ => f ((j:ℝ)/K)) MeasureTheory.volume ((j:ℝ)/K) (((j:ℝ)+1)/K) := intervalIntegrable_const
    have hwidth : ((j:ℝ)+1)/K - (j:ℝ)/K = 1/K := by ring
    have hsubint : (∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) - (1/K) * f ((j:ℝ)/K) = ∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), (f x - f ((j:ℝ)/K)) := by
      rw [intervalIntegral.integral_sub hintblock hc_int, intervalIntegral.integral_const, smul_eq_mul, hwidth]
    have hnorm : ‖∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), (f x - f ((j:ℝ)/K))‖ ≤ ε * |((j:ℝ)+1)/K - (j:ℝ)/K| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hmono] at hx
      rw [Real.norm_eq_abs]
      exact hvar j (Finset.mem_range.mpr hj) x (Set.Ioc_subset_Icc_self hx)
    rw [abs_of_nonneg (by linarith [hmono] : (0:ℝ) ≤ ((j:ℝ)+1)/K - (j:ℝ)/K), hwidth] at hnorm
    rw [← Real.norm_eq_abs, hsubint]
    exact hnorm.trans_eq (by ring)
  rw [hpart, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc |∑ j ∈ Finset.range K, ((∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) - (1/K) * f ((j:ℝ)/K))|
      ≤ ∑ j ∈ Finset.range K, |(∫ x in ((j:ℝ)/K)..(((j:ℝ)+1)/K), f x) - (1/K) * f ((j:ℝ)/K)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range K, ε/K := Finset.sum_le_sum hblock
    _ = ε := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

end Erdos858
