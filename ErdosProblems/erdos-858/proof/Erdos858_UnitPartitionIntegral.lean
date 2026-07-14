/-
Erdős Problem #858 — §5.4 Riemann-sum ladder rung A (Chojecki 2026).

`intervalIntegral_eq_sum_unit_partition`: the uniform partition identity. For
continuous `f` on `[0,1]` and `K ≥ 1`,
  `∫₀¹ f = Σ_{j=0}^{K-1} ∫_{j/K}^{(j+1)/K} f`,
splitting the unit-interval integral into the `K` equal subintervals over which the
left-endpoint Riemann sum is taken (toward the generic log-harmonic Riemann-sum
theorem, and thence Theorem 1.2).

Proof: `intervalIntegral.sum_integral_adjacent_intervals` with node map
`a(j) = j/K` (`a(0)=0`, `a(K)=1`); each block is integrable since `f` is continuous
on `[0,1] ⊇ [j/K,(j+1)/K]`. Specialized real-interval statement (no general Riemann
integration theory). Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode c7023983-da1f-4fcf-b874-803d1d6ede91,
  problem_version_id 34db60ec-201c-41fd-a003-c70580146dd4.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 842433e28a014c56daf2c7331c18cc36ccc6c2e5935ae1e5638bdc7bd8028e4b.
-/
import Mathlib

namespace Erdos858

/-- Ladder rung A (uniform partition identity): for continuous `f` on `[0,1]` and
`K ≥ 1`, `∫₀¹ f = Σ_{j=0}^{K-1} ∫_{j/K}^{(j+1)/K} f`. The K equal subintervals of the
left-endpoint Riemann sum. -/
theorem erdos858_intervalIntegral_eq_sum_unit_partition :
    ∀ (f : ℝ → ℝ) (K : ℕ), 0 < K → ContinuousOn f (Set.Icc (0:ℝ) 1) →
      (∑ j ∈ Finset.range K, ∫ x in ((j : ℝ)/K)..(((j : ℝ) + 1)/K), f x) = ∫ x in (0:ℝ)..1, f x := by
  intro f K hK hcont
  have hle : (0:ℝ) ≤ 1 := zero_le_one
  have hKR : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hcont' : ContinuousOn f (Set.uIcc (0:ℝ) 1) := by rwa [Set.uIcc_of_le hle]
  have hint : ∀ k, k < K → IntervalIntegrable f MeasureTheory.volume ((k:ℝ)/K) (((k+1:ℕ):ℝ)/K) := by
    intro k hk
    apply (hcont'.mono ?_).intervalIntegrable
    have hmono : (k:ℝ)/K ≤ ((k+1:ℕ):ℝ)/K := (div_le_div_iff_of_pos_right hKR).mpr (by exact_mod_cast Nat.le_succ k)
    rw [Set.uIcc_of_le hmono, Set.uIcc_of_le hle]
    apply Set.Icc_subset_Icc
    · positivity
    · rw [div_le_one hKR]; exact_mod_cast hk
  have key := intervalIntegral.sum_integral_adjacent_intervals (f := f) hint
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at key
  rw [div_self (ne_of_gt hKR)] at key
  exact key

end Erdos858
