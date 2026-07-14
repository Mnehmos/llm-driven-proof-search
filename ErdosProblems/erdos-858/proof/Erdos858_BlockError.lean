/-
Erdős Problem #858 — §5.4 Riemann-sum ladder rung B (Chojecki 2026).

`intervalIntegral_sub_rectangle_bound` (unit_partition_block_error): the single-block
rectangle estimate. If `f` is within `ε` of a constant `c` throughout `[a,b]`
(`a ≤ b`), then the integral of `f` over the block is within `ε·(b−a)` of the
rectangle `(b−a)·c`:
  `|∫_a^b f − (b−a)·c| ≤ ε·(b−a)`.
The reusable rectangle-error bound for the left-endpoint Riemann sum (toward the
generic log-harmonic Riemann-sum theorem and Theorem 1.2).

Proof: `∫_a^b f − (b−a)c = ∫_a^b (f−c)` (`integral_sub` + `integral_const`), and
`|∫_a^b (f−c)| ≤ ε·|b−a| = ε(b−a)` via
`intervalIntegral.norm_integral_le_of_norm_le_const` with the pointwise bound
`|f−c| ≤ ε`. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 59964e3b-17b5-434e-9f47-cafc2bf9dace,
  problem_version_id 8311adb0-33a6-4472-8b8b-2dfaa6ffc4f4.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7bbc6e5119a588f446b52373a5904e5481f9bc5776d8cf541e9c471cf93d6dce.
-/
import Mathlib

namespace Erdos858

/-- Ladder rung B (block rectangle error): if `|f − c| ≤ ε` on `[a,b]` (`a ≤ b`, `f`
integrable), then `|∫_a^b f − (b−a)·c| ≤ ε·(b−a)`. The rectangle-error bound for the
left-endpoint Riemann sum. -/
theorem erdos858_intervalIntegral_sub_rectangle_bound :
    ∀ (f : ℝ → ℝ) (a b c ε : ℝ), a ≤ b → IntervalIntegrable f MeasureTheory.volume a b →
      (∀ x ∈ Set.Icc a b, |f x - c| ≤ ε) → |(∫ x in a..b, f x) - (b - a) * c| ≤ ε * (b - a) := by
  intro f a b c ε hab hint hbound
  have hc_int : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume a b := intervalIntegrable_const
  have hsub : (∫ x in a..b, f x) - (b - a) * c = ∫ x in a..b, (f x - c) := by
    rw [intervalIntegral.integral_sub hint hc_int, intervalIntegral.integral_const, smul_eq_mul]
  have hnorm : ‖∫ x in a..b, (f x - c)‖ ≤ ε * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    rw [Real.norm_eq_abs]
    exact hbound x (Set.Ioc_subset_Icc_self hx)
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at hnorm
  rw [hsub, ← Real.norm_eq_abs]
  exact hnorm

end Erdos858
