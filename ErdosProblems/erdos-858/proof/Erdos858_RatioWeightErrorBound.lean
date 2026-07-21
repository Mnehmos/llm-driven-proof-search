/-
Erdős Problem #858 — semiprime uniform Riemann-sum upgrade, ASSEMBLY STEP (b),
part 1 (Chojecki 2026).

**Generic error bound**: given `C,L : ℝ → ℝ` with `|C(t)−L(t)| ≤ K` pointwise
on `(a,x]` (K explicit, nonnegative), and the needed integrability of
`gd·C`, `gd·L`, and `gd` on `Set.Ioc a x`,

  `|∫_{Ioc a x} gd(t)·C(t) dt − ∫_{Ioc a x} gd(t)·L(t) dt| ≤ K · ∫_{Ioc a x} |gd(t)| dt`.

This is the "pure bounding" half of the semiprime-wall assembly plan (see the
`erdos-858-campaign-state` memory PART 7): combined with the deterministic-
part capstone (`erdos858_deterministic_part_capstone`, which isolates exactly
`−∫gd·C dt + ∫gd·loglog dt` as the error term between the semiprime Abel sum
and the paper's target `∫g(v)/v dv`), instantiating `C := Σ_{p≤·}1/p`,
`L := loglog`, and `K` from the corpus's EXISTING qualitative Mertens-2
capstone (`erdos858_mertens2_capstone`, `|Σ_{p≤x}1/p − loglogx| ≤ [explicit]`,
no unknown constant) gives the full explicit error bound needed for the
literal uniform semiprime result.

Proof: `∫gd·C − ∫gd·L = ∫gd·(C−L)` (`MeasureTheory.integral_sub` + a
`funext`+`ring` congr to match the `gd·(C−L)` vs `gd·C−gd·L` forms), bounded
via `MeasureTheory.norm_integral_le_integral_norm` (‖·‖ converted to `|·|` via
`Real.norm_eq_abs`, since the library lemma is stated in norm form), then the
pointwise bound `|gd·(C−L)| ≤ |gd|·K` (`abs_mul` + `mul_le_mul_of_nonneg_left`,
keeping the shared `|gd t|` factor consistently on the LEFT throughout to
avoid ambiguous bare `mul_comm` rewrites) integrates via
`MeasureTheory.setIntegral_mono_on`, and `MeasureTheory.integral_mul_const`
pulls `K` out.

Kernel-verified via the proofsearch MCP:
  episode 68773e61-5a58-4d6d-8e6f-153b9e51a51c,
  problem_version_id 2194d9af-e8a5-4007-8fc8-b87f12a13da1.
Outcome: kernel_verified / root_proved (3rd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 5601e5debbc4c35c176958ccaa719d8fb351c797dcb603f813bda47ea554a356.

**Lean lessons**: (1) `MeasureTheory.norm_integral_le_integral_norm` is stated
with `‖·‖` (norm), not `|·|` (abs) — even for ℝ-valued integrands these are
not syntactically interchangeable for `exact`; bridge via
`simpa [Real.norm_eq_abs] using h`. (2) a bare `rw [mul_comm]` with no
argument is AMBIGUOUS — it rewrote only the goal's LHS occurrence
(`|gd t|*|C t−L t|` → `|C t−L t|*|gd t|`), leaving the RHS `K*|gd t|`
untouched, breaking the subsequent `mul_le_mul_of_nonneg_left` match (which
needs the shared factor on the same side of both sides of `≤`). Fix: keep the
shared factor (`|gd t|`) consistently on ONE side throughout the whole chain
(`.mul_const`/`integral_mul_const`, not `.const_mul`/`integral_const_mul`),
and apply only ONE unambiguous top-level `mul_comm` on two plain real numbers
at the very end (supplied as an explicit `linarith` hint, not an in-place
`rw`).
-/
import Mathlib

namespace Erdos858

/-- Generic error bound: given `|C(t)−L(t)|≤K` pointwise on `(a,x]` and the
needed integrability, `|∫gd·C − ∫gd·L| ≤ K·∫|gd|`. The pure-bounding half of
the semiprime-wall assembly, paired with `erdos858_deterministic_part_capstone`. -/
theorem erdos858_ratio_weight_error_bound :
    ∀ (gd C L : ℝ → ℝ) (K : ℝ) (a x : ℝ), a ≤ x → 0 ≤ K →
      MeasureTheory.IntegrableOn (fun t => gd t * C t) (Set.Ioc a x) MeasureTheory.volume →
      MeasureTheory.IntegrableOn (fun t => gd t * L t) (Set.Ioc a x) MeasureTheory.volume →
      MeasureTheory.IntegrableOn gd (Set.Ioc a x) MeasureTheory.volume →
      (∀ t ∈ Set.Ioc a x, |C t - L t| ≤ K) →
      |(∫ t in Set.Ioc a x, gd t * C t) - ∫ t in Set.Ioc a x, gd t * L t| ≤ K * ∫ t in Set.Ioc a x, |gd t| := by
  intro gd C L K a x hax hK hCint hLint hgdint hCL
  have heq : (fun t => gd t * C t - gd t * L t) = fun t => gd t * (C t - L t) := by funext t; ring
  have hCLint : MeasureTheory.IntegrableOn (fun t => gd t * (C t - L t)) (Set.Ioc a x) MeasureTheory.volume := by rw [← heq]; exact hCint.sub hLint
  have hsub : (∫ t in Set.Ioc a x, gd t * C t) - ∫ t in Set.Ioc a x, gd t * L t = ∫ t in Set.Ioc a x, gd t * (C t - L t) := by rw [← heq]; exact (MeasureTheory.integral_sub hCint hLint).symm
  rw [hsub]
  have hbound1 : |∫ t in Set.Ioc a x, gd t * (C t - L t)| ≤ ∫ t in Set.Ioc a x, |gd t * (C t - L t)| := by
    have h := MeasureTheory.norm_integral_le_integral_norm (μ := MeasureTheory.volume.restrict (Set.Ioc a x)) (fun t => gd t * (C t - L t))
    simpa [Real.norm_eq_abs] using h
  have hgdabs_int : MeasureTheory.IntegrableOn (fun t => |gd t|) (Set.Ioc a x) MeasureTheory.volume := hgdint.abs
  have hgdK_int : MeasureTheory.IntegrableOn (fun t => |gd t| * K) (Set.Ioc a x) MeasureTheory.volume := hgdabs_int.mul_const K
  have hCLabs_int : MeasureTheory.IntegrableOn (fun t => |gd t * (C t - L t)|) (Set.Ioc a x) MeasureTheory.volume := hCLint.abs
  have hpointwise : ∀ t ∈ Set.Ioc a x, |gd t * (C t - L t)| ≤ |gd t| * K := by
    intro t ht
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hCL t ht) (abs_nonneg _)
  have hbound2 : (∫ t in Set.Ioc a x, |gd t * (C t - L t)|) ≤ ∫ t in Set.Ioc a x, |gd t| * K := MeasureTheory.setIntegral_mono_on hCLabs_int hgdK_int measurableSet_Ioc hpointwise
  have heq2 : (∫ t in Set.Ioc a x, |gd t| * K) = (∫ t in Set.Ioc a x, |gd t|) * K := MeasureTheory.integral_mul_const K _
  have hcomm : (∫ t in Set.Ioc a x, |gd t|) * K = K * ∫ t in Set.Ioc a x, |gd t| := mul_comm _ _
  linarith [hbound1, hbound2, heq2, hcomm]

end Erdos858
