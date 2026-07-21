/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 6 (Chojecki 2026).

`Ioc set-integral additivity` (generic): for `f` integrable on `(2,b]` and
`2 ≤ a ≤ b`,

  `∫_{(2,b]} f = ∫_{(2,a]} f + ∫_{(a,b]} f`.

Via `Set.Ioc_union_Ioc_eq_Ioc` + a direct `disjoint_left` proof +
`MeasureTheory.setIntegral_union`, with the piece-integrabilities from
`IntegrableOn.mono_set` (`Ioc_subset_Ioc_right` / `Ioc_subset_Ioc_left`).
Generic in `f`, so the o(1)-Mertens assembly can instantiate it at the
step-function integrand `A(t)/(t·log²t)` (integrability supplied separately),
converting the difference of two Mertens-2 split identities (#118) into the
interval Abel form.

Kernel-verified via the proofsearch MCP:
  episode b1d800f4-2da0-4086-97a5-686027b61407,
  problem_version_id 1b6a4e05-9d0b-41d3-a33a-8b864323fb49.
Outcome: kernel_verified / root_kernel_verified (2nd submission; the name
`Set.Ioc_disjoint_Ioc_same` does not exist in this pin — replaced by a direct
`Set.disjoint_left.mpr` term).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7908d194d0c2f9ed5819a196f3c282e556aadb6585d710abc6f279fcc8743526.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 6 (Ioc additivity, generic): `f` integrable on
`(2,b]`, `2 ≤ a ≤ b` ⟹ `∫_{(2,b]} f = ∫_{(2,a]} f + ∫_{(a,b]} f`. -/
theorem erdos858_ioc_integral_additivity :
    ∀ (f : ℝ → ℝ) (a b : ℝ), 2 ≤ a → a ≤ b →
      MeasureTheory.IntegrableOn f (Set.Ioc 2 b) MeasureTheory.volume →
      ∫ t in Set.Ioc (2:ℝ) b, f t = (∫ t in Set.Ioc (2:ℝ) a, f t) + ∫ t in Set.Ioc a b, f t := by
  intro f a b ha hab hint
  have hunion : Set.Ioc (2:ℝ) a ∪ Set.Ioc a b = Set.Ioc 2 b := Set.Ioc_union_Ioc_eq_Ioc ha hab
  have hdisj : Disjoint (Set.Ioc (2:ℝ) a) (Set.Ioc a b) := Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2.1))
  have hint1 : MeasureTheory.IntegrableOn f (Set.Ioc (2:ℝ) a) MeasureTheory.volume := hint.mono_set (Set.Ioc_subset_Ioc_right hab)
  have hint2 : MeasureTheory.IntegrableOn f (Set.Ioc a b) MeasureTheory.volume := hint.mono_set (Set.Ioc_subset_Ioc_left ha)
  rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2]

end Erdos858
