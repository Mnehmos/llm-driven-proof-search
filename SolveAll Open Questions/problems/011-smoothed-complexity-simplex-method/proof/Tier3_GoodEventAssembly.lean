/-
SolveAll #11 — probability-event assembly for the Bach--Huiberts lower bound.

The quantitative row-tail event is not the only event needed by the geometric
argument: the normalized LP must also be in affine general position.  The
latter holds almost surely under the exact product-Gaussian perturbation law.
This file checks the measure-theoretic bookkeeping which is easy to state but
important for the final probability: intersecting with an almost-sure event
does not increase the failure probability at all.
-/
import Mathlib

open MeasureTheory

namespace SolveAll011.Tier3

/-- Adjoining failure of an almost-sure predicate to a quantitative bad event
does not change its real-valued measure.  No independence is required. -/
theorem measureReal_bad_union_ae_compl_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad generic : Set Ω) (hgeneric : ∀ᵐ ω ∂μ, ω ∈ generic) :
    μ.real (bad ∪ genericᶜ) = μ.real bad := by
  apply measureReal_congr
  filter_upwards [hgeneric] with ω hω
  apply propext
  constructor
  · intro h
    rcases h with hbad | hnot
    · exact hbad
    · exact False.elim (hnot hω)
  · exact Or.inl

/-- Failure-bound form of the tail/genericity conjunction. -/
theorem measureReal_bad_union_ae_compl_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad generic : Set Ω) (δ : ℝ)
    (hbad : μ.real bad ≤ δ) (hgeneric : ∀ᵐ ω ∂μ, ω ∈ generic) :
    μ.real (bad ∪ genericᶜ) ≤ δ := by
  rw [measureReal_bad_union_ae_compl_eq μ bad generic hgeneric]
  exact hbad

/-- Success-probability form.  The success event is `badᶜ ∩ generic`; under a
probability measure it has probability at least `1 - δ`. -/
theorem measureReal_ae_good_inter_compl_ge
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bad generic : Set Ω) (δ : ℝ)
    (hnull : NullMeasurableSet (bad ∪ genericᶜ) μ)
    (hbad : μ.real bad ≤ δ) (hgeneric : ∀ᵐ ω ∂μ, ω ∈ generic) :
    1 - δ ≤ μ.real (badᶜ ∩ generic) := by
  have hfailure : μ.real (bad ∪ genericᶜ) ≤ δ :=
    measureReal_bad_union_ae_compl_le μ bad generic δ hbad hgeneric
  have hcompl : (bad ∪ genericᶜ)ᶜ = badᶜ ∩ generic := by simp
  rw [← hcompl, probReal_compl_eq_one_sub₀ hnull]
  linarith

/-- Two separate quantitative bad events can be union-bounded before adding
the probability-one genericity event. -/
theorem measureReal_two_bad_union_ae_compl_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad₁ bad₂ generic : Set Ω) (δ₁ δ₂ : ℝ)
    (hbad₁ : μ.real bad₁ ≤ δ₁) (hbad₂ : μ.real bad₂ ≤ δ₂)
    (hgeneric : ∀ᵐ ω ∂μ, ω ∈ generic) :
    μ.real ((bad₁ ∪ bad₂) ∪ genericᶜ) ≤ δ₁ + δ₂ := by
  apply measureReal_bad_union_ae_compl_le μ (bad₁ ∪ bad₂) generic
  · exact (measureReal_union_le bad₁ bad₂).trans (add_le_add hbad₁ hbad₂)
  · exact hgeneric

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.measureReal_bad_union_ae_compl_eq
#print axioms SolveAll011.Tier3.measureReal_bad_union_ae_compl_le
#print axioms SolveAll011.Tier3.measureReal_ae_good_inter_compl_ge
#print axioms SolveAll011.Tier3.measureReal_two_bad_union_ae_compl_le
