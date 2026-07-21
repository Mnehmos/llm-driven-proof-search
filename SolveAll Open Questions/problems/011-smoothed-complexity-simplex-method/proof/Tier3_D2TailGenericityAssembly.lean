/-
SolveAll #11 — exact dimension-two tail/genericity event assembly.

This module combines the already-checked scalar-coordinate Gaussian tail
bounds with the probability-one affine-genericity event.  It spends `4n/n^8`
on the two coordinates of each perturbed normal and `2n/n^8` on the scalar
right-hand side.  Almost-sure genericity costs nothing, so the total failure
probability is at most `n⁻²`.
-/
import Tier3_GaussianTail
import Tier3_GoodEventAssembly
import Tier3_BachHuibertsD2Parameters

open MeasureTheory ProbabilityTheory

namespace SolveAll011.Tier3

/-- The full high-probability event needed before deterministic roundness and
incidence arguments are invoked in dimension two.  The two random fields may
be dependent: only their stated coordinate marginals are used. -/
theorem d2_tail_and_ae_generic_failure_le
    {ρ Ω : Type*} [Fintype ρ] [MeasurableSpace Ω]
    (μ : Measure Ω)
    (Anoise : ρ → Ω → EuclideanSpace ℝ (Fin 2))
    (bnoise : ρ → Ω → EuclideanSpace ℝ (Fin 1))
    (generic : Set Ω)
    (n : ℕ) (hn : 2 ≤ n) (hcard : Fintype.card ρ = n)
    (τ : ℝ) (hτ : 0 < τ)
    (hMeasA : ∀ r i, AEMeasurable (fun ω => Anoise r ω i) μ)
    (hlawA : ∀ r i, μ.map (fun ω => Anoise r ω i) =
      gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩)
    (hMeasb : ∀ r i, AEMeasurable (fun ω => bnoise r ω i) μ)
    (hlawb : ∀ r i, μ.map (fun ω => bnoise r ω i) =
      gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩)
    (hgeneric : ∀ᵐ ω ∂μ, ω ∈ generic) :
    μ.real
      (({ω | ∃ r,
          Real.sqrt (Fintype.card (Fin 2)) *
              (4 * τ * Real.sqrt (Real.log n)) < ‖Anoise r ω‖} ∪
        {ω | ∃ r,
          Real.sqrt (Fintype.card (Fin 1)) *
              (4 * τ * Real.sqrt (Real.log n)) < ‖bnoise r ω‖}) ∪
        genericᶜ) ≤
      1 / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := le_trans (by omega) hn
  have hA := measure_exists_norm_gt_four_mul_sqrt_log_le
    Anoise n hn1 τ hτ hMeasA hlawA
  have hb := measure_exists_norm_gt_four_mul_sqrt_log_le
    bnoise n hn1 τ hτ hMeasb hlawb
  calc
    μ.real
        (({ω | ∃ r,
            Real.sqrt (Fintype.card (Fin 2)) *
                (4 * τ * Real.sqrt (Real.log n)) < ‖Anoise r ω‖} ∪
          {ω | ∃ r,
            Real.sqrt (Fintype.card (Fin 1)) *
                (4 * τ * Real.sqrt (Real.log n)) < ‖bnoise r ω‖}) ∪
          genericᶜ) ≤
        (Fintype.card ρ : ℝ) * (Fintype.card (Fin 2) : ℝ) *
            (2 / (n : ℝ) ^ 8) +
          (Fintype.card ρ : ℝ) * (Fintype.card (Fin 1) : ℝ) *
            (2 / (n : ℝ) ^ 8) :=
      measureReal_two_bad_union_ae_compl_le μ _ _ generic _ _ hA hb hgeneric
    _ = 6 * (n : ℝ) / (n : ℝ) ^ 8 := by
      rw [hcard]
      simp only [Fintype.card_fin]
      ring
    _ ≤ 1 / (n : ℝ) ^ 2 := six_mul_n_div_n_pow_eight_le_inv_n_sq n hn

/-- Pointwise eliminator for the complement of the assembled failure event.
Once the two concrete tail thresholds are bounded by `η`, membership in the
good event supplies both row bounds and the genericity predicate. -/
theorem d2_good_event_implies_tail_bounds_and_generic
    {ρ Ω : Type*} [Fintype ρ]
    (Anoise : ρ → Ω → EuclideanSpace ℝ (Fin 2))
    (bnoise : ρ → Ω → EuclideanSpace ℝ (Fin 1))
    (generic : Set Ω) (n : ℕ) (τ η : ℝ) (ω : Ω)
    (hAη : Real.sqrt (Fintype.card (Fin 2)) *
        (4 * τ * Real.sqrt (Real.log n)) ≤ η)
    (hbη : Real.sqrt (Fintype.card (Fin 1)) *
        (4 * τ * Real.sqrt (Real.log n)) ≤ η)
    (hω : ω ∈
      ((({ω | ∃ r,
          Real.sqrt (Fintype.card (Fin 2)) *
              (4 * τ * Real.sqrt (Real.log n)) < ‖Anoise r ω‖} ∪
        {ω | ∃ r,
          Real.sqrt (Fintype.card (Fin 1)) *
              (4 * τ * Real.sqrt (Real.log n)) < ‖bnoise r ω‖}) ∪
        genericᶜ)ᶜ)) :
    (∀ r, ‖Anoise r ω‖ ≤ η) ∧
      (∀ r, ‖bnoise r ω‖ ≤ η) ∧ ω ∈ generic := by
  have hnot : ω ∉
      (({ω | ∃ r,
          Real.sqrt (Fintype.card (Fin 2)) *
              (4 * τ * Real.sqrt (Real.log n)) < ‖Anoise r ω‖} ∪
        {ω | ∃ r,
          Real.sqrt (Fintype.card (Fin 1)) *
              (4 * τ * Real.sqrt (Real.log n)) < ‖bnoise r ω‖}) ∪
        genericᶜ) := hω
  have hnotA : ¬ ∃ r,
      Real.sqrt (Fintype.card (Fin 2)) *
          (4 * τ * Real.sqrt (Real.log n)) < ‖Anoise r ω‖ := by
    intro h
    exact hnot (Or.inl (Or.inl h))
  have hnotb : ¬ ∃ r,
      Real.sqrt (Fintype.card (Fin 1)) *
          (4 * τ * Real.sqrt (Real.log n)) < ‖bnoise r ω‖ := by
    intro h
    exact hnot (Or.inl (Or.inr h))
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact (le_of_not_gt (fun h => hnotA ⟨r, h⟩)).trans hAη
  · intro r
    exact (le_of_not_gt (fun h => hnotb ⟨r, h⟩)).trans hbη
  · by_contra hgeneric
    exact hnot (Or.inr hgeneric)

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.d2_tail_and_ae_generic_failure_le
#print axioms SolveAll011.Tier3.d2_good_event_implies_tail_bounds_and_generic
