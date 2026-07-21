/-
SolveAll #11 — exact Gaussian augmented-row genericity assembly.

This repository assembly composes the previously checked translated/scaled
Gaussian absolute-continuity theorem with the joint-product/projective-marginal
genericity theorem.  The result is one exact joint Gaussian smoothing sample in
which every selected augmented-row subset of size at most `d+1` is linearly
independent almost surely.
-/
import Tier3_GenericityProbability
import Milestone2_COND_ScaledGaussianAC

open MeasureTheory ProbabilityTheory

namespace SolveAll011.Tier3

/-- The translated scaled-Gaussian law of one augmented constraint row. -/
noncomputable def augmentedRowLaw
    (d : ℕ) (center : EuclideanSpace ℝ (Fin (d + 1))) (σ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin (d + 1))) :=
  (stdGaussian (EuclideanSpace ℝ (Fin (d + 1)))).map
    (fun g => center + σ • g)

/-- Exact joint-law affine genericity: independent Gaussian perturbations of
all augmented rows are simultaneously in general position on every subset of
size at most `d+1`. -/
theorem ae_augmentedGaussianRows_every_subset_linearIndependent
    {ι : Type} [Fintype ι]
    (d : ℕ) (center : ι → EuclideanSpace ℝ (Fin (d + 1)))
    (σ : ℝ) (hσ : σ ≠ 0) (I : Finset ι) :
    ∀ᵐ rows ∂Measure.pi (fun i : I => augmentedRowLaw d (center i) σ),
      ∀ J : Finset ι, ∀ hJI : J ⊆ I,
        J.card ≤ d + 1 →
        LinearIndependent ℝ (fun j : J => rows ⟨j, hJI j.property⟩) := by
  letI : ∀ i, IsProbabilityMeasure (augmentedRowLaw d (center i) σ) := fun i => by
    rw [augmentedRowLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hgeneric := ae_every_restrict_finset_linearIndependent_pi_volume
    (fun i => augmentedRowLaw d (center i) σ)
    (fun i => SolveAll011.M2COND.scaled_gaussian_ac (d + 1) (center i) σ hσ) I
  simpa using hgeneric

#print axioms ae_augmentedGaussianRows_every_subset_linearIndependent

end SolveAll011.Tier3
