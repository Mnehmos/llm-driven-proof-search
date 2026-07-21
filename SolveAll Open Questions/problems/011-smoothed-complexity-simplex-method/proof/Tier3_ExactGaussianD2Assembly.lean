/-
SolveAll #11 — exact one-sample Gaussian event for the dimension-two lower bound.

The preceding event theorem accepts coordinate Gaussian laws as hypotheses.
Here those laws are derived from the exact same product of translated/scaled
augmented-row laws on which affine general position holds almost surely.  Thus
the row tails and genericity are properties of one joint smoothing sample.
-/
import Tier3_D2TailGenericityAssembly
import Tier3_GaussianAffineGenericityAssembly

open MeasureTheory ProbabilityTheory WithLp
open scoped ENNReal NNReal

namespace SolveAll011.Tier3

/-- A scaled coordinate of a standard Euclidean Gaussian has variance `τ²`. -/
theorem stdGaussian_scaled_coordinate_law
    {ι : Type*} [Fintype ι] (i : ι) (τ : ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun g => τ * g i) =
      gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) := by
  let ν : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 1)
  calc
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun g => τ * g i) =
        (ν.map (toLp 2)).map (fun g => τ * g i) := by
      rw [map_pi_eq_stdGaussian]
    _ = ν.map (fun x => τ * x i) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (ν.map (Function.eval i)).map (fun x => τ * x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (gaussianReal 0 1).map (fun x => τ * x) := by
      rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq]
    _ = gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · apply NNReal.eq
        change τ ^ 2 * 1 = τ ^ 2
        ring

/-- Centering one coordinate of a translated/scaled augmented row recovers the
centered `N(0,τ²)` law. -/
theorem augmentedRowLaw_centered_coordinate
    (d : ℕ) (center : EuclideanSpace ℝ (Fin (d + 1)))
    (τ : ℝ) (i : Fin (d + 1)) :
    (augmentedRowLaw d center τ).map (fun x => (x - center) i) =
      gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) := by
  calc
    (augmentedRowLaw d center τ).map (fun x => (x - center) i) =
        ((stdGaussian (EuclideanSpace ℝ (Fin (d + 1)))).map
          (fun g => center + τ • g)).map (fun x => (x - center) i) := by rfl
    _ = (stdGaussian (EuclideanSpace ℝ (Fin (d + 1)))).map
        (fun g => τ * g i) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext g
      simp
    _ = gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) :=
      stdGaussian_scaled_coordinate_law i τ

/-- A coordinate of one row under the joint product law has the required
centered Gaussian perturbation law. -/
theorem pi_augmentedRowLaw_centered_coordinate
    {ρ : Type*} [Fintype ρ]
    (center : ρ → EuclideanSpace ℝ (Fin 3)) (τ : ℝ)
    (r : ρ) (i : Fin 3) :
    (Measure.pi (fun j : ρ => augmentedRowLaw 2 (center j) τ)).map
        (fun rows => (rows r - center r) i) =
      gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) := by
  letI : ∀ j : ρ, IsProbabilityMeasure (augmentedRowLaw 2 (center j) τ) :=
    fun j => by
      rw [augmentedRowLaw]
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  let μ : Measure (ρ → EuclideanSpace ℝ (Fin 3)) :=
    Measure.pi (fun j : ρ => augmentedRowLaw 2 (center j) τ)
  calc
    (Measure.pi (fun j : ρ => augmentedRowLaw 2 (center j) τ)).map
        (fun rows => (rows r - center r) i) =
      (μ.map (Function.eval r)).map (fun x => (x - center r) i) := by
        change μ.map (fun rows => (rows r - center r) i) = _
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
    _ = (augmentedRowLaw 2 (center r) τ).map
        (fun x => (x - center r) i) := by
      rw [(measurePreserving_eval
        (fun j : ρ => augmentedRowLaw 2 (center j) τ) r).map_eq]
    _ = gaussianReal 0 (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) :=
      augmentedRowLaw_centered_coordinate 2 (center r) τ i

/-- First two coordinates of an augmented-row perturbation. -/
noncomputable def d2NormalNoise
    {ρ : Type*} (center : ρ → EuclideanSpace ℝ (Fin 3))
    (r : ρ) (rows : ρ → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) :=
  toLp 2 (fun i : Fin 2 => (rows r - center r) i.castSucc)

/-- Last coordinate of an augmented-row perturbation, packaged as a
one-dimensional Euclidean vector for the common finite-row tail theorem. -/
noncomputable def d2RhsNoise
    {ρ : Type*} (center : ρ → EuclideanSpace ℝ (Fin 3))
    (r : ρ) (rows : ρ → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 1) :=
  toLp 2 (fun _ : Fin 1 => (rows r - center r) (Fin.last 2))

/-- End-to-end one-sample probability assembly: under the exact product law of
translated/scaled augmented Gaussian rows, simultaneous normal/RHS tail control
and affine general position fail with probability at most `n⁻²` in dimension
two. -/
theorem exact_d2_tail_and_generic_failure_le
    {κ : Type} [Fintype κ]
    (I : Finset κ) (center : κ → EuclideanSpace ℝ (Fin 3))
    (τ : ℝ) (hτ : 0 < τ) (hn : 2 ≤ I.card) :
    let P : I → Measure (EuclideanSpace ℝ (Fin 3)) :=
      fun i => augmentedRowLaw 2 (center i) τ
    let μ : Measure (I → EuclideanSpace ℝ (Fin 3)) := Measure.pi P
    let generic : Set (I → EuclideanSpace ℝ (Fin 3)) :=
      {rows | ∀ J : Finset κ, ∀ hJI : J ⊆ I, J.card ≤ 3 →
        LinearIndependent ℝ (fun j : J => rows ⟨j, hJI j.property⟩)}
    μ.real
      (({rows | ∃ r,
          Real.sqrt (Fintype.card (Fin 2)) *
              (4 * τ * Real.sqrt (Real.log I.card)) <
            ‖d2NormalNoise (fun i : I => center i) r rows‖} ∪
        {rows | ∃ r,
          Real.sqrt (Fintype.card (Fin 1)) *
              (4 * τ * Real.sqrt (Real.log I.card)) <
            ‖d2RhsNoise (fun i : I => center i) r rows‖}) ∪
        genericᶜ) ≤
      1 / (I.card : ℝ) ^ 2 := by
  dsimp only
  let P : I → Measure (EuclideanSpace ℝ (Fin 3)) :=
    fun i => augmentedRowLaw 2 (center i) τ
  let μ : Measure (I → EuclideanSpace ℝ (Fin 3)) := Measure.pi P
  let generic : Set (I → EuclideanSpace ℝ (Fin 3)) :=
    {rows | ∀ J : Finset κ, ∀ hJI : J ⊆ I, J.card ≤ 3 →
      LinearIndependent ℝ (fun j : J => rows ⟨j, hJI j.property⟩)}
  letI : ∀ i : I, IsProbabilityMeasure (P i) := fun i => by
    dsimp [P]
    rw [augmentedRowLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hgeneric : ∀ᵐ rows ∂μ, rows ∈ generic := by
    dsimp [μ, generic, P]
    simpa using ae_augmentedGaussianRows_every_subset_linearIndependent
      2 center τ hτ.ne' I
  apply d2_tail_and_ae_generic_failure_le μ
    (d2NormalNoise (fun i : I => center i))
    (d2RhsNoise (fun i : I => center i)) generic I.card hn (by simp) τ hτ
  · intro r i
    change AEMeasurable (fun rows => (rows r - center r) i.castSucc) μ
    have hsub : Measurable
        (fun rows : I → EuclideanSpace ℝ (Fin 3) => rows r - center r) :=
      (measurable_pi_apply r).sub measurable_const
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i.castSucc).measurable.comp
      hsub).aemeasurable
  · intro r i
    simpa [μ, P, d2NormalNoise] using
      pi_augmentedRowLaw_centered_coordinate
        (fun j : I => center j) τ r i.castSucc
  · intro r i
    change AEMeasurable (fun rows => (rows r - center r) (Fin.last 2)) μ
    have hsub : Measurable
        (fun rows : I → EuclideanSpace ℝ (Fin 3) => rows r - center r) :=
      (measurable_pi_apply r).sub measurable_const
    exact ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last 2)).measurable.comp
      hsub).aemeasurable
  · intro r i
    simpa [μ, P, d2RhsNoise] using
      pi_augmentedRowLaw_centered_coordinate
        (fun j : I => center j) τ r (Fin.last 2)
  · exact hgeneric

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.stdGaussian_scaled_coordinate_law
#print axioms SolveAll011.Tier3.augmentedRowLaw_centered_coordinate
#print axioms SolveAll011.Tier3.pi_augmentedRowLaw_centered_coordinate
#print axioms SolveAll011.Tier3.exact_d2_tail_and_generic_failure_le
