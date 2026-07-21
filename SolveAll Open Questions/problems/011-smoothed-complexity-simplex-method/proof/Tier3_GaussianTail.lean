/-
SolveAll #11 — Gaussian tail estimates for the Bach--Huiberts lower bound.

This module turns Mathlib's exact Gaussian moment-generating function into the
scalar Chernoff bound used to control the perturbation event.  It is kept
independent of the later matrix and polytope bookkeeping.
-/
import Mathlib

namespace SolveAll011.Tier3

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- Two-sided Chernoff bound for any random variable with a sub-Gaussian MGF.
No independence hypothesis is involved. -/
theorem measure_abs_ge_le_of_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * c)) := by
  have hupper := hX.measure_ge_le ht
  have hlower0 := hX.neg.measure_ge_le ht
  have hlower : μ.real {ω | X ω ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * c)) := by
    have hlower' : μ.real {ω | t ≤ -X ω} ≤ Real.exp (-t ^ 2 / (2 * c)) := by
      simpa only [Pi.neg_apply] using hlower0
    rw [show {ω : Ω | t ≤ -X ω} = {ω | X ω ≤ -t} by
      ext ω
      simp only [mem_setOf_eq]
      constructor <;> intro hω <;> linarith] at hlower'
    exact hlower'
  rw [show {ω : Ω | t ≤ |X ω|} = {ω | t ≤ X ω} ∪ {ω | X ω ≤ -t} by
    ext ω
    simp only [mem_setOf_eq, mem_union]
    rw [le_abs]
    constructor <;> intro hω
    · rcases hω with hω | hω
      · exact Or.inl hω
      · exact Or.inr (by linarith)
    · rcases hω with hω | hω
      · exact Or.inl hω
      · exact Or.inr (by linarith)]
  calc
    μ.real ({ω | t ≤ X ω} ∪ {ω | X ω ≤ -t}) ≤
        μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * c)) + Real.exp (-t ^ 2 / (2 * c)) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-t ^ 2 / (2 * c)) := by ring

/-- Finite-family sub-Gaussian union bound.  This is the probability interface
needed to control every scalar perturbation in a finite LP instance at once;
it deliberately assumes no independence. -/
theorem measure_exists_abs_ge_le_of_hasSubgaussianMGF
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ι → Ω → ℝ) (c : ℝ≥0)
    (hX : ∀ i, HasSubgaussianMGF (X i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ i, t ≤ |X i ω|} ≤
      (Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * c))) := by
  rw [show {ω : Ω | ∃ i, t ≤ |X i ω|} = ⋃ i, {ω | t ≤ |X i ω|} by
    ext ω
    simp]
  calc
    μ.real (⋃ i, {ω | t ≤ |X i ω|}) ≤
        ∑ i, μ.real {ω | t ≤ |X i ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, 2 * Real.exp (-t ^ 2 / (2 * c)) := by
      exact Finset.sum_le_sum fun i _ => measure_abs_ge_le_of_hasSubgaussianMGF (hX i) ht
    _ = (Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * c))) := by simp

/-- If every coordinate of a Euclidean vector is at most `t` in absolute
value, its Euclidean norm is at most `sqrt(dim) * t`. -/
theorem norm_le_sqrt_card_mul_of_forall_abs_le
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) {t : ℝ} (ht : 0 ≤ t)
    (hx : ∀ i, |x i| ≤ t) :
    ‖x‖ ≤ Real.sqrt (Fintype.card ι) * t := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, t ^ 2 := by
    exact Finset.sum_le_sum fun i _ => by
      rw [Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) ht).2 (hx i)
  calc
    √(∑ i, ‖x i‖ ^ 2) ≤ √(∑ _i : ι, t ^ 2) := Real.sqrt_le_sqrt hsum
    _ = √((Fintype.card ι : ℝ) * t ^ 2) := by simp
    _ = √(Fintype.card ι : ℝ) * √(t ^ 2) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    _ = √(Fintype.card ι : ℝ) * t := by rw [Real.sqrt_sq ht]

/-- Coordinatewise sub-Gaussian control implies a Euclidean-norm tail bound.
This is sufficient for the row-perturbation event in the lower-bound
construction and again uses only a union bound, not independence. -/
theorem measure_norm_gt_le_of_coordinate_hasSubgaussianMGF
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {μ : Measure Ω}
    (X : Ω → EuclideanSpace ℝ ι) (c : ℝ≥0)
    (hX : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | Real.sqrt (Fintype.card ι) * t < ‖X ω‖} ≤
      (Fintype.card ι : ℝ) * (2 * Real.exp (-t ^ 2 / (2 * c))) := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    let i0 : ι := Classical.choice hι
    letI : IsFiniteMeasure μ := by
      have hi := (hX i0).integrable_exp_mul 0
      simpa [integrable_const_iff] using hi
    apply (measureReal_mono ?_).trans
      (measure_exists_abs_ge_le_of_hasSubgaussianMGF
        (fun i ω => X ω i) c hX ht)
    intro ω hω
    by_contra hnot
    simp only [mem_setOf_eq, not_exists, not_le] at hnot
    exact (not_le_of_gt hω) (norm_le_sqrt_card_mul_of_forall_abs_le (X ω) ht fun i =>
      (hnot i).le)
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have hzero : ∀ ω, X ω = 0 := fun ω => Subsingleton.elim _ _
    simp [hzero]

/-- Simultaneous row-norm control for a finite family of Euclidean random
vectors.  The failure probability is at most `2 * rows * dim` times the scalar
Gaussian exponential factor. -/
theorem measure_exists_norm_gt_le_of_coordinate_hasSubgaussianMGF
    {ρ ι Ω : Type*} [Fintype ρ] [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} (X : ρ → Ω → EuclideanSpace ℝ ι) (c : ℝ≥0)
    (hX : ∀ r i, HasSubgaussianMGF (fun ω => X r ω i) c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ r, Real.sqrt (Fintype.card ι) * t < ‖X r ω‖} ≤
      (Fintype.card ρ : ℝ) * (Fintype.card ι : ℝ) *
        (2 * Real.exp (-t ^ 2 / (2 * c))) := by
  rw [show {ω : Ω | ∃ r, Real.sqrt (Fintype.card ι) * t < ‖X r ω‖} =
      ⋃ r, {ω | Real.sqrt (Fintype.card ι) * t < ‖X r ω‖} by
    ext ω
    simp]
  calc
    μ.real (⋃ r, {ω | Real.sqrt (Fintype.card ι) * t < ‖X r ω‖}) ≤
        ∑ r, μ.real {ω | Real.sqrt (Fintype.card ι) * t < ‖X r ω‖} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _r : ρ, (Fintype.card ι : ℝ) *
        (2 * Real.exp (-t ^ 2 / (2 * c))) := by
      exact Finset.sum_le_sum fun r _ =>
        measure_norm_gt_le_of_coordinate_hasSubgaussianMGF (X r) c (hX r) ht
    _ = (Fintype.card ρ : ℝ) * (Fintype.card ι : ℝ) *
        (2 * Real.exp (-t ^ 2 / (2 * c))) := by simp [mul_assoc]

/-- A centered real Gaussian with variance `v` has sub-Gaussian MGF parameter
`v`. -/
theorem hasSubgaussianMGF_id_gaussianReal_zero (v : ℝ≥0) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := by
    simpa [id_eq] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := v) t)
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- Transfer the centered-Gaussian sub-Gaussian certificate across an exact
pushforward-law statement. -/
theorem hasSubgaussianMGF_of_map_eq_gaussianReal_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} (v : ℝ≥0)
    (hX : AEMeasurable X μ) (hlaw : μ.map X = gaussianReal 0 v) :
    HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX]
  rw [hlaw]
  exact hasSubgaussianMGF_id_gaussianReal_zero v

/-- Exact centered-Gaussian-law version of the simultaneous row-norm bound.
This is the direct interface for a smoothed LP whose coordinate perturbations
have variance `v`. -/
theorem measure_exists_norm_gt_le_of_coordinate_gaussianReal
    {ρ ι Ω : Type*} [Fintype ρ] [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} (X : ρ → Ω → EuclideanSpace ℝ ι) (v : ℝ≥0)
    (hMeas : ∀ r i, AEMeasurable (fun ω => X r ω i) μ)
    (hlaw : ∀ r i, μ.map (fun ω => X r ω i) = gaussianReal 0 v)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ r, Real.sqrt (Fintype.card ι) * t < ‖X r ω‖} ≤
      (Fintype.card ρ : ℝ) * (Fintype.card ι : ℝ) *
        (2 * Real.exp (-t ^ 2 / (2 * v))) :=
  measure_exists_norm_gt_le_of_coordinate_hasSubgaussianMGF X v
    (fun r i => hasSubgaussianMGF_of_map_eq_gaussianReal_zero v (hMeas r i) (hlaw r i)) ht

/-- One-sided Chernoff bound for a centered real Gaussian. -/
theorem gaussianReal_zero_measure_ge_le (v : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v).real {x | t ≤ x} ≤ Real.exp (-t ^ 2 / (2 * v)) :=
  (hasSubgaussianMGF_id_gaussianReal_zero v).measure_ge_le ht

/-- The matching lower-tail Chernoff bound for a centered real Gaussian. -/
theorem gaussianReal_zero_measure_le_neg_le (v : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v).real {x | x ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * v)) := by
  have h := (hasSubgaussianMGF_id_gaussianReal_zero v).neg.measure_ge_le ht
  have h' :
      (gaussianReal 0 v).real {x | t ≤ -x} ≤ Real.exp (-t ^ 2 / (2 * v)) := by
    simpa only [Pi.neg_apply, id_eq] using h
  rw [show {x : ℝ | t ≤ -x} = {x | x ≤ -t} by
    ext x
    simp only [mem_setOf_eq]
    constructor <;> intro hx <;> linarith] at h'
  exact h'

/-- Two-sided scalar Gaussian tail bound, in the real-valued measure API used
by Mathlib's Chernoff theory. -/
theorem gaussianReal_zero_measure_abs_ge_le (v : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v).real {x | t ≤ |x|} ≤
      2 * Real.exp (-t ^ 2 / (2 * v)) := by
  rw [show {x : ℝ | t ≤ |x|} = {x | t ≤ x} ∪ {x | x ≤ -t} by
    ext x
    simp only [mem_setOf_eq, mem_union]
    rw [le_abs]
    constructor <;> intro h
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)]
  calc
    (gaussianReal 0 v).real ({x | t ≤ x} ∪ {x | x ≤ -t}) ≤
        (gaussianReal 0 v).real {x | t ≤ x} +
          (gaussianReal 0 v).real {x | x ≤ -t} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * v)) + Real.exp (-t ^ 2 / (2 * v)) :=
      add_le_add (gaussianReal_zero_measure_ge_le v ht)
        (gaussianReal_zero_measure_le_neg_le v ht)
    _ = 2 * Real.exp (-t ^ 2 / (2 * v)) := by ring

/-- The explicit Chernoff substitution used in Bach--Huiberts Theorem 57:
at threshold `4 * σ * sqrt(log n)`, the two-sided scalar failure factor is
exactly `2 / n^8`. -/
theorem gaussian_tail_factor_four_mul_sqrt_log
    (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 < σ) :
    2 * Real.exp (-(4 * σ * Real.sqrt (Real.log n)) ^ 2 /
        (2 * (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0))) =
      2 / (n : ℝ) ^ 8 := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have harg :
      -(4 * σ * Real.sqrt (Real.log n)) ^ 2 /
          (2 * (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0)) =
        -(8 * Real.log n) := by
    change -(4 * σ * Real.sqrt (Real.log n)) ^ 2 / (2 * σ ^ 2) =
      -(8 * Real.log n)
    field_simp [hσ.ne']
    nlinarith [Real.sq_sqrt hlog]
  rw [harg, Real.exp_neg]
  have hexp : Real.exp (8 * Real.log (n : ℝ)) = (n : ℝ) ^ 8 := by
    rw [show (8 : ℝ) * Real.log (n : ℝ) = (8 : ℕ) * Real.log (n : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hnReal]
  rw [hexp]
  rfl

/-- Simultaneous row version after the concrete Theorem 57 substitution.  For
`rows` many `dim`-dimensional perturbations, the bad row-norm probability is at
most `2 * rows * dim / n^8`. -/
theorem measure_exists_norm_gt_four_mul_sqrt_log_le
    {ρ ι Ω : Type*} [Fintype ρ] [Fintype ι] [MeasurableSpace Ω]
    {μ : Measure Ω} (X : ρ → Ω → EuclideanSpace ℝ ι)
    (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 < σ)
    (hMeas : ∀ r i, AEMeasurable (fun ω => X r ω i) μ)
    (hlaw : ∀ r i, μ.map (fun ω => X r ω i) =
      gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) :
    μ.real {ω | ∃ r,
        Real.sqrt (Fintype.card ι) *
            (4 * σ * Real.sqrt (Real.log n)) < ‖X r ω‖} ≤
      (Fintype.card ρ : ℝ) * (Fintype.card ι : ℝ) *
        (2 / (n : ℝ) ^ 8) := by
  have ht : 0 ≤ 4 * σ * Real.sqrt (Real.log n) := by positivity
  calc
    μ.real {ω | ∃ r,
        Real.sqrt (Fintype.card ι) *
            (4 * σ * Real.sqrt (Real.log n)) < ‖X r ω‖} ≤
        (Fintype.card ρ : ℝ) * (Fintype.card ι : ℝ) *
          (2 * Real.exp (-(4 * σ * Real.sqrt (Real.log n)) ^ 2 /
            (2 * (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0)))) :=
      measure_exists_norm_gt_le_of_coordinate_gaussianReal X
        ⟨σ ^ 2, sq_nonneg σ⟩ hMeas hlaw ht
    _ = (Fintype.card ρ : ℝ) * (Fintype.card ι : ℝ) *
        (2 / (n : ℝ) ^ 8) := by
      rw [gaussian_tail_factor_four_mul_sqrt_log n hn σ hσ]

#print axioms hasSubgaussianMGF_id_gaussianReal_zero
#print axioms hasSubgaussianMGF_of_map_eq_gaussianReal_zero
#print axioms measure_abs_ge_le_of_hasSubgaussianMGF
#print axioms measure_exists_abs_ge_le_of_hasSubgaussianMGF
#print axioms norm_le_sqrt_card_mul_of_forall_abs_le
#print axioms measure_norm_gt_le_of_coordinate_hasSubgaussianMGF
#print axioms measure_exists_norm_gt_le_of_coordinate_hasSubgaussianMGF
#print axioms measure_exists_norm_gt_le_of_coordinate_gaussianReal
#print axioms gaussianReal_zero_measure_ge_le
#print axioms gaussianReal_zero_measure_le_neg_le
#print axioms gaussianReal_zero_measure_abs_ge_le
#print axioms gaussian_tail_factor_four_mul_sqrt_log
#print axioms measure_exists_norm_gt_four_mul_sqrt_log_le

end SolveAll011.Tier3
