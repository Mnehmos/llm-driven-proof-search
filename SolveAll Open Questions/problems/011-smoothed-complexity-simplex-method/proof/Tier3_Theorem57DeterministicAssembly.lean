/-
SolveAll #11 — deterministic end-to-end Bach--Huiberts assembly.

This closes the wrapper from the raw near-spherical inequalities to the actual
charged Tier-2 pivot count.  It combines Lemma 55 roundness, positive-RHS
normalization, polar exposed-face diameter, objective-ray incidence, and the
finite charged basis-path capstone.
-/
import Tier3_ExecutionLowerBoundAssembly
import Tier3_PolarIncidence
import Tier3_NormalizedLPBasis

namespace SolveAll011.Tier3

open scoped RealInnerProductSpace

/-- A charged antipodal run through a near-spherical smoothed LP obeys the full
deterministic Bach--Huiberts lower bound, stated directly on Tier-2
`pivotCount`. -/
theorem theorem57_deterministic_pivotCount_lower
    {ConstraintData Objective ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A s : ι → E) (b : ι → ℝ) (η : ℝ)
    (hη : 0 < η) (hηsmall : η ≤ 1 / 8)
    (hsunit : ∀ i, ‖s i‖ = 1)
    (hdense : ∀ u : E, ‖u‖ = 1 → ∃ i, ‖u - s i‖ ≤ η)
    (hpert : ∀ i, ‖A i - s i‖ ≤ η)
    (hb : ∀ i, 1 - η ≤ b i ∧ b i ≤ 1 + η)
    (R : ObjectiveIndependentPivotRule ConstraintData Objective
      (NormalizedFeasibleBasis (normalizedNormal A b)))
    (data : ConstraintData) (objective : Objective) (k : ℕ)
    (run : NormalizedChargedExecution (normalizedNormal A b) R data objective k)
    (c : E) (hc : ‖c‖ = 1)
    (hd : 2 ≤ Module.finrank ℝ E)
    (hstartMax : ∀ x ∈ normalizedFeasible A b,
      ⟪c, x⟫ ≤ ⟪c, (run.path.basis 0).vertex⟫)
    (hfinishMax : ∀ x ∈ normalizedFeasible A b,
      ⟪-c, x⟫ ≤ ⟪-c, (run.path.basis ⟨k, Nat.lt_succ_self k⟩).vertex⟫) :
    (((Module.finrank ℝ E - 1 : ℕ) : ℝ) *
        (2 / ((1 + 4 * η) * (8 * Real.sqrt η)) - 3) ≤
      (SolveAll011.Tier2.pivotCount (R.step data objective) k (R.init data) : ℝ)) := by
  let a : ι → E := normalizedNormal A b
  let P : Set E := normalizedFeasible A b
  let r : ℝ := 1 - 2 * η
  let radius : ℝ := 1 + 4 * η
  let γ : ℝ := 8 * Real.sqrt η
  have hη0 : 0 ≤ η := hη.le
  have hr : 0 < r := by dsimp [r]; nlinarith
  have hRadius : 0 < radius := by dsimp [radius]; nlinarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hsandwich := bachHuiberts_roundness_sandwich
    η s A b hη0 hηsmall hsunit hdense hpert hb
  have hinner : Metric.closedBall (0 : E) r ⊆ P := by
    simpa [r, P] using hsandwich.1
  have houter : P ⊆ Metric.closedBall (0 : E) radius := by
    simpa [radius, P] using hsandwich.2
  have hbabs : ∀ i, |b i - 1| ≤ η := by
    intro i
    rw [abs_le]
    constructor <;> linarith [(hb i).1, (hb i).2]
  have hηone : η < 1 := lt_of_le_of_lt hηsmall (by norm_num)
  have hbpos : ∀ i, 0 < b i := rhs_positive_of_abs_sub_one_le b η hηone hbabs
  have hfeasibleEq :
      normalizedFeasible a (fun _ => 1) = P := by
    simpa [a, P, normalizedFeasible] using normalized_feasible_eq A b hbpos
  have haPolar : ∀ i, a i ∈ polarBody P := by
    intro i
    apply constraint_normal_mem_polar a P
    intro x hx j
    have hx' : x ∈ normalizedFeasible a (fun _ => 1) := by
      rw [hfeasibleEq]
      exact hx
    exact hx' j
  have hrecip := reciprocal_roundness_bounds η hη0 hηsmall
  have basisVertex_mem (t : Fin (k + 1)) : (run.path.basis t).vertex ∈ P := by
    rw [← hfeasibleEq]
    exact run.path.basis t |>.feasible
  have faceNonempty (t : Fin (k + 1)) :
      (polarExposedFace P (run.path.basis t).vertex).Nonempty := by
    have hcard := (run.path.basis t).card_eq
    have hnonempty : (run.path.basis t).indices.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.2
      intro hempty
      rw [hempty, Finset.card_empty] at hcard
      omega
    obtain ⟨i, hi⟩ := hnonempty
    refine ⟨a i, haPolar i, ?_⟩
    rw [real_inner_comm]
    exact (run.path.basis t).active i hi
  have faceDiameter (t : Fin (k + 1)) :
      NormDiameterLE (polarExposedFace P (run.path.basis t).vertex) γ := by
    dsimp [γ]
    exact polarExposedFace_normDiameter_eight_sqrt_of_ball_sandwich
      P (run.path.basis t).vertex r radius η hr hRadius hη0 hηsmall
      hinner houter (basisVertex_mem t) hrecip.1 hrecip.2 (faceNonempty t)
  let vPlus : E := (run.path.basis 0).vertex
  let vMinus : E := (run.path.basis ⟨k, Nat.lt_succ_self k⟩).vertex
  let zPlus : E := normalizedObjectiveRay c vPlus
  let zMinus : E := normalizedObjectiveRay (-c) vMinus
  have hplusRay : zPlus ∈ polarExposedFace P vPlus := by
    dsimp [zPlus, vPlus]
    exact normalizedObjectiveRay_mem_polarExposedFace_of_inner_ball
      P r c (run.path.basis 0).vertex hr hc hinner hstartMax
  have hminusRay : zMinus ∈ polarExposedFace P vMinus := by
    dsimp [zMinus, vMinus]
    exact normalizedObjectiveRay_mem_polarExposedFace_of_inner_ball
      P r (-c) (run.path.basis ⟨k, Nat.lt_succ_self k⟩).vertex hr
      (by simpa using hc) hinner hfinishMax
  have hfaceDiam : ∀ t ≤ k, ∀ i, i ∈ run.path.indicesAt t →
      ∀ j, j ∈ run.path.indicesAt t → ‖a i - a j‖ ≤ γ := by
    intro t ht i hi j hj
    rw [NormalizedSimplexPath.indicesAt, dif_pos ht] at hi hj
    let ft : Fin (k + 1) := ⟨t, Nat.lt_succ_iff.mpr ht⟩
    have hiact : ⟪(run.path.basis ft).vertex, a i⟫ = 1 := by
      rw [real_inner_comm]
      exact (run.path.basis ft).active i hi
    have hjact : ⟪(run.path.basis ft).vertex, a j⟫ = 1 := by
      rw [real_inner_comm]
      exact (run.path.basis ft).active j hj
    exact active_normals_dist_le_of_faceDiameter a P
      (run.path.basis ft).vertex i j γ haPolar hiact hjact (faceDiameter ft)
  have hstart : ∀ i, i ∈ run.path.indicesAt 0 → ‖zPlus - a i‖ ≤ γ := by
    intro i hi
    rw [NormalizedSimplexPath.indicesAt, dif_pos (Nat.zero_le k)] at hi
    have hactive : ⟪(run.path.basis 0).vertex, a i⟫ = 1 := by
      rw [real_inner_comm]
      exact (run.path.basis 0).active i hi
    exact normalizedObjectiveRay_dist_active_normal_le a P c vPlus i γ
      hplusRay (haPolar i) (by simpa [vPlus] using hactive) (faceDiameter 0)
  have hfinish : ∀ i, i ∈ run.path.indicesAt k → ‖a i - zMinus‖ ≤ γ := by
    intro i hi
    rw [NormalizedSimplexPath.indicesAt, dif_pos le_rfl] at hi
    let fk : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    have hactive : ⟪(run.path.basis fk).vertex, a i⟫ = 1 := by
      rw [real_inner_comm]
      exact (run.path.basis fk).active i hi
    exact active_normal_dist_normalizedObjectiveRay_le a P (-c) vMinus i γ
      hminusRay (haPolar i) (by simpa [vMinus, fk] using hactive) (faceDiameter fk)
  have hplusPos : 0 < ⟪c, vPlus⟫ := by
    dsimp [vPlus]
    exact objective_value_pos_of_inner_ball P r c _ hr hc hinner hstartMax
  have hminusPos : 0 < ⟪-c, vMinus⟫ := by
    dsimp [vMinus]
    exact objective_value_pos_of_inner_ball P r (-c) _ hr (by simpa using hc)
      hinner hfinishMax
  have hsupport := antipodal_support_values_le_radius radius c vPlus vMinus hc
    (by simpa [vPlus, Metric.mem_closedBall, dist_zero_right] using
      houter (basisVertex_mem 0))
    (by
      let fk : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      simpa [vMinus, fk, Metric.mem_closedBall, dist_zero_right] using
        houter (basisVertex_mem fk))
  have hfar : 2 / radius ≤ ‖zPlus - zMinus‖ := by
    dsimp [zPlus, zMinus]
    exact antipodal_normalizedObjectiveRays_far radius c vPlus vMinus hRadius hc
      hplusPos hminusPos hsupport.1 hsupport.2
  simpa [a, radius, γ] using
    run.pivotCount_bachHuiberts_lower a zPlus zMinus radius γ
      hd hRadius hγ hfaceDiam hstart hfinish hfar

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.theorem57_deterministic_pivotCount_lower
