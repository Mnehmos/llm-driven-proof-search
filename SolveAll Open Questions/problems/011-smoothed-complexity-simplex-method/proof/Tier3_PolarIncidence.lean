/-
SolveAll #11 — deterministic polar-incidence bridge from Bach--Huiberts,
Lemma 56.

This module connects LP constraint normals and optimal objective rays to the
same exposed faces of the polar body.  It is deliberately stated for arbitrary
real inner-product spaces; the finite-dimensional basis/facet dimension facts
can be layered on top.
-/
import Mathlib

namespace SolveAll011.Tier3

open scoped RealInnerProductSpace

/-- Polar body of a set, using the normalization `⟪x,y⟫ ≤ 1`. -/
def polarBody {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) : Set E :=
  {y | ∀ x ∈ P, ⟪x, y⟫ ≤ 1}

/-- The exposed face of the polar body supported by a primal point `v`. -/
def polarExposedFace {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (v : E) : Set E :=
  {y | y ∈ polarBody P ∧ ⟪v, y⟫ = 1}

/-- Convex hull of the constraint normals indexed by a basis. -/
def basisNormalHull {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (B : Finset ι) : Set E :=
  convexHull ℝ (a '' (B : Set ι))

/-- Pairwise norm diameter bound, avoiding any dependence on a polytope-face
API. -/
def NormDiameterLE {E : Type} [NormedAddCommGroup E]
    (S : Set E) (γ : ℝ) : Prop :=
  ∀ y ∈ S, ∀ z ∈ S, ‖y - z‖ ≤ γ

/-- A polar body is convex, as an intersection of linear halfspaces. -/
theorem polarBody_convex
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Set E) : Convex ℝ (polarBody P) := by
  rw [convex_iff_add_mem]
  intro y hy z hz α β hα hβ hsum x hx
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hy' := hy x hx
  have hz' := hz x hx
  nlinarith

/-- A polar exposed face is convex. -/
theorem polarExposedFace_convex
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (v : E) : Convex ℝ (polarExposedFace P v) := by
  rw [convex_iff_add_mem]
  intro y hy z hz α β hα hβ hsum
  constructor
  · exact polarBody_convex P hy.1 hz.1 hα hβ hsum
  · rw [inner_add_right, inner_smul_right, inner_smul_right, hy.2, hz.2]
    nlinarith

/-- A polar body is closed, since it is an intersection of closed linear
halfspaces. -/
theorem polarBody_isClosed
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) : IsClosed (polarBody P) := by
  rw [polarBody, show {y : E | ∀ x ∈ P, ⟪x, y⟫ ≤ 1} =
      ⋂ x ∈ P, {y | ⟪x, y⟫ ≤ 1} by
    ext y
    simp]
  exact isClosed_biInter fun x _ => isClosed_le (by fun_prop) continuous_const

/-- A polar exposed face is closed. -/
theorem polarExposedFace_isClosed
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (v : E) : IsClosed (polarExposedFace P v) := by
  rw [polarExposedFace, show {y : E | y ∈ polarBody P ∧ ⟪v, y⟫ = 1} =
      polarBody P ∩ {y | ⟪v, y⟫ = 1} by rfl]
  exact (polarBody_isClosed P).inter (isClosed_eq (by fun_prop) continuous_const)

/-- Every nonempty polar exposed face has a minimum-norm point, and that
point satisfies the first-order inequality used in Bach--Huiberts Theorem 57.
This discharges the paper's previously implicit closest-point existence step. -/
theorem exists_polarExposedFace_minimizer
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : Set E) (v : E)
    (hne : (polarExposedFace P v).Nonempty) :
    ∃ y ∈ polarExposedFace P v,
      ∀ z ∈ polarExposedFace P v, ‖y‖ ≤ ‖z‖ ∧ ‖y‖ ^ 2 ≤ ⟪y, z⟫ := by
  have hcomplete : IsComplete (polarExposedFace P v) :=
    (polarExposedFace_isClosed P v).isComplete
  obtain ⟨y, hy, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcomplete
      (polarExposedFace_convex P v) (0 : E)
  refine ⟨y, hy, ?_⟩
  intro z hz
  have hfirst :=
    (norm_eq_iInf_iff_real_inner_le_zero (polarExposedFace_convex P v) hy).1 hmin z hz
  constructor
  · let z' : polarExposedFace P v := ⟨z, hz⟩
    have hInf : ⨅ w : polarExposedFace P v, ‖(0 : E) - w‖ ≤ ‖(0 : E) - z'‖ :=
      ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ z'
    rw [← hmin] at hInf
    simpa using hInf
  · rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hfirst
    linarith

/-- The polar reverses an outer Euclidean-ball inclusion: if `P` lies in the
radius-`R` ball, then the radius-`R⁻¹` ball lies in `P°`. -/
theorem closedBall_inv_radius_subset_polarBody
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (R : ℝ) (hR : 0 < R)
    (houter : P ⊆ Metric.closedBall (0 : E) R) :
    Metric.closedBall (0 : E) R⁻¹ ⊆ polarBody P := by
  intro y hy x hx
  have hyNorm : ‖y‖ ≤ R⁻¹ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have hxNorm : ‖x‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using houter hx
  calc
    ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ R * R⁻¹ := mul_le_mul hxNorm hyNorm (norm_nonneg _) hR.le
    _ = 1 := mul_inv_cancel₀ hR.ne'

/-- The polar reverses an inner Euclidean-ball inclusion: if `P` contains the
radius-`r` ball, then `P°` lies in the radius-`r⁻¹` ball. -/
theorem polarBody_subset_closedBall_inv_radius
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (r : ℝ) (hr : 0 < r)
    (hinner : Metric.closedBall (0 : E) r ⊆ P) :
    polarBody P ⊆ Metric.closedBall (0 : E) r⁻¹ := by
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hy0 : y = 0
  · simp [hy0, hr.le]
  · have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    let u : E := (‖y‖⁻¹ : ℝ) • y
    have huNorm : ‖u‖ = 1 := by
      simp [u, norm_smul, hynorm.ne']
    have hxBall : r • u ∈ Metric.closedBall (0 : E) r := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, huNorm, mul_one]
    have hsupport := hy (r • u) (hinner hxBall)
    have hinnerEq : ⟪r • u, y⟫ = r * ‖y‖ := by
      rw [inner_smul_left]
      dsimp [u]
      rw [inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [starRingEnd_apply, star_trivial]
      field_simp [hynorm.ne']
    rw [hinnerEq] at hsupport
    rw [inv_eq_one_div, le_div_iff₀ hr]
    simpa [mul_comm] using hsupport

/-- Near-spherical polar roundness gives the exact `8 * sqrt η` diameter
bound for every nonempty exposed face.  The minimum-norm point and its
first-order condition are produced internally by Hilbert projection. -/
theorem polarExposedFace_normDiameter_eight_sqrt
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : Set E) (v : E) (η : ℝ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hLower : ∀ y ∈ polarExposedFace P v, 1 - 4 * η ≤ ‖y‖)
    (hUpper : ∀ y ∈ polarBody P, ‖y‖ ≤ 1 + 3 * η)
    (hne : (polarExposedFace P v).Nonempty) :
    NormDiameterLE (polarExposedFace P v) (8 * Real.sqrt η) := by
  obtain ⟨y, hy, hyMin⟩ := exists_polarExposedFace_minimizer P v hne
  have hyLower : 1 - 4 * η ≤ ‖y‖ := hLower y hy
  intro z hz w hw
  have pointDist : ∀ q ∈ polarExposedFace P v,
      ‖q - y‖ ≤ Real.sqrt (14 * η) := by
    intro q hq
    have hqUpper : ‖q‖ ≤ 1 + 3 * η := hUpper q hq.1
    have hclosest : ‖y‖ ^ 2 ≤ ⟪y, q⟫ := (hyMin q hq).2
    have hyRadius : 0 ≤ 1 - 4 * η := by nlinarith
    have hqRadius : 0 ≤ 1 + 3 * η := by nlinarith
    have hySqLower : (1 - 4 * η) ^ 2 ≤ ‖y‖ ^ 2 := by
      nlinarith [norm_nonneg y]
    have hqSqUpper : ‖q‖ ^ 2 ≤ (1 + 3 * η) ^ 2 := by
      nlinarith [norm_nonneg q]
    have hinner : ‖y‖ ^ 2 ≤ ⟪q, y⟫ := by rwa [real_inner_comm]
    have hsq : ‖q - y‖ ^ 2 ≤ 14 * η := by
      rw [norm_sub_sq_real]
      nlinarith [sq_nonneg η]
    apply le_of_sq_le_sq
    · rw [Real.sq_sqrt (by positivity)]
      exact hsq
    · exact Real.sqrt_nonneg _
  have hzDist := pointDist z hz
  have hwDist := pointDist w hw
  have hpair : ‖z - w‖ ≤ 2 * Real.sqrt (14 * η) := by
    calc
      ‖z - w‖ = ‖(z - y) + (y - w)‖ := by congr 1; abel
      _ ≤ ‖z - y‖ + ‖y - w‖ := norm_add_le _ _
      _ = ‖z - y‖ + ‖w - y‖ := by rw [norm_sub_rev y w]
      _ ≤ Real.sqrt (14 * η) + Real.sqrt (14 * η) := add_le_add hzDist hwDist
      _ = 2 * Real.sqrt (14 * η) := by ring
  apply hpair.trans
  apply le_of_sq_le_sq
  · rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hη),
      mul_pow, Real.sq_sqrt hη]
    nlinarith
  · positivity

/-- Direct primal-sandwich version of the exposed-face diameter theorem.  It
combines reciprocal polar containment, the support equation `⟪v,y⟫=1`, and the
minimum-point theorem above. -/
theorem polarExposedFace_normDiameter_eight_sqrt_of_ball_sandwich
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (P : Set E) (v : E) (r R η : ℝ)
    (hr : 0 < r) (hR : 0 < R)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hinner : Metric.closedBall (0 : E) r ⊆ P)
    (houter : P ⊆ Metric.closedBall (0 : E) R)
    (hv : v ∈ P)
    (hrecipLower : 1 - 4 * η ≤ R⁻¹)
    (hrecipUpper : r⁻¹ ≤ 1 + 3 * η)
    (hne : (polarExposedFace P v).Nonempty) :
    NormDiameterLE (polarExposedFace P v) (8 * Real.sqrt η) := by
  have hvNorm : ‖v‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using houter hv
  have hLower : ∀ y ∈ polarExposedFace P v, 1 - 4 * η ≤ ‖y‖ := by
    intro y hy
    have hone : 1 ≤ R * ‖y‖ := by
      calc
        1 = ⟪v, y⟫ := hy.2.symm
        _ ≤ ‖v‖ * ‖y‖ := real_inner_le_norm _ _
        _ ≤ R * ‖y‖ := mul_le_mul_of_nonneg_right hvNorm (norm_nonneg _)
    exact hrecipLower.trans ((inv_le_iff_one_le_mul₀' hR).2 hone)
  have hUpper : ∀ y ∈ polarBody P, ‖y‖ ≤ 1 + 3 * η := by
    intro y hy
    have hyBall := polarBody_subset_closedBall_inv_radius P r hr hinner hy
    have hyInv : ‖y‖ ≤ r⁻¹ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hyBall
    exact hyInv.trans hrecipUpper
  exact polarExposedFace_normDiameter_eight_sqrt P v η hη hηsmall hLower hUpper hne

/-- Every normalized LP constraint normal belongs to the polar of its feasible
set. -/
theorem constraint_normal_mem_polar
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (P : Set E)
    (hconstraint : ∀ x ∈ P, ∀ i, ⟪a i, x⟫ ≤ 1) (i : ι) :
    a i ∈ polarBody P := by
  intro x hx
  rw [real_inner_comm]
  exact hconstraint x hx i

/-- Active basis normals, and hence their convex hull, lie in the polar
exposed face supported by the corresponding primal vertex. -/
theorem basisNormalHull_subset_polarExposedFace
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (P : Set E) (v : E) (B : Finset ι)
    (haPolar : ∀ i, a i ∈ polarBody P)
    (hactive : ∀ i ∈ B, ⟪v, a i⟫ = 1) :
    basisNormalHull a B ⊆ polarExposedFace P v := by
  apply convexHull_min
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact ⟨haPolar i, hactive i hi⟩
  · exact polarExposedFace_convex P v

/-- A single active normal belongs to the corresponding polar exposed face. -/
theorem active_normal_mem_polarExposedFace
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (P : Set E) (v : E) (i : ι)
    (haPolar : a i ∈ polarBody P) (hactive : ⟪v, a i⟫ = 1) :
    a i ∈ polarExposedFace P v :=
  ⟨haPolar, hactive⟩

/-- A face-diameter hypothesis bounds every pair of active basis normals. -/
theorem active_normals_dist_le_of_faceDiameter
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (P : Set E) (v : E) (i j : ι) (γ : ℝ)
    (haPolar : ∀ r, a r ∈ polarBody P)
    (hi : ⟪v, a i⟫ = 1) (hj : ⟪v, a j⟫ = 1)
    (hdiam : NormDiameterLE (polarExposedFace P v) γ) :
    ‖a i - a j‖ ≤ γ :=
  hdiam (a i) (active_normal_mem_polarExposedFace a P v i (haPolar i) hi)
    (a j) (active_normal_mem_polarExposedFace a P v j (haPolar j) hj)

/-- The objective value at a maximizer is positive when the feasible set
contains a positive-radius ball and the objective is a unit vector. -/
theorem objective_value_pos_of_inner_ball
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (r : ℝ) (c v : E)
    (hr : 0 < r) (hc : ‖c‖ = 1)
    (hball : Metric.closedBall (0 : E) r ⊆ P)
    (hmax : ∀ x ∈ P, ⟪c, x⟫ ≤ ⟪c, v⟫) :
    0 < ⟪c, v⟫ := by
  have hrcBall : r • c ∈ Metric.closedBall (0 : E) r := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, hc, mul_one]
  have hbound := hmax (r • c) (hball hrcBall)
  rw [inner_smul_right, real_inner_self_eq_norm_sq, hc] at hbound
  norm_num at hbound
  exact hr.trans_le hbound

/-- The positive objective ray normalized to have support value one. -/
noncomputable def normalizedObjectiveRay
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c v : E) : E :=
  (⟪c, v⟫⁻¹ : ℝ) • c

/-- A normalized maximizing-objective ray lies in the polar exposed face of
the maximizing vertex.  This is the endpoint-incidence step in Lemma 56. -/
theorem normalizedObjectiveRay_mem_polarExposedFace
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (c v : E)
    (hpos : 0 < ⟪c, v⟫)
    (hmax : ∀ x ∈ P, ⟪c, x⟫ ≤ ⟪c, v⟫) :
    normalizedObjectiveRay c v ∈ polarExposedFace P v := by
  constructor
  · intro x hx
    change ⟪x, (⟪c, v⟫⁻¹ : ℝ) • c⟫ ≤ 1
    rw [inner_smul_right]
    have hxc : ⟪x, c⟫ ≤ ⟪c, v⟫ := by
      rw [real_inner_comm]
      exact hmax x hx
    calc
      (⟪c, v⟫⁻¹ : ℝ) * ⟪x, c⟫ ≤ ⟪c, v⟫⁻¹ * ⟪c, v⟫ :=
        mul_le_mul_of_nonneg_left hxc (inv_nonneg.mpr hpos.le)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  · change ⟪v, (⟪c, v⟫⁻¹ : ℝ) • c⟫ = 1
    rw [inner_smul_right, show ⟪v, c⟫ = ⟪c, v⟫ from real_inner_comm _ _]
    exact inv_mul_cancel₀ hpos.ne'

/-- Combined version deriving positivity from the inner-ball hypothesis. -/
theorem normalizedObjectiveRay_mem_polarExposedFace_of_inner_ball
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (r : ℝ) (c v : E)
    (hr : 0 < r) (hc : ‖c‖ = 1)
    (hball : Metric.closedBall (0 : E) r ⊆ P)
    (hmax : ∀ x ∈ P, ⟪c, x⟫ ≤ ⟪c, v⟫) :
    normalizedObjectiveRay c v ∈ polarExposedFace P v :=
  normalizedObjectiveRay_mem_polarExposedFace P c v
    (objective_value_pos_of_inner_ball P r c v hr hc hball hmax) hmax

/-- The same face-diameter hypothesis bounds a normalized objective ray and
every active normal of its endpoint basis. -/
theorem normalizedObjectiveRay_dist_active_normal_le
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (P : Set E) (c v : E) (i : ι) (γ : ℝ)
    (hray : normalizedObjectiveRay c v ∈ polarExposedFace P v)
    (haPolar : a i ∈ polarBody P) (hactive : ⟪v, a i⟫ = 1)
    (hdiam : NormDiameterLE (polarExposedFace P v) γ) :
    ‖normalizedObjectiveRay c v - a i‖ ≤ γ :=
  hdiam _ hray _ (active_normal_mem_polarExposedFace a P v i haPolar hactive)

/-- Reversed orientation of the previous endpoint estimate. -/
theorem active_normal_dist_normalizedObjectiveRay_le
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (P : Set E) (c v : E) (i : ι) (γ : ℝ)
    (hray : normalizedObjectiveRay c v ∈ polarExposedFace P v)
    (haPolar : a i ∈ polarBody P) (hactive : ⟪v, a i⟫ = 1)
    (hdiam : NormDiameterLE (polarExposedFace P v) γ) :
    ‖a i - normalizedObjectiveRay c v‖ ≤ γ :=
  hdiam _ (active_normal_mem_polarExposedFace a P v i haPolar hactive) _ hray

/-- The normalized rays for antipodal objectives are at least `2 / R` apart
when both support values are positive and at most `R`.  This supplies the
`hfar` hypothesis of the metric-chain theorem in Lemma 56. -/
theorem antipodal_normalizedObjectiveRays_far
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (c vPlus vMinus : E)
    (hR : 0 < R) (hc : ‖c‖ = 1)
    (hplusPos : 0 < ⟪c, vPlus⟫)
    (hminusPos : 0 < ⟪-c, vMinus⟫)
    (hplusR : ⟪c, vPlus⟫ ≤ R)
    (hminusR : ⟪-c, vMinus⟫ ≤ R) :
    2 / R ≤
      ‖normalizedObjectiveRay c vPlus - normalizedObjectiveRay (-c) vMinus‖ := by
  have hplusInv : R⁻¹ ≤ ⟪c, vPlus⟫⁻¹ :=
    (inv_le_inv₀ hR hplusPos).2 hplusR
  have hminusInv : R⁻¹ ≤ ⟪-c, vMinus⟫⁻¹ :=
    (inv_le_inv₀ hR hminusPos).2 hminusR
  have hsumPos : 0 < ⟪c, vPlus⟫⁻¹ + ⟪-c, vMinus⟫⁻¹ :=
    add_pos (inv_pos.mpr hplusPos) (inv_pos.mpr hminusPos)
  have hvec :
      normalizedObjectiveRay c vPlus - normalizedObjectiveRay (-c) vMinus =
        (⟪c, vPlus⟫⁻¹ + ⟪-c, vMinus⟫⁻¹) • c := by
    simp only [normalizedObjectiveRay]
    module
  rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hsumPos, hc, mul_one]
  rw [div_eq_mul_inv]
  nlinarith

/-- The support-value upper bounds used above follow from a radius bound on
the primal maximizing/minimizing vertices. -/
theorem antipodal_support_values_le_radius
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : ℝ) (c vPlus vMinus : E)
    (hc : ‖c‖ = 1) (hvPlus : ‖vPlus‖ ≤ R) (hvMinus : ‖vMinus‖ ≤ R) :
    ⟪c, vPlus⟫ ≤ R ∧ ⟪-c, vMinus⟫ ≤ R := by
  constructor
  · calc
      ⟪c, vPlus⟫ ≤ ‖c‖ * ‖vPlus‖ := real_inner_le_norm _ _
      _ = ‖vPlus‖ := by rw [hc, one_mul]
      _ ≤ R := hvPlus
  · calc
      ⟪-c, vMinus⟫ ≤ ‖-c‖ * ‖vMinus‖ := real_inner_le_norm _ _
      _ = ‖vMinus‖ := by rw [norm_neg, hc, one_mul]
      _ ≤ R := hvMinus

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.polarBody_convex
#print axioms SolveAll011.Tier3.polarExposedFace_convex
#print axioms SolveAll011.Tier3.polarBody_isClosed
#print axioms SolveAll011.Tier3.polarExposedFace_isClosed
#print axioms SolveAll011.Tier3.exists_polarExposedFace_minimizer
#print axioms SolveAll011.Tier3.closedBall_inv_radius_subset_polarBody
#print axioms SolveAll011.Tier3.polarBody_subset_closedBall_inv_radius
#print axioms SolveAll011.Tier3.polarExposedFace_normDiameter_eight_sqrt
#print axioms SolveAll011.Tier3.polarExposedFace_normDiameter_eight_sqrt_of_ball_sandwich
#print axioms SolveAll011.Tier3.constraint_normal_mem_polar
#print axioms SolveAll011.Tier3.basisNormalHull_subset_polarExposedFace
#print axioms SolveAll011.Tier3.active_normal_mem_polarExposedFace
#print axioms SolveAll011.Tier3.active_normals_dist_le_of_faceDiameter
#print axioms SolveAll011.Tier3.objective_value_pos_of_inner_ball
#print axioms SolveAll011.Tier3.normalizedObjectiveRay_mem_polarExposedFace
#print axioms SolveAll011.Tier3.normalizedObjectiveRay_mem_polarExposedFace_of_inner_ball
#print axioms SolveAll011.Tier3.normalizedObjectiveRay_dist_active_normal_le
#print axioms SolveAll011.Tier3.active_normal_dist_normalizedObjectiveRay_le
#print axioms SolveAll011.Tier3.antipodal_normalizedObjectiveRays_far
#print axioms SolveAll011.Tier3.antipodal_support_values_le_radius
