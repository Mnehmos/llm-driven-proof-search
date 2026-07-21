/-
SolveAll #11 — lower-bound reduction discovered in the 2026 literature audit.

This file does NOT formalize the geometric diameter theorem of Bach–Huiberts
(FOCS 2025, arXiv:2504.04197v2, Theorem 57).  It kernel-checks the short but
essential bridge from such a diameter theorem to a pivot-count lower bound.

For a fixed feasible polytope, suppose Phase I chooses the same starting vertex
for objectives `c` and `-c`.  If every edge path between the maximizing and
minimizing vertices has length at least `D`, then the two simplex runs for `c`
and `-c` perform at least `D` pivots in total.  Consequently one of the two runs
uses at least half that many pivots.  If the objective distribution is symmetric
under negation (as a centered Gaussian is), integration gives the same factor-2
lower bound for the expected pivot count.

The first theorem is purely combinatorial.  The second states the expectation
step for an arbitrary measure-preserving involution; negation of a centered
Gaussian is the intended instance.  Neither theorem assumes independence among
constraints or makes a union bound over bases.
-/
import Mathlib

open MeasureTheory

namespace SolveAll011.Tier3

/-- A minimal literal model of the page's unrestricted initialization wording.
The work performed by `init` is not charged; only applications of `step` count
as pivots. -/
structure LiteralPivotRule (Instance Vertex : Type)
    (IsOptimal : Instance → Vertex → Prop) where
  init : Instance → Vertex
  step : Instance → Vertex → Option Vertex
  stop_at_optimal : ∀ I v, IsOptimal I v → step I v = none

/-- Count only edge steps after initialization, matching the page's stated cost
metric. -/
def countedPivots {Instance Vertex : Type}
    (step : Instance → Vertex → Option Vertex) (I : Instance) : ℕ → Vertex → ℕ
  | 0, _ => 0
  | fuel + 1, v =>
      match step I v with
      | none => 0
      | some w => countedPivots step I fuel w + 1

/-- If an unrestricted initializer may select an optimal vertex by uncharged
work, it defines a literal pivot rule which immediately stops. -/
def oracleInitializedRule {Instance Vertex : Type}
    {IsOptimal : Instance → Vertex → Prop}
    (chooseOptimal : Instance → Vertex) :
    LiteralPivotRule Instance Vertex IsOptimal where
  init := chooseOptimal
  step := fun _ _ => none
  stop_at_optimal := by simp

/-- The oracle-initialized rule has pointwise zero pivot count for every fuel
budget.  This is why the literal root must charge or constrain initialization. -/
theorem oracle_initialization_gives_zero_pivots
    {Instance Vertex : Type} {IsOptimal : Instance → Vertex → Prop}
    (chooseOptimal : Instance → Vertex)
    (hoptimal : ∀ I, IsOptimal I (chooseOptimal I))
    (I : Instance) (fuel : ℕ) :
    IsOptimal I ((oracleInitializedRule (IsOptimal := IsOptimal) chooseOptimal).init I) ∧
      countedPivots (oracleInitializedRule (IsOptimal := IsOptimal) chooseOptimal).step I fuel
        ((oracleInitializedRule (IsOptimal := IsOptimal) chooseOptimal).init I) = 0 := by
  refine ⟨hoptimal I, ?_⟩
  cases fuel <;> rfl

/-- A long path between antipodal optima forces one of two runs from a common
start to be long.  `graphDist` is intended to be shortest-path distance in the
1-skeleton, while `pivotsToMax` and `pivotsToMin` are the pivot counts for the
objectives `c` and `-c` respectively. -/
theorem antipodal_pivot_sum_ge
    {Vertex : Type} (graphDist : Vertex → Vertex → ℕ)
    (start maximize minimize : Vertex)
    (pivotsToMax pivotsToMin diameterLowerBound : ℕ)
    (hsymm : graphDist maximize start = graphDist start maximize)
    (htriangle :
      graphDist maximize minimize ≤
        graphDist maximize start + graphDist start minimize)
    (hdiameter : diameterLowerBound ≤ graphDist maximize minimize)
    (hmax : graphDist start maximize ≤ pivotsToMax)
    (hmin : graphDist start minimize ≤ pivotsToMin) :
    diameterLowerBound ≤ pivotsToMax + pivotsToMin := by
  omega

/-- Quantitative corollary: at least one of the antipodal runs uses at least
`⌈D/2⌉` pivots. -/
theorem antipodal_one_run_ge_half
    (pivotsToMax pivotsToMin diameterLowerBound : ℕ)
    (hsum : diameterLowerBound ≤ pivotsToMax + pivotsToMin) :
    (diameterLowerBound + 1) / 2 ≤ max pivotsToMax pivotsToMin := by
  omega

/-- Expectation bridge for symmetric objective noise.  If `flip` preserves the
probability measure (for the application, `flip c = -c`) and every paired pair
of runs has total cost at least `D`, then one run has expected cost at least
`D/2`, expressed without division as `D ≤ 2 * E[T]`.

Using `ℝ≥0∞` avoids any integrability side condition and is natural for a
nonnegative pivot count. -/
theorem symmetric_lintegral_pair_lower_bound
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (flip : Ω → Ω) (cost : Ω → ENNReal) (D : ENNReal)
    (hflip : MeasurePreserving flip μ μ)
    (hcost : Measurable cost)
    (hpair : ∀ ω, D ≤ cost ω + cost (flip ω)) :
    D ≤ 2 * ∫⁻ ω, cost ω ∂μ := by
  calc
    D = ∫⁻ _ : Ω, D ∂μ := by simp
    _ ≤ ∫⁻ ω, (cost ω + cost (flip ω)) ∂μ :=
      lintegral_mono hpair
    _ = (∫⁻ ω, cost ω ∂μ) + ∫⁻ ω, cost (flip ω) ∂μ := by
      rw [lintegral_add_left hcost]
    _ = (∫⁻ ω, cost ω ∂μ) + ∫⁻ ω, cost ω ∂μ := by
      rw [hflip.lintegral_comp hcost]
    _ = 2 * ∫⁻ ω, cost ω ∂μ := by ring

/-- The analytic separation used at the end of the lower-bound transfer.  After
putting `x = 1/σ`, the lower bound has an `x^(1/4)` numerator and a
`log(x)^(1/4)` denominator.  For every fixed polylogarithmic exponent `k`, the
combined logarithmic power `k + 1/4` is little-o of `x^(1/4)`.

This is the precise asymptotic fact showing that the rescaled Bach--Huiberts
lower bound cannot be dominated by any fixed polylogarithm in `1/σ`. -/
theorem polylog_with_quarter_isLittleO_quarterPower (k : ℕ) :
    (fun x : ℝ => Real.log x ^ ((k : ℝ) + 1 / 4)) =o[Filter.atTop]
      (fun x : ℝ => x ^ (1 / 4 : ℝ)) := by
  exact isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ))
    ((k : ℝ) + 1 / 4) (by norm_num)

/-- Constant-factor parameter conversion in the fixed-dimension-two rescaling.
If the literature construction has `8/τ² ≤ M ≤ 16/τ²` constraints and is
scaled by `(2M)⁻¹/²`, then its SolveAll noise
`σ = τ / sqrt(2M)` lies between `τ²/(4√2)` and `τ²/4`.

The floor estimate `8/τ² ≤ floor((4/τ)²) ≤ 16/τ²` is kept separate; this theorem
is the analytic core of the claim `σ = Θ(τ²)`. -/
theorem scaled_noise_between_quadratic_bounds
    (τ M σ : ℝ) (hτ : 0 < τ)
    (hMlower : 8 / τ ^ 2 ≤ M) (hMupper : M ≤ 16 / τ ^ 2)
    (hσ : σ = τ / Real.sqrt (2 * M)) :
    τ ^ 2 / (4 * Real.sqrt 2) ≤ σ ∧ σ ≤ τ ^ 2 / 4 := by
  have hτsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hMpos : 0 < M := lt_of_lt_of_le (div_pos (by norm_num) hτsq) hMlower
  have hspos : 0 < Real.sqrt (2 * M) := Real.sqrt_pos.2 (by positivity)
  have hssq : (Real.sqrt (2 * M)) ^ 2 = 2 * M :=
    Real.sq_sqrt (by positivity)
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hMτlower : 8 ≤ M * τ ^ 2 :=
    (div_le_iff₀ hτsq).mp hMlower
  have hMτupper : M * τ ^ 2 ≤ 16 :=
    (le_div_iff₀ hτsq).mp hMupper
  have hscaledSq : (τ * Real.sqrt (2 * M)) ^ 2 = 2 * (M * τ ^ 2) := by
    rw [mul_pow, hssq]
    ring
  have hscaledLower : 4 ≤ τ * Real.sqrt (2 * M) := by
    nlinarith [mul_pos hτ hspos]
  have hscaledUpper : τ * Real.sqrt (2 * M) ≤ 4 * Real.sqrt 2 := by
    nlinarith [mul_pos hτ hspos, sq_nonneg
      (τ * Real.sqrt (2 * M) - 4 * Real.sqrt 2)]
  rw [hσ]
  constructor
  · apply (div_le_div_iff₀ (mul_pos (by norm_num) hsqrt2pos) hspos).2
    nlinarith
  · apply (div_le_div_iff₀ hspos (by norm_num : (0 : ℝ) < 4)).2
    nlinarith

/-- The elementary floor estimate used with
`x = (4/τ)^2`: once `x ≥ 2`, its natural floor lies between `x/2` and `x`.
This supplies `8/τ² ≤ M ≤ 16/τ²` for
`M = floor((4/τ)^2)`. -/
theorem half_le_natFloor_and_natFloor_le (x : ℝ) (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  have hxnonneg : 0 ≤ x := le_trans (by norm_num) hx
  constructor
  · have hlt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  · exact Nat.floor_le hxnonneg

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.oracle_initialization_gives_zero_pivots
#print axioms SolveAll011.Tier3.antipodal_pivot_sum_ge
#print axioms SolveAll011.Tier3.antipodal_one_run_ge_half
#print axioms SolveAll011.Tier3.symmetric_lintegral_pair_lower_bound
#print axioms SolveAll011.Tier3.polylog_with_quarter_isLittleO_quarterPower
#print axioms SolveAll011.Tier3.scaled_noise_between_quadratic_bounds
#print axioms SolveAll011.Tier3.half_le_natFloor_and_natFloor_le
