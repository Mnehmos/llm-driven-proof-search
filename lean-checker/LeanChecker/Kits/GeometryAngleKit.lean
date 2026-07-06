import Mathlib

/-!
# Geometry angle kit (issue #74)

Bridge lemmas that turn Putnam-style synthetic Euclidean configuration
hypotheses (equal distances, betweenness, external bisectors) into SCALAR
angle equations, so that the final step is plain `linarith` — never a large
`nlinarith` over raw `∠` atoms (which the 2026-07-06 retry showed can burn
the whole heartbeat budget as a deterministic timeout; see issue #71).

## Route to `putnam_1965_a1` (remaining gaps, deliberately out of scope here)

1. Case analysis turning `Collinear ℝ {X, B, C}` + the angle inequalities into
   a definite betweenness fact (`Sbtw ℝ X B C` in the intended configuration),
   ruling the other arrangements out.
2. Applying `base_angle_eq_pi_sub_apex_div_two` in triangle `A B X`
   (`dist A X = dist A B`) and `angle_add_angle_eq_pi_of_sbtw` at `B`, plus the
   analogous pair at `Y`, produces the two scalar equations
   `β = 3π/4 − α/4` and `α = (π − β)/4` — whose linear solution is `α = π/15`
   (see the fixture below).
-/

namespace LeanChecker.GeometryAngleKit

open Real EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- **Isosceles base-angle bridge**: in a (possibly degenerate) triangle with
`dist p₁ p₂ = dist p₁ p₃`, the base angle at `p₂` equals `(π − apex)/2`.
Combines Mathlib's `angle_eq_angle_of_dist_eq` with the angle-sum theorem so
callers get a scalar equation directly. -/
theorem base_angle_eq_pi_sub_apex_div_two {p₁ p₂ p₃ : P}
    (hd : dist p₁ p₂ = dist p₁ p₃) (hne : p₂ ≠ p₁) :
    ∠ p₁ p₂ p₃ = (π - ∠ p₂ p₁ p₃) / 2 := by
  have hiso := EuclideanGeometry.angle_eq_angle_of_dist_eq hd
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi p₃ hne
  rw [EuclideanGeometry.angle_comm p₁ p₃ p₂] at hiso
  rw [EuclideanGeometry.angle_comm p₃ p₁ p₂] at hsum
  linarith

/-- **Supplementary-angle bridge across a line**: if `p₂` lies strictly
between `p₁` and `p₃`, the two angles a fourth point `q` makes at `p₂` are
supplementary. This is the tool that replaces "X is on line BC on the far
side of B" configuration talk with the scalar equation `∠ABX = π − ∠ABC`. -/
theorem angle_add_angle_eq_pi_of_sbtw {p₁ p₂ p₃ q : P} (h : Sbtw ℝ p₁ p₂ p₃) :
    ∠ p₁ p₂ q + ∠ q p₂ p₃ = π := by
  have := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi q h.angle₁₂₃_eq_pi
  rw [EuclideanGeometry.angle_comm q p₂ p₁] at this
  linarith

/-- Fixture (the 1965 A1 endgame): once the geometry has been eliminated into
the two scalar equations the kit produces, plain `linarith` closes the system
— no `nlinarith` over angle atoms anywhere. -/
example (α β : ℝ) (h1 : β = 3 * π / 4 - α / 4) (h2 : α = (π - β) / 4) :
    α = π / 15 := by
  linarith

/-! ## v2 (issue #84): three rays at a vertex, via oriented angles

Unoriented `∠` has no additivity without configuration facts. In an oriented
2-plane, `EuclideanGeometry.oangle` IS additive (`oangle_add`), and
`angle_eq_abs_oangle_toReal` bridges back. Folding the `Real.Angle`
wraparound cases through the bridge yields the canonical constraint on the
three pairwise unoriented angles of three rays at one vertex: one of them is
the sum of the other two, or all three sum to `2π`. This is exactly the fact
the 1965 A1 Y-side equation needs (see the fixture below), and it eliminates
all remaining `nlinarith`-over-`∠`-atoms temptation: after this lemma, every
diagram fact is a linear scalar (in)equation.

Route to `putnam_1965_a1` from here: case-split `Collinear` via betweenness
trichotomy, use `Wbtw`/`Sbtw` zero/π angle lemmas plus
`angle_add_angle_eq_pi_of_sbtw` and `base_angle_eq_pi_sub_apex_div_two` for
the X-side equation, then `three_ray_angle_decomposition` at `B` for the
Y-side; the angle inequalities kill every branch but `α = (π − β)/4`, and the
first fixture above finishes. -/

section Oriented

open Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]
  [Module.Oriented ℝ V (Fin 2)]

/-- **Three-ray decomposition**: for three points `a b c` distinct from a
vertex `v` in an oriented Euclidean plane, the three pairwise unoriented
angles at `v` satisfy: the outer angle splits over the middle ray, one of the
outer angles absorbs the other two, or the three angles wrap the full turn. -/
theorem three_ray_angle_decomposition {v a b c : P}
    (ha : a ≠ v) (hb : b ≠ v) (hc : c ≠ v) :
    ∠ a v c = ∠ a v b + ∠ b v c ∨
    ∠ a v b = ∠ a v c + ∠ b v c ∨
    ∠ b v c = ∠ a v b + ∠ a v c ∨
    ∠ a v b + ∠ b v c + ∠ a v c = 2 * π := by
  set x : ℝ := (∡ a v b).toReal with hxdef
  set y : ℝ := (∡ b v c).toReal with hydef
  have hA : ∠ a v b = |x| := EuclideanGeometry.angle_eq_abs_oangle_toReal ha hb
  have hB : ∠ b v c = |y| := EuclideanGeometry.angle_eq_abs_oangle_toReal hb hc
  have hC : ∠ a v c = |(∡ a v c).toReal| := EuclideanGeometry.angle_eq_abs_oangle_toReal ha hc
  have hx1 : -π < x := Real.Angle.neg_pi_lt_toReal _
  have hx2 : x ≤ π := Real.Angle.toReal_le_pi _
  have hy1 : -π < y := Real.Angle.neg_pi_lt_toReal _
  have hy2 : y ≤ π := Real.Angle.toReal_le_pi _
  have key : ((x + y : ℝ) : Real.Angle) = ∡ a v c := by
    rw [Real.Angle.coe_add, hxdef, hydef, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
    exact EuclideanGeometry.oangle_add ha hb hc
  rcases le_or_gt (x + y) π with hhi | hover
  · rcases lt_or_ge (-π) (x + y) with hlo | hunder
    · -- No wraparound: (∡ a v c).toReal = x + y.
      have hz : (∡ a v c).toReal = x + y := by
        rw [← key, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hlo, hhi⟩]
      rcases le_or_gt 0 x with hx0 | hx0 <;> rcases le_or_gt 0 y with hy0 | hy0
      · left
        rw [hC, hA, hB, hz, abs_of_nonneg hx0, abs_of_nonneg hy0, abs_of_nonneg (by linarith)]
      · rcases le_or_gt 0 (x + y) with hxy0 | hxy0
        · right; left
          rw [hA, hC, hB, hz, abs_of_nonneg hx0, abs_of_neg hy0, abs_of_nonneg hxy0]
          ring
        · right; right; left
          rw [hB, hA, hC, hz, abs_of_neg hy0, abs_of_nonneg hx0, abs_of_neg hxy0]
          ring
      · rcases le_or_gt 0 (x + y) with hxy0 | hxy0
        · right; right; left
          rw [hB, hA, hC, hz, abs_of_nonneg hy0, abs_of_neg hx0, abs_of_nonneg hxy0]
          ring
        · right; left
          rw [hA, hC, hB, hz, abs_of_neg hx0, abs_of_nonneg hy0, abs_of_neg hxy0]
          ring
      · left
        rw [hC, hA, hB, hz, abs_of_neg hx0, abs_of_neg hy0, abs_of_neg (by linarith)]
        ring
    · -- Wraparound below: x + y ≤ -π, so (∡ a v c).toReal = x + y + 2π.
      have hper : ((x + y : ℝ) : Real.Angle) = ((x + y + 2 * π : ℝ) : Real.Angle) := by
        rw [Real.Angle.coe_add (x + y) (2 * π), Real.Angle.coe_two_pi, add_zero]
      have hz : (∡ a v c).toReal = x + y + 2 * π := by
        rw [← key, hper, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith, by linarith⟩]
      have hx0 : x < 0 := by linarith
      have hy0 : y < 0 := by linarith
      right; right; right
      rw [hA, hB, hC, hz, abs_of_neg hx0, abs_of_neg hy0, abs_of_nonneg (by linarith)]
      ring
  · -- Wraparound above: x + y > π, so (∡ a v c).toReal = x + y - 2π.
    have hper : ((x + y : ℝ) : Real.Angle) = ((x + y - 2 * π : ℝ) : Real.Angle) := by
      conv_lhs => rw [show x + y = (x + y - 2 * π) + 2 * π by ring]
      rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
    have hz : (∡ a v c).toReal = x + y - 2 * π := by
      rw [← key, hper, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith, by linarith⟩]
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    right; right; right
    rw [hA, hB, hC, hz, abs_of_pos hx0, abs_of_pos hy0, abs_of_nonpos (by linarith)]
    ring

/-- Fixture (issue #84 acceptance): the 1965 A1 **Y-side** scalar equation.
Given the three pairwise angles of the rays `va`, `vc`, `vy` in the shapes the
benchmark hypotheses produce (`∠ a v c = β`, the external-bisector angle
`∠ c v y = (π − β)/2`, and the isosceles-derived `∠ a v y = π − 2α`), the
three-ray decomposition plus the triangle's angle inequalities force
`α = (π − β)/4` — by `linarith` alone, never `nlinarith` over `∠` atoms. -/
example {v a c y : P} (hav : a ≠ v) (hcv : c ≠ v) (hyv : y ≠ v) {α β : ℝ}
    (hac : ∠ a v c = β) (hcy : ∠ c v y = (π - β) / 2) (hay : ∠ a v y = π - 2 * α)
    (hα0 : 0 < α) (hα : α < π / 2) (hβ : π / 2 < β) (hαγ : α < π - α - β) :
    α = (π - β) / 4 := by
  have hβπ : β ≤ π := hac ▸ EuclideanGeometry.angle_le_pi a v c
  rcases three_ray_angle_decomposition hav hcv hyv with h | h | h | h <;>
    rw [hac, hcy, hay] at h <;> linarith [hα, hβπ]

end Oriented

end LeanChecker.GeometryAngleKit
