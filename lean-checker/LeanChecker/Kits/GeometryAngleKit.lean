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

end LeanChecker.GeometryAngleKit
