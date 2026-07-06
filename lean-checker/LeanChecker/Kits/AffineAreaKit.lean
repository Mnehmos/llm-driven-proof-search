import Mathlib

/-!
# Affine area kit (issue #73)

Coordinate scaffolding for Putnam-style cevian / Routh-type triangle area
problems: an explicit signed-area determinant, a ratio-`k` division point with
its `segment` membership and vector-ratio characterization, and computational
fixtures showing the intended endgame (`norm_num`/`ring` over explicit
coordinates, never a raw fight with `volume (convexHull …)`).

## Route to `putnam_1962_a3` (remaining gaps, deliberately out of scope here)

1. Affine normalization: reduce a noncollinear triangle in
   `EuclideanSpace ℝ (Fin 2)` to the frame `(0,0), (1,0), (0,1)` (area ratios
   are invariant under invertible affine maps).
2. Cevian intersection coordinates for general `k` (the fixture below pins the
   classical `k = 2` "one-seventh triangle" instance).
3. The measure bridge `volume (convexHull ℝ {a, b, c}) = |triangleDet a b c| / 2`
   (ENNReal-valued) — the genuinely missing Mathlib piece.
-/

namespace LeanChecker.AffineAreaKit

/-- Twice the signed area of the triangle `(a, b, c)` in the coordinate
plane: the classic 2×2 determinant of the edge vectors at `a`. -/
def triangleDet (a b c : ℝ × ℝ) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

/-- The point on segment `[b, c]` dividing it with ratio `k` on the `c` side:
`divPoint b c k − c = k • (b − divPoint b c k)` (so for a cevian problem's
"`CA'/A'B = k`", take `A' = divPoint B C k`). -/
noncomputable def divPoint (b c : ℝ × ℝ) (k : ℝ) : ℝ × ℝ :=
  ((k * b.1 + c.1) / (k + 1), (k * b.2 + c.2) / (k + 1))

/-- **Segment-ratio coordinate lemma**: the ratio-`k` division point lies on
the segment. -/
theorem divPoint_mem_segment (b c : ℝ × ℝ) {k : ℝ} (hk : 0 ≤ k) :
    divPoint b c k ∈ segment ℝ b c := by
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  refine ⟨k / (k + 1), 1 / (k + 1), by positivity, by positivity, ?_, ?_⟩
  · field_simp
  · have h : ∀ u v : ℝ, k / (k + 1) * u + 1 / (k + 1) * v = (k * u + v) / (k + 1) := by
      intro u v
      field_simp
    apply Prod.ext
    · simpa [divPoint, Prod.smul_def, smul_eq_mul] using h b.1 c.1
    · simpa [divPoint, Prod.smul_def, smul_eq_mul] using h b.2 c.2

/-- **Segment-ratio vector characterization**: `divPoint b c k` divides the
segment with ratio `k` on the `c` side, stated affinely (no metric, so it is
immune to the `ℝ × ℝ` sup-metric trap — `dist` on the product is NOT the
Euclidean distance). -/
theorem divPoint_ratio (b c : ℝ × ℝ) {k : ℝ} (hk : k + 1 ≠ 0) :
    divPoint b c k - c = k • (b - divPoint b c k) := by
  apply Prod.ext
  · simp only [divPoint, Prod.fst_sub, Prod.smul_def, smul_eq_mul]
    field_simp
    ring
  · simp only [divPoint, Prod.snd_sub, Prod.smul_def, smul_eq_mul]
    field_simp
    ring

/-- The normalized frame has determinant 1. -/
@[simp] theorem triangleDet_normalized :
    triangleDet (0, 0) (1, 0) (0, 1) = 1 := by
  norm_num [triangleDet]

/-- **Area-ratio invariance under translation** — determinant areas depend
only on edge vectors. -/
theorem triangleDet_translate (t a b c : ℝ × ℝ) :
    triangleDet (a + t) (b + t) (c + t) = triangleDet a b c := by
  simp only [triangleDet, Prod.fst_add, Prod.snd_add]
  ring

/-- Fixture (Routh, `k = 2` — the classical "one-seventh triangle"): the inner
triangle of the `k = 2` cevians of the normalized frame has area ratio
`(k−1)²/(k²+k+1) = 1/7`, by pure coordinate computation. The intersection
points are `P = BB' ∩ CC'`, `Q = CC' ∩ AA'`, `R = AA' ∩ BB'` for
`A' = divPoint B C 2`, `B' = divPoint C A 2`, `C' = divPoint A B 2`. -/
example :
    triangleDet ((1 : ℝ)/7, (4 : ℝ)/7) ((2 : ℝ)/7, (1 : ℝ)/7) ((4 : ℝ)/7, (2 : ℝ)/7) /
      triangleDet (0, 0) (1, 0) (0, 1) = ((2 : ℝ) - 1) ^ 2 / (2 ^ 2 + 2 + 1) := by
  norm_num [triangleDet]

/-- Fixture: the `k = 2` division points of the normalized frame are where the
one-seventh construction says they are. -/
example : divPoint ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) 2 = (2/3, 1/3) := by
  norm_num [divPoint]

end LeanChecker.AffineAreaKit
