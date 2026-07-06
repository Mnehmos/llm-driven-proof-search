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

/-! ## v2 (issue #85): general-`k` pipeline and the volume bridge

v1 pinned the classical `k = 2` instance; v2 supplies the general-`k`
computational pipeline: closed-form division points on the normalized frame,
a cevian-intersection fixture with genuine `segment` membership, the Routh
inner-triangle determinant `(k−1)²/(k²+k+1)` for ALL real `k`, and the volume
bridge `volume (convexHull {a,b,c}) = ofReal |triangleDet a b c| · V₀` where
`V₀ = volume (convexHull {(0,0),(1,0),(0,1)})` is the standard-triangle
constant.

**Exactly one Mathlib piece is still missing** (documented per issue #85's
acceptance criteria): a named lemma computing
`volume (convexHull ℝ {((0:ℝ),(0:ℝ)), (1,0), (0,1)}) = ENNReal.ofReal (1/2)`.
It is provable via `regionBetween` (the standard triangle is the region
between `0` and `x ↦ 1 − x` over `[0,1]`, whose integral is `1/2`) plus a
set-equality with the hull, but no such lemma exists in the pinned Mathlib.
For `putnam_1962_a3` the constant CANCELS in the target ratio
`volume(hull PQR).toReal / volume(hull ABC).toReal`, so the remaining needs
are only `0 < V₀ < ∞` (positivity via interior nonempty, finiteness via
boundedness) rather than its exact value.

Route to `putnam_1962_a3` from here (remaining steps):
1. Extract `A' = divPoint B C k` (and cyclic) from the benchmark's
   `A' ∈ segment ℝ B C ∧ dist C A' / dist A' B = k` hypotheses.
2. Affine normalization of the noncollinear `A B C` to the standard frame
   (area ratios invariant — the bridge below does the measure side).
3. Feed `routh_inner_det` + `volume_convexHull_triangle` into the ratio, and
   cancel `V₀` using `0 < V₀ < ∞`. -/

section V2

open MeasureTheory

/-- Normalized-frame side `BC` division point, general `k`. -/
@[simp] theorem divPoint_frame_BC (k : ℝ) :
    divPoint ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) k = (k / (k + 1), 1 / (k + 1)) := by
  norm_num [divPoint]

/-- Normalized-frame side `CA` division point, general `k`. -/
@[simp] theorem divPoint_frame_CA (k : ℝ) :
    divPoint ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (0 : ℝ)) k = (0, k / (k + 1)) := by
  norm_num [divPoint]

/-- Normalized-frame side `AB` division point, general `k`. -/
@[simp] theorem divPoint_frame_AB (k : ℝ) :
    divPoint ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) k = (1 / (k + 1), 0) := by
  norm_num [divPoint]

/-- The Routh denominator never vanishes over `ℝ`. -/
theorem routh_denom_ne_zero (k : ℝ) : k ^ 2 + k + 1 ≠ 0 := by
  nlinarith [sq_nonneg (2 * k + 1)]

/-- Fixture (issue #85 acceptance): **general-`k` cevian intersection**. The
point `(k, 1)/(k² + k + 1)` lies on BOTH the cevian `A–A'` and the cevian
`C–C'` of the normalized frame — real `segment` membership, not just a line
equation. (This is the point `Q = CC' ∩ AA'`; `P` and `R` are its cyclic
images, visible in the determinant fixture below.) -/
theorem cevian_intersection_general (k : ℝ) (hk : 0 ≤ k) :
    (k / (k ^ 2 + k + 1), 1 / (k ^ 2 + k + 1)) ∈
        segment ℝ ((0 : ℝ), (0 : ℝ)) (divPoint ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) k) ∧
    (k / (k ^ 2 + k + 1), 1 / (k ^ 2 + k + 1)) ∈
        segment ℝ ((0 : ℝ), (1 : ℝ)) (divPoint ((0 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) k) := by
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have hD : (0 : ℝ) < k ^ 2 + k + 1 := by nlinarith [sq_nonneg k]
  rw [divPoint_frame_BC, divPoint_frame_AB]
  constructor
  · refine ⟨1 - (k + 1) / (k ^ 2 + k + 1), (k + 1) / (k ^ 2 + k + 1), ?_, by positivity,
      by ring, ?_⟩
    · rw [sub_nonneg]
      rw [div_le_one hD]
      nlinarith [sq_nonneg k]
    · simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> (field_simp; ring)
  · refine ⟨1 - k * (k + 1) / (k ^ 2 + k + 1), k * (k + 1) / (k ^ 2 + k + 1), ?_, by positivity,
      by ring, ?_⟩
    · rw [sub_nonneg]
      rw [div_le_one hD]
      nlinarith
    · simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> (field_simp; ring)

/-- **Routh inner-triangle determinant, general `k`** (issue #85 acceptance):
the cevian intersection triangle `P Q R` of the normalized frame has
`triangleDet = (k − 1)²/(k² + k + 1)` — for every real `k`, by `field_simp`
and `ring` alone. At `k = 2` this is the v1 one-seventh fixture. -/
theorem routh_inner_det (k : ℝ) :
    triangleDet (1 / (k ^ 2 + k + 1), k ^ 2 / (k ^ 2 + k + 1))
        (k / (k ^ 2 + k + 1), 1 / (k ^ 2 + k + 1))
        (k ^ 2 / (k ^ 2 + k + 1), k / (k ^ 2 + k + 1))
      = (k - 1) ^ 2 / (k ^ 2 + k + 1) := by
  have hD := routh_denom_ne_zero k
  have hDD : (k ^ 2 + k + 1) * (k ^ 2 + k + 1) ≠ 0 := mul_ne_zero hD hD
  simp only [triangleDet, div_sub_div_same, div_mul_div_comm]
  rw [div_eq_div_iff hDD hD]
  ring

/-- The edge map of the triangle `(a, b, c)`: the linear map sending the
standard frame's edge vectors `(1,0)`, `(0,1)` to the edge vectors
`b − a`, `c − a`. -/
noncomputable def edgeMap (a b c : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![b.1 - a.1, c.1 - a.1; b.2 - a.2, c.2 - a.2]

theorem edgeMap_det (a b c : ℝ × ℝ) :
    LinearMap.det (edgeMap a b c) = triangleDet a b c := by
  rw [edgeMap, LinearMap.det_toLin, Matrix.det_fin_two_of, triangleDet]

theorem edgeMap_e1 (a b c : ℝ × ℝ) : edgeMap a b c (1, 0) = b - a := by
  have h : ((1 : ℝ), (0 : ℝ)) = Module.Basis.finTwoProd ℝ 0 := by simp
  rw [edgeMap, h, Matrix.toLin_self]
  simp [Fin.sum_univ_two, Prod.ext_iff]

theorem edgeMap_e2 (a b c : ℝ × ℝ) : edgeMap a b c (0, 1) = c - a := by
  have h : ((0 : ℝ), (1 : ℝ)) = Module.Basis.finTwoProd ℝ 1 := by simp
  rw [edgeMap, h, Matrix.toLin_self]
  simp [Fin.sum_univ_two, Prod.ext_iff]

/-- **Volume bridge, partial form** (issue #85 acceptance): the Lebesgue
volume of ANY coordinate triangle is `|triangleDet|` times the
standard-triangle constant `V₀ = volume (convexHull {(0,0),(1,0),(0,1)})`.
Together with a future `V₀ = 1/2` (or mere `0 < V₀ < ∞`, which suffices for
ratio problems), this closes the benchmark's `volume (convexHull …)` gap. -/
theorem volume_convexHull_triangle (a b c : ℝ × ℝ) :
    volume (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) =
      ENNReal.ofReal |triangleDet a b c| *
        volume (convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} : Set (ℝ × ℝ))) := by
  set f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
    AffineMap.const ℝ (ℝ × ℝ) a + (edgeMap a b c).toAffineMap with hf
  have hcoe : ⇑f = (fun x => a + x) ∘ ⇑(edgeMap a b c) := by
    funext x
    simp [hf]
  have himg : f '' ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} : Set (ℝ × ℝ)) = {a, b, c} := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    have h0 : f ((0 : ℝ), (0 : ℝ)) = a := by simp [hcoe, Prod.mk_zero_zero]
    have h1 : f ((1 : ℝ), (0 : ℝ)) = b := by simp [hcoe, edgeMap_e1]
    have h2 : f ((0 : ℝ), (1 : ℝ)) = c := by simp [hcoe, edgeMap_e2]
    rw [h0, h1, h2]
  calc volume (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)))
      = volume (f '' convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} : Set (ℝ × ℝ))) := by
        rw [AffineMap.image_convexHull, himg]
    _ = volume ((fun x => a + x) ''
          (⇑(edgeMap a b c) '' convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} : Set (ℝ × ℝ)))) := by
        rw [hcoe, Set.image_comp]
    _ = volume (⇑(edgeMap a b c) '' convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} : Set (ℝ × ℝ))) := by
        rw [Set.image_add_left, measure_preimage_add]
    _ = ENNReal.ofReal |triangleDet a b c| *
          volume (convexHull ℝ ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1)} : Set (ℝ × ℝ))) := by
        rw [Measure.addHaar_image_linearMap, edgeMap_det]

end V2

end LeanChecker.AffineAreaKit
