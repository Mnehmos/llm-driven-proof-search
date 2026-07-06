import Mathlib

/-!
# Finite convexity kit (issue #75)

Finite planar point-set infrastructure for Happy-Ending-style problems: a
`ConvexPosition` predicate in exactly the benchmark's shape, a linear
separation criterion for `convexHull` non-membership, a reusable
per-vertex-separation criterion for convex position, and a four-point fixture.

## Route to `putnam_1962_a1` (remaining gaps, deliberately out of scope here)

1. Hull-size case split for a 5-point set with no 3 collinear: the convex hull
   has 3, 4, or 5 extreme points (extreme-point machinery on finite sets).
2. Hull ≥ 4 vertices: any 4 hull vertices are in convex position (each is
   extreme, hence separated — feed `convexPosition_of_separation`).
3. Hull = 3: the two interior points' line meets two triangle sides; those two
   interior points plus the two vertices on one side of that line are in
   convex position.
-/

namespace LeanChecker.FiniteConvexityKit

/-- Convex position, in exactly the shape `putnam_1962_a1` uses: no point of
`T` lies in the convex hull of the others. -/
def ConvexPosition (T : Set (ℝ × ℝ)) : Prop :=
  ¬∃ t ∈ T, t ∈ convexHull ℝ (T \ {t})

/-- **Separation exclusion**: if a linear functional puts `x` strictly below
everything in `s`, then `x` is outside `convexHull ℝ s`. -/
theorem not_mem_convexHull_of_forall_le {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (c : ℝ) (hs : ∀ y ∈ s, c ≤ f y) (hx : f x < c) :
    x ∉ convexHull ℝ s := by
  intro hmem
  have hsub : convexHull ℝ s ⊆ {y | c ≤ f y} :=
    convexHull_min hs (convex_halfSpace_ge f.isLinear c)
  exact absurd (hsub hmem) (not_le.mpr hx)

/-- **Reusable convex-position criterion**: if every point of `T` is strictly
linearly separated below the rest of `T`, then `T` is in convex position.
Works for any `T` (the Happy-Ending application uses 4-point sets). -/
theorem convexPosition_of_separation {T : Set (ℝ × ℝ)}
    (h : ∀ t ∈ T, ∃ (f : (ℝ × ℝ) →ₗ[ℝ] ℝ) (c : ℝ),
      f t < c ∧ ∀ y ∈ T \ {t}, c ≤ f y) :
    ConvexPosition T := by
  rintro ⟨t, htT, hthull⟩
  obtain ⟨f, c, hft, hother⟩ := h t htT
  exact not_mem_convexHull_of_forall_le f c hother hft hthull

/-- Fixture: the unit square's four corners are in convex position, via one
explicit separating functional per corner. -/
theorem unitSquare_convexPosition :
    ConvexPosition {((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1), (1, 1)} := by
  apply convexPosition_of_separation
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  have mem4 : ∀ y : ℝ × ℝ, y ∈ ({((0 : ℝ), (0 : ℝ)), (1, 0), (0, 1), (1, 1)} : Set (ℝ × ℝ)) →
      y = (0, 0) ∨ y = (1, 0) ∨ y = (0, 1) ∨ y = (1, 1) := by
    intro y hy
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
  rcases ht with rfl | rfl | rfl | rfl
  · -- (0,0): separate below x + y ≥ 1.
    refine ⟨LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ, 1, by norm_num, ?_⟩
    rintro y ⟨hy, hne⟩
    rcases mem4 y hy with rfl | rfl | rfl | rfl
    · exact absurd (Set.mem_singleton _) hne
    · norm_num
    · norm_num
    · norm_num
  · -- (1,0): separate below y − x ≥ 0.
    refine ⟨LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ, 0, by norm_num, ?_⟩
    rintro y ⟨hy, hne⟩
    rcases mem4 y hy with rfl | rfl | rfl | rfl
    · norm_num
    · exact absurd (Set.mem_singleton _) hne
    · norm_num
    · norm_num
  · -- (0,1): separate below x − y ≥ 0.
    refine ⟨LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ, 0, by norm_num, ?_⟩
    rintro y ⟨hy, hne⟩
    rcases mem4 y hy with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · exact absurd (Set.mem_singleton _) hne
    · norm_num
  · -- (1,1): separate below −x − y ≥ −1.
    refine ⟨-(LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ), -1, by norm_num, ?_⟩
    rintro y ⟨hy, hne⟩
    rcases mem4 y hy with rfl | rfl | rfl | rfl
    · norm_num
    · norm_num
    · norm_num
    · exact absurd (Set.mem_singleton _) hne

end LeanChecker.FiniteConvexityKit
