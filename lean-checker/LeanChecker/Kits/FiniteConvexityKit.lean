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

/-! ## v2 (issue #87): extreme points and witness extraction

v1 recognizes convex position from explicit separating functionals. The v2
layer connects `ConvexPosition` to Mathlib's extreme-point machinery so hull
STRUCTURE (rather than hand-picked functionals) produces witnesses: any
subset of the extreme points of `convexHull ℝ S` is automatically in convex
position, and a distinct 4-element subset of extreme points yields the
benchmark existential in its exact shape (`∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T,
t ∈ convexHull ℝ (T \ {t})`) — see the fixture.

Route to `putnam_1962_a1` from here (remaining steps):
1. Count extreme points: for a 5-point set with no 3 collinear, the hull's
   extreme-point set has size 3, 4, or 5 (Carathéodory/finite Krein-Milman
   style counting — the genuinely missing piece).
2. Size ≥ 4: choose any 4 extreme points; `convexPosition_of_subset_extremePoints`
   plus `ncard_four` finish in the benchmark shape (the fixture below is this
   step verbatim).
3. Size = 3: the two non-extreme points lie inside the triangle; the line
   through them meets two sides, and those two interior points plus the two
   triangle vertices on one side of that line are in convex position
   (side-of-line case analysis, then the v1 separation criterion). -/

/-- `ConvexPosition` unfolded to the universally quantified form — the shape
`convexPosition_of_subset_extremePoints` and hand proofs actually use. -/
theorem convexPosition_iff_forall {T : Set (ℝ × ℝ)} :
    ConvexPosition T ↔ ∀ t ∈ T, t ∉ convexHull ℝ (T \ {t}) := by
  simp [ConvexPosition]

/-- **Extreme-point exclusion**: an extreme point of `convexHull ℝ S` is
outside the hull of `S` with that point removed. This is the bridge from
Mathlib hull structure to the benchmark's `t ∈ convexHull ℝ (T \ {t})`
membership talk. -/
theorem not_mem_convexHull_diff_of_extremePoint {S : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    (hx : x ∈ (convexHull ℝ S).extremePoints ℝ) :
    x ∉ convexHull ℝ (S \ {x}) := by
  have h := ((convex_convexHull ℝ S).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff).mp hx
  intro hmem
  exact h.2 (convexHull_mono (Set.sdiff_subset_sdiff_left (subset_convexHull ℝ S)) hmem)

/-- **Hull-vertex criterion**: any subset of the extreme points of
`convexHull ℝ S` that is also a subset of `S`'s ambient talk is in convex
position — no separating functionals needed. This is the step-2 workhorse for
the Happy-Ending case split. -/
theorem convexPosition_of_subset_extremePoints {S T : Set (ℝ × ℝ)}
    (hTS : T ⊆ S) (hT : T ⊆ (convexHull ℝ S).extremePoints ℝ) :
    ConvexPosition T := by
  rintro ⟨t, htT, hthull⟩
  exact not_mem_convexHull_diff_of_extremePoint (hT htT)
    (convexHull_mono (Set.sdiff_subset_sdiff_left hTS) hthull)

/-- Four pairwise-distinct points have `ncard = 4` — the cardinality half of
the benchmark existential, packaged so witness extraction is one lemma
application instead of an `ncard_insert` chain. -/
theorem ncard_four {a b c d : ℝ × ℝ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Set (ℝ × ℝ)).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        push Not
        exact ⟨hab, hac, had⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        push Not
        exact ⟨hbc, hbd⟩),
      Set.ncard_insert_of_notMem (by simp only [Set.mem_singleton_iff]; exact hcd),
      Set.ncard_singleton]

/-- Fixture (issue #87 acceptance): **witness extraction in the exact
benchmark shape**. Four pairwise-distinct members of `S` that are extreme
points of its hull yield `∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ
(T \ {t})` — the `putnam_1962_a1` goal verbatim. Once the hull-size case
split lands, the size ≥ 4 branch IS this fixture. -/
example {S : Set (ℝ × ℝ)} {a b c d : ℝ × ℝ}
    (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hext : ({a, b, c, d} : Set (ℝ × ℝ)) ⊆ (convexHull ℝ S).extremePoints ℝ) :
    ∃ T ⊆ S, T.ncard = 4 ∧ ¬∃ t ∈ T, t ∈ convexHull ℝ (T \ {t}) := by
  have hTS : ({a, b, c, d} : Set (ℝ × ℝ)) ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  exact ⟨{a, b, c, d}, hTS, ncard_four hab hac had hbc hbd hcd,
    convexPosition_of_subset_extremePoints hTS hext⟩

end LeanChecker.FiniteConvexityKit
