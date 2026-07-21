/-
SolveAll #11 — normalized LP bases and simplex basis paths.

The Bach--Huiberts polar argument uses a minimal normalized inequality
description `⟪aᵢ,x⟫ ≤ 1`.  This module connects that description to the actual
smoothed data `⟪Aᵢ,x⟫ ≤ bᵢ` when every `bᵢ` is positive, then records the
concrete feasible-basis and one-index-exchange semantics of a simplex path.
-/
import Mathlib

namespace SolveAll011.Tier3

open scoped RealInnerProductSpace

/-- Normalize a constraint with positive right-hand side. -/
noncomputable def normalizedNormal
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : ι → E) (b : ι → ℝ) (i : ι) : E :=
  (b i)⁻¹ • A i

/-- Dividing one affine inequality by a positive right-hand side preserves it. -/
theorem normalized_constraint_iff
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : ι → E) (b : ι → ℝ) (i : ι) (x : E) (hb : 0 < b i) :
    ⟪normalizedNormal A b i, x⟫ ≤ 1 ↔ ⟪A i, x⟫ ≤ b i := by
  rw [normalizedNormal, inner_smul_left, starRingEnd_apply, star_trivial]
  change (b i)⁻¹ * ⟪A i, x⟫ ≤ 1 ↔ _
  rw [inv_mul_le_one₀ hb]

/-- The original and normalized feasible polyhedra are exactly equal when all
right-hand sides are positive. -/
theorem normalized_feasible_eq
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : ι → E) (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    {x : E | ∀ i, ⟪normalizedNormal A b i, x⟫ ≤ 1} =
      {x : E | ∀ i, ⟪A i, x⟫ ≤ b i} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx i
    exact (normalized_constraint_iff A b i x (hb i)).1 (hx i)
  · intro hx i
    exact (normalized_constraint_iff A b i x (hb i)).2 (hx i)

/-- The high-probability right-hand-side event in Theorem 57 guarantees all
right-hand sides are positive, so normalization is legitimate. -/
theorem rhs_positive_of_abs_sub_one_le
    {ι : Type} (b : ι → ℝ) (η : ℝ) (hη : η < 1)
    (hb : ∀ i, |b i - 1| ≤ η) : ∀ i, 0 < b i := by
  intro i
  have hlower := (abs_le.mp (hb i)).1
  linarith

/-- Every normalized constraint normal lies in the polar of the original
feasible polyhedron. -/
theorem normalizedNormal_mem_polar_feasible
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : ι → E) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (i : ι) :
    normalizedNormal A b i ∈
      {y : E | ∀ x ∈ {x : E | ∀ j, ⟪A j, x⟫ ≤ b j}, ⟪x, y⟫ ≤ 1} := by
  intro x hx
  rw [real_inner_comm]
  exact (normalized_constraint_iff A b i x (hb i)).2 (hx i)

/-- A concrete full-dimensional feasible basis for a normalized inequality LP.
The active normals are required to be linearly independent, so the basis
determines at most one primal point. -/
structure NormalizedFeasibleBasis
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) where
  indices : Finset ι
  vertex : E
  card_eq : indices.card = Module.finrank ℝ E
  feasible : ∀ i, ⟪a i, vertex⟫ ≤ 1
  active : ∀ i ∈ indices, ⟪a i, vertex⟫ = 1
  independent : LinearIndependent ℝ (fun i : {i // i ∈ indices} => a i)

/-- Two full bases are simplex-adjacent when they share exactly `d-1` active
constraints, i.e. one constraint leaves and one enters. -/
def NormalizedFeasibleBasis.Adjacent
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ι → E} (B C : NormalizedFeasibleBasis a) : Prop :=
  (B.indices ∩ C.indices).card + 1 = Module.finrank ℝ E

/-- A finite concrete simplex path represented by feasible bases. -/
structure NormalizedSimplexPath
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (k : ℕ) where
  basis : Fin (k + 1) → NormalizedFeasibleBasis a
  adjacent : ∀ t : Fin k,
    (basis (Fin.castSucc t)).Adjacent (basis t.succ)

/-- Every consecutive pair in a concrete simplex basis path intersects in
exactly `d-1` indices, the combinatorial hypothesis used in Lemma 56. -/
theorem NormalizedSimplexPath.consecutive_inter_card
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ι → E} {k : ℕ} (p : NormalizedSimplexPath a k) (t : Fin k) :
    ((p.basis (Fin.castSucc t)).indices ∩ (p.basis t.succ).indices).card =
      Module.finrank ℝ E - 1 := by
  have hadj := p.adjacent t
  change ((p.basis (Fin.castSucc t)).indices ∩
    (p.basis t.succ).indices).card + 1 = Module.finrank ℝ E at hadj
  omega

/-- Extend the finite path's basis-index sequence to natural indices.  Values
beyond the charged path length are irrelevant; bounded path theorems only query
`t ≤ k`. -/
noncomputable def NormalizedSimplexPath.indicesAt
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ι → E} {k : ℕ} (p : NormalizedSimplexPath a k) (t : ℕ) : Finset ι :=
  if ht : t ≤ k then (p.basis ⟨t, Nat.lt_succ_iff.mpr ht⟩).indices
  else (p.basis 0).indices

/-- Every in-range entry of the natural-index extension is a full basis. -/
theorem NormalizedSimplexPath.indicesAt_card
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ι → E} {k : ℕ} (p : NormalizedSimplexPath a k)
    (t : ℕ) (ht : t ≤ k) :
    (p.indicesAt t).card = Module.finrank ℝ E := by
  simp [NormalizedSimplexPath.indicesAt, ht,
    (p.basis ⟨t, Nat.lt_succ_iff.mpr ht⟩).card_eq]

/-- Every charged transition in the natural-index extension exchanges exactly
one active constraint. -/
theorem NormalizedSimplexPath.indicesAt_inter_card
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ι → E} {k : ℕ} (p : NormalizedSimplexPath a k)
    (t : ℕ) (ht : t < k) :
    (p.indicesAt t ∩ p.indicesAt (t + 1)).card = Module.finrank ℝ E - 1 := by
  let ft : Fin k := ⟨t, ht⟩
  have h := p.consecutive_inter_card ft
  have ht0 : t ≤ k := (Nat.le_of_lt ht).trans (Nat.le_refl k)
  have ht1 : t + 1 ≤ k := by omega
  simpa [NormalizedSimplexPath.indicesAt, ht0, ht1, ft] using h

/-- The active equations of a linearly independent full basis determine its
vertex uniquely. -/
theorem NormalizedFeasibleBasis.vertex_unique
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {a : ι → E} (B : NormalizedFeasibleBasis a) (x : E)
    (hx : ∀ i ∈ B.indices, ⟪a i, x⟫ = 1) : x = B.vertex := by
  have hspan : Submodule.span ℝ (Set.range fun i : {i // i ∈ B.indices} => a i) = ⊤ := by
    apply B.independent.span_eq_top_of_card_eq_finrank'
    simp [B.card_eq]
  let L : E →ₗ[ℝ] ℝ := (innerSL ℝ (x - B.vertex)).toLinearMap
  have hrange : (Set.range fun i : {i // i ∈ B.indices} => a i) ⊆ LinearMap.ker L := by
    rintro y ⟨i, rfl⟩
    change ⟪x - B.vertex, a i⟫ = 0
    rw [real_inner_comm, inner_sub_right, hx i i.property, B.active i i.property, sub_self]
  have hspanKer : Submodule.span ℝ
      (Set.range fun i : {i // i ∈ B.indices} => a i) ≤ LinearMap.ker L :=
    Submodule.span_le.2 hrange
  have hmem : x - B.vertex ∈ LinearMap.ker L := by
    apply hspanKer
    rw [hspan]
    exact Submodule.mem_top
  have hself : ⟪x - B.vertex, x - B.vertex⟫ = 0 := by
    change L (x - B.vertex) = 0 at hmem
    change ⟪x - B.vertex, x - B.vertex⟫ = 0 at hmem
    exact hmem
  rw [real_inner_self_eq_norm_sq] at hself
  have hnorm : ‖x - B.vertex‖ = 0 := by nlinarith [norm_nonneg (x - B.vertex)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

#print axioms normalized_constraint_iff
#print axioms normalized_feasible_eq
#print axioms rhs_positive_of_abs_sub_one_le
#print axioms normalizedNormal_mem_polar_feasible
#print axioms NormalizedSimplexPath.consecutive_inter_card
#print axioms NormalizedSimplexPath.indicesAt_card
#print axioms NormalizedSimplexPath.indicesAt_inter_card
#print axioms NormalizedFeasibleBasis.vertex_unique

end SolveAll011.Tier3
