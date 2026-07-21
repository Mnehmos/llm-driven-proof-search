/-
SolveAll #11 — deterministic geometry from Bach--Huiberts, Lemma 55.

This module formalizes the roundness lemma used in the 2026 lower-bound proof.
If unit normals `s i` are eta-dense on the unit sphere, the actual constraint
normals `a i` are eta-close to them, and right-hand sides lie in
`[1-eta,1+eta]`, then the feasible polyhedron lies between Euclidean balls of
radii `1-2*eta` and `1+4*eta`.

The result is stated in an arbitrary real inner-product space.  Finite
dimensionality and finiteness of the constraint family are not needed for this
deterministic implication.
-/
import Mathlib

namespace SolveAll011.Tier3

open scoped RealInnerProductSpace

/-- Feasible set for a family of normalized linear inequalities. -/
def normalizedFeasible {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (b : ι → ℝ) : Set E :=
  {x | ∀ i, ⟪(a i), x⟫ ≤ b i}

/-- The inner-ball half of Bach--Huiberts Lemma 55. -/
theorem inner_ball_subset_normalizedFeasible
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (s a : ι → E) (b : ι → ℝ)
    (hη : 0 ≤ η) (_hηsmall : η ≤ 1 / 8)
    (hsunit : ∀ i, ‖s i‖ = 1)
    (hpert : ∀ i, ‖a i - s i‖ ≤ η)
    (hbLower : ∀ i, 1 - η ≤ b i) :
    Metric.closedBall (0 : E) (1 - 2 * η) ⊆ normalizedFeasible a b := by
  intro x hx
  change ∀ i, ⟪(a i), x⟫ ≤ b i
  intro i
  have hxnorm : ‖x‖ ≤ 1 - 2 * η := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hanorm : ‖a i‖ ≤ 1 + η := by
    calc
      ‖a i‖ = ‖(a i - s i) + s i‖ := by
        congr 1
        abel
      _ ≤ ‖a i - s i‖ + ‖s i‖ := norm_add_le _ _
      _ ≤ η + 1 := add_le_add (hpert i) (le_of_eq (hsunit i))
      _ = 1 + η := by ring
  calc
    ⟪(a i), x⟫ ≤ ‖a i‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ (1 + η) * (1 - 2 * η) := by
      apply mul_le_mul hanorm hxnorm (norm_nonneg x)
      nlinarith
    _ ≤ 1 - η := by nlinarith [sq_nonneg η]
    _ ≤ b i := hbLower i

/-- The outer-ball half of Bach--Huiberts Lemma 55.  `hdense` is the exact
eta-density property needed: every unit vector is eta-close to one of the
reference normals. -/
theorem normalizedFeasible_subset_outer_ball
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (s a : ι → E) (b : ι → ℝ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hdense : ∀ u : E, ‖u‖ = 1 → ∃ i, ‖u - s i‖ ≤ η)
    (hpert : ∀ i, ‖a i - s i‖ ≤ η)
    (hbUpper : ∀ i, b i ≤ 1 + η) :
    normalizedFeasible a b ⊆ Metric.closedBall (0 : E) (1 + 4 * η) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra houter
  have hxlarge : 1 + 4 * η < ‖x‖ := lt_of_not_ge houter
  have hxnormpos : 0 < ‖x‖ := by nlinarith
  let u : E := (‖x‖⁻¹ : ℝ) • x
  have hunorm : ‖u‖ = 1 := by
    simp [u, norm_smul, inv_mul_cancel₀ hxnormpos.ne']
  obtain ⟨i, huis⟩ := hdense u hunorm
  have huia : ‖u - a i‖ ≤ 2 * η := by
    calc
      ‖u - a i‖ = ‖(u - s i) + (s i - a i)‖ := by
        congr 1
        abel
      _ ≤ ‖u - s i‖ + ‖s i - a i‖ := norm_add_le _ _
      _ = ‖u - s i‖ + ‖a i - s i‖ := by
        rw [show ‖s i - a i‖ = ‖a i - s i‖ from norm_sub_rev _ _]
      _ ≤ η + η := add_le_add huis (hpert i)
      _ = 2 * η := by ring
  have huinner : ⟪u, x⟫ = ‖x‖ := by
    simp only [u, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have herror : ⟪u - (a i), x⟫ ≤ 2 * η * ‖x‖ := by
    calc
      ⟪u - (a i), x⟫ ≤ ‖u - a i‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (2 * η) * ‖x‖ :=
        mul_le_mul_of_nonneg_right huia (norm_nonneg x)
  have hainner : (1 - 2 * η) * ‖x‖ ≤ ⟪(a i), x⟫ := by
    rw [inner_sub_left, huinner] at herror
    nlinarith
  have hstrict : 1 + η < ⟪(a i), x⟫ := by
    have hfactor : 0 < 1 - 2 * η := by nlinarith
    have hproduct : 1 + η < (1 - 2 * η) * ‖x‖ := by
      calc
        1 + η ≤ (1 - 2 * η) * (1 + 4 * η) := by
          nlinarith [sq_nonneg η]
        _ < (1 - 2 * η) * ‖x‖ :=
          mul_lt_mul_of_pos_left hxlarge hfactor
    exact lt_of_lt_of_le hproduct hainner
  exact (not_lt_of_ge (le_trans (hx i) (hbUpper i))) hstrict

/-- Full deterministic roundness sandwich, matching Bach--Huiberts Lemma 55. -/
theorem bachHuiberts_roundness_sandwich
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (s a : ι → E) (b : ι → ℝ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hsunit : ∀ i, ‖s i‖ = 1)
    (hdense : ∀ u : E, ‖u‖ = 1 → ∃ i, ‖u - s i‖ ≤ η)
    (hpert : ∀ i, ‖a i - s i‖ ≤ η)
    (hb : ∀ i, 1 - η ≤ b i ∧ b i ≤ 1 + η) :
    Metric.closedBall (0 : E) (1 - 2 * η) ⊆ normalizedFeasible a b ∧
      normalizedFeasible a b ⊆ Metric.closedBall (0 : E) (1 + 4 * η) := by
  constructor
  · exact inner_ball_subset_normalizedFeasible η s a b hη hηsmall hsunit hpert
      (fun i => (hb i).1)
  · exact normalizedFeasible_subset_outer_ball η s a b hη hηsmall hdense hpert
      (fun i => (hb i).2)

/-- The reciprocal radii used when passing the roundness sandwich to the
polar body.  Bach--Huiberts relax these reciprocals to the cleaner radii
`1 - 4 * η` and `1 + 3 * η`. -/
theorem reciprocal_roundness_bounds (η : ℝ) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8) :
    1 - 4 * η ≤ (1 + 4 * η)⁻¹ ∧ (1 - 2 * η)⁻¹ ≤ 1 + 3 * η := by
  have hposOuter : 0 < 1 + 4 * η := by nlinarith
  have hposInner : 0 < 1 - 2 * η := by nlinarith
  constructor
  · rw [show (1 + 4 * η)⁻¹ = (1 + 4 * η)⁻¹ * 1 by ring,
        le_inv_mul_iff₀ hposOuter]
    nlinarith [sq_nonneg η]
  · rw [inv_le_iff_one_le_mul₀ hposInner]
    nlinarith [sq_nonneg η]

/-- Quantitative closest-point estimate behind the polar-facet diameter
bound in Bach--Huiberts Theorem 57.  If `y` is the minimum-norm point of a
facet, its first-order condition at `v` is exactly `‖y‖² ≤ ⟪y,v⟫`. -/
theorem near_round_facet_point_dist
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (y v : E)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hyLower : 1 - 4 * η ≤ ‖y‖)
    (hvUpper : ‖v‖ ≤ 1 + 3 * η)
    (hclosest : ‖y‖ ^ 2 ≤ ⟪y, v⟫) :
    ‖v - y‖ ≤ Real.sqrt (14 * η) := by
  have hyRadius : 0 ≤ 1 - 4 * η := by nlinarith
  have hvRadius : 0 ≤ 1 + 3 * η := by nlinarith
  have hySqLower : (1 - 4 * η) ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [norm_nonneg y]
  have hvSqUpper : ‖v‖ ^ 2 ≤ (1 + 3 * η) ^ 2 := by
    nlinarith [norm_nonneg v]
  have hinner : ‖y‖ ^ 2 ≤ ⟪v, y⟫ := by
    rwa [real_inner_comm]
  have hsq : ‖v - y‖ ^ 2 ≤ 14 * η := by
    rw [norm_sub_sq_real]
    nlinarith [sq_nonneg η]
  apply le_of_sq_le_sq
  · rw [Real.sq_sqrt (by positivity)]
    exact hsq
  · exact Real.sqrt_nonneg _

/-- Any two points satisfying the same facet first-order condition are at
distance at most `2 * sqrt (14 * η)`.  This is the deterministic diameter
estimate used by the lower-bound construction. -/
theorem near_round_facet_pair_dist
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (y v w : E)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hyLower : 1 - 4 * η ≤ ‖y‖)
    (hvUpper : ‖v‖ ≤ 1 + 3 * η)
    (hwUpper : ‖w‖ ≤ 1 + 3 * η)
    (hvClosest : ‖y‖ ^ 2 ≤ ⟪y, v⟫)
    (hwClosest : ‖y‖ ^ 2 ≤ ⟪y, w⟫) :
    ‖v - w‖ ≤ 2 * Real.sqrt (14 * η) := by
  have hv := near_round_facet_point_dist η y v hη hηsmall hyLower hvUpper hvClosest
  have hw := near_round_facet_point_dist η y w hη hηsmall hyLower hwUpper hwClosest
  calc
    ‖v - w‖ = ‖(v - y) + (y - w)‖ := by
      congr 1
      abel
    _ ≤ ‖v - y‖ + ‖y - w‖ := norm_add_le _ _
    _ = ‖v - y‖ + ‖w - y‖ := by
      rw [show ‖y - w‖ = ‖w - y‖ from norm_sub_rev _ _]
    _ ≤ Real.sqrt (14 * η) + Real.sqrt (14 * η) := add_le_add hv hw
    _ = 2 * Real.sqrt (14 * η) := by ring

/-- The paper's final simplification of the facet-diameter constant. -/
theorem two_sqrt_fourteen_mul_le_eight_sqrt (η : ℝ) (hη : 0 ≤ η) :
    2 * Real.sqrt (14 * η) ≤ 8 * Real.sqrt η := by
  apply le_of_sq_le_sq
  · rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num) hη),
        mul_pow, Real.sq_sqrt hη]
    nlinarith
  · positivity

/-- Exact `8 * sqrt η` polar-facet diameter estimate stated in the proof of
Bach--Huiberts Theorem 57. -/
theorem near_round_facet_pair_dist_eight_sqrt
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : ℝ) (y v w : E)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 8)
    (hyLower : 1 - 4 * η ≤ ‖y‖)
    (hvUpper : ‖v‖ ≤ 1 + 3 * η)
    (hwUpper : ‖w‖ ≤ 1 + 3 * η)
    (hvClosest : ‖y‖ ^ 2 ≤ ⟪y, v⟫)
    (hwClosest : ‖y‖ ^ 2 ≤ ⟪y, w⟫) :
    ‖v - w‖ ≤ 8 * Real.sqrt η :=
  (near_round_facet_pair_dist η y v w hη hηsmall hyLower hvUpper hwUpper
    hvClosest hwClosest).trans (two_sqrt_fourteen_mul_le_eight_sqrt η hη)

/-- A chain of `ℓ` short links has endpoint displacement at most `ℓ * γ`.
This is the metric telescoping step in Bach--Huiberts Lemma 56. -/
theorem norm_chain_le
    {E : Type} [NormedAddCommGroup E]
    (p : ℕ → E) (γ : ℝ) (ℓ : ℕ)
    (hstep : ∀ t < ℓ, ‖p t - p (t + 1)‖ ≤ γ) :
    ‖p 0 - p ℓ‖ ≤ (ℓ : ℝ) * γ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      have hprefix : ∀ t < ℓ, ‖p t - p (t + 1)‖ ≤ γ := by
        intro t ht
        exact hstep t (Nat.lt_trans ht (Nat.lt_succ_self ℓ))
      have hlast : ‖p ℓ - p (ℓ + 1)‖ ≤ γ := hstep ℓ (Nat.lt_succ_self ℓ)
      calc
        ‖p 0 - p (ℓ + 1)‖ = ‖(p 0 - p ℓ) + (p ℓ - p (ℓ + 1))‖ := by
          congr 1
          abel
        _ ≤ ‖p 0 - p ℓ‖ + ‖p ℓ - p (ℓ + 1)‖ := norm_add_le _ _
        _ ≤ (ℓ : ℝ) * γ + γ := add_le_add (ih hprefix) hlast
        _ = (↑(Nat.succ ℓ) : ℝ) * γ := by push_cast; ring

/-- Directed symmetric-difference cardinality satisfies a triangle inequality. -/
theorem card_sdiff_triangle
    {ι : Type} [DecidableEq ι] (s t u : Finset ι) :
    (s \ u).card ≤ (s \ t).card + (t \ u).card := by
  have hsub : s \ u ⊆ (s \ t) ∪ (t \ u) := by
    intro x hx
    have hxu := Finset.mem_sdiff.mp hx
    by_cases hxt : x ∈ t
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxt, hxu.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxu.1, hxt⟩)
  exact (Finset.card_mono hsub).trans (Finset.card_union_le _ _)

/-- Along `ℓ` exchanges that each remove at most one index, at most `ℓ`
indices from the initial basis can disappear. -/
theorem basis_chain_sdiff_card_le
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (ℓ : ℕ)
    (hstep : ∀ t < ℓ, (B t \ B (t + 1)).card ≤ 1) :
    (B 0 \ B ℓ).card ≤ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      have hprefix : ∀ t < ℓ, (B t \ B (t + 1)).card ≤ 1 := by
        intro t ht
        exact hstep t (Nat.lt_trans ht (Nat.lt_succ_self ℓ))
      calc
        (B 0 \ B (ℓ + 1)).card ≤
            (B 0 \ B ℓ).card + (B ℓ \ B (ℓ + 1)).card :=
          card_sdiff_triangle _ _ _
        _ ≤ ℓ + 1 := Nat.add_le_add (ih hprefix) (hstep ℓ (Nat.lt_succ_self ℓ))
        _ = Nat.succ ℓ := by omega

/-- If fewer than `d` one-index exchanges occur, the first and last
`d`-element bases still share an index. -/
theorem basis_chain_inter_nonempty
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (d ℓ : ℕ)
    (hcard : (B 0).card = d) (hℓ : ℓ < d)
    (hstep : ∀ t < ℓ, (B t \ B (t + 1)).card ≤ 1) :
    (B 0 ∩ B ℓ).Nonempty := by
  have hdiff := basis_chain_sdiff_card_le B ℓ hstep
  have hsum := Finset.card_sdiff_add_card_inter (B 0) (B ℓ)
  rw [hcard] at hsum
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hinterzero : (B 0 ∩ B ℓ).card = 0 := by simp [hempty]
  rw [hinterzero, Nat.add_zero] at hsum
  omega

/-- The basis-block overlap assertion used in Bach--Huiberts Lemma 56:
adjacent `d`-element bases intersect in `d-1` indices, so endpoints fewer than
`d` pivots apart have nonempty intersection. -/
theorem adjacent_basis_chain_inter_nonempty
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (d ℓ : ℕ)
    (hcard : ∀ t ≤ ℓ, (B t).card = d)
    (hinter : ∀ t < ℓ, (B t ∩ B (t + 1)).card = d - 1)
    (hℓ : ℓ < d) :
    (B 0 ∩ B ℓ).Nonempty := by
  apply basis_chain_inter_nonempty B d ℓ (hcard 0 (Nat.zero_le _)) hℓ
  intro t ht
  rw [Finset.card_sdiff, hcard t (Nat.le_of_lt ht)]
  rw [Finset.inter_comm, hinter t ht]
  omega

/-- Shifted form of `adjacent_basis_chain_inter_nonempty`, used on each
`d-1`-pivot block of a longer simplex path. -/
theorem adjacent_basis_chain_inter_nonempty_at
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (d start ℓ : ℕ)
    (hcard : ∀ t, (B t).card = d)
    (hinter : ∀ t, (B t ∩ B (t + 1)).card = d - 1)
    (hℓ : ℓ < d) :
    (B start ∩ B (start + ℓ)).Nonempty := by
  let B' : ℕ → Finset ι := fun t => B (start + t)
  have hB' := adjacent_basis_chain_inter_nonempty B' d ℓ
    (fun t _ => hcard (start + t))
    (fun t _ => by simpa [B', Nat.add_assoc] using hinter (start + t)) hℓ
  simpa [B'] using hB'

/-- Bounded shifted form, matching an actual finite path of length `k`. -/
theorem adjacent_basis_chain_inter_nonempty_at_bounded
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (d k start ℓ : ℕ)
    (hcard : ∀ t ≤ k, (B t).card = d)
    (hinter : ∀ t < k, (B t ∩ B (t + 1)).card = d - 1)
    (hend : start + ℓ ≤ k) (hℓ : ℓ < d) :
    (B start ∩ B (start + ℓ)).Nonempty := by
  let B' : ℕ → Finset ι := fun t => B (start + t)
  have hB' := adjacent_basis_chain_inter_nonempty B' d ℓ
    (fun t ht => hcard (start + t) (by omega))
    (fun t ht => by
      simpa [B', Nat.add_assoc] using hinter (start + t) (by omega)) hℓ
  simpa [B'] using hB'

/-- Choose one shared row index from every sampled block boundary of a basis
path.  This constructs the `p_t` sequence in Bach--Huiberts Lemma 56. -/
theorem exists_block_shared_indices
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (d q ℓ : ℕ)
    (hcard : ∀ t, (B t).card = d)
    (hinter : ∀ t, (B t ∩ B (t + 1)).card = d - 1)
    (hq : q < d) :
    ∃ p : Fin ℓ → ι,
      ∀ t : Fin ℓ, p t ∈ B (q * t) ∩ B (q * (t + 1)) := by
  classical
  have hne : ∀ t : Fin ℓ, (B (q * t) ∩ B (q * (t + 1))).Nonempty := by
    intro t
    simpa [Nat.mul_add] using
      adjacent_basis_chain_inter_nonempty_at B d (q * t) q hcard hinter hq
  choose p hp using hne
  exact ⟨p, hp⟩

/-- The last sampled block basis and the actual terminal basis share a row:
the remainder after division by the block size is shorter than one block. -/
theorem quotient_block_endpoint_inter_nonempty
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (d q k : ℕ)
    (hcard : ∀ t, (B t).card = d)
    (hinter : ∀ t, (B t ∩ B (t + 1)).card = d - 1)
    (hqpos : 0 < q) (hq : q < d) :
    (B (q * (k / q)) ∩ B k).Nonempty := by
  have hrem : k % q < d := (Nat.mod_lt k hqpos).trans hq
  have hoverlap := adjacent_basis_chain_inter_nonempty_at
    B d (q * (k / q)) (k % q) hcard hinter hrem
  have hk : q * (k / q) + k % q = k := Nat.div_add_mod k q
  simpa [hk] using hoverlap

/-- Bounded endpoint-block overlap for an actual path indexed only through `k`. -/
theorem quotient_block_endpoint_inter_nonempty_bounded
    {ι : Type} [DecidableEq ι]
    (B : ℕ → Finset ι) (d q k : ℕ)
    (hcard : ∀ t ≤ k, (B t).card = d)
    (hinter : ∀ t < k, (B t ∩ B (t + 1)).card = d - 1)
    (hqpos : 0 < q) (hq : q < d) :
    (B (q * (k / q)) ∩ B k).Nonempty := by
  have hrem : k % q < d := (Nat.mod_lt k hqpos).trans hq
  have hk : q * (k / q) + k % q = k := Nat.div_add_mod k q
  have hoverlap := adjacent_basis_chain_inter_nonempty_at_bounded
    B d k (q * (k / q)) (k % q) hcard hinter (by omega) hrem
  simpa [hk] using hoverlap

/-- The endpoint and link estimates in Lemma 56 imply
`2 / R ≤ (ℓ + 3) * γ`.  The extra three links are one at the maximizing
facet and two at the minimizing facet. -/
theorem antipodal_chain_forces_many_blocks
    {E : Type} [NormedAddCommGroup E]
    (p : ℕ → E) (zPlus zMinus : E) (R γ : ℝ) (ℓ : ℕ)
    (hfar : 2 / R ≤ ‖zPlus - zMinus‖)
    (hstart : ‖zPlus - p 0‖ ≤ γ)
    (hfinish : ‖p ℓ - zMinus‖ ≤ 2 * γ)
    (hstep : ∀ t < ℓ, ‖p t - p (t + 1)‖ ≤ γ) :
    2 / R ≤ ((ℓ : ℝ) + 3) * γ := by
  have hmiddle := norm_chain_le p γ ℓ hstep
  have hupper : ‖zPlus - zMinus‖ ≤ ((ℓ : ℝ) + 3) * γ := by
    calc
      ‖zPlus - zMinus‖ =
          ‖(zPlus - p 0) + ((p 0 - p ℓ) + (p ℓ - zMinus))‖ := by
            congr 1
            abel
      _ ≤ ‖zPlus - p 0‖ + ‖(p 0 - p ℓ) + (p ℓ - zMinus)‖ := norm_add_le _ _
      _ ≤ ‖zPlus - p 0‖ + (‖p 0 - p ℓ‖ + ‖p ℓ - zMinus‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ γ + ((ℓ : ℝ) * γ + 2 * γ) := add_le_add hstart (add_le_add hmiddle hfinish)
      _ = ((ℓ : ℝ) + 3) * γ := by ring
  exact hfar.trans hupper

/-- Numerical conclusion of Bach--Huiberts Lemma 56.  Here `q = d - 1`,
`ℓ = floor (k / q)`, and `q * ℓ ≤ k` is the elementary block-count fact. -/
theorem bachHuiberts_length_from_chain
    (R γ q k ℓ : ℝ)
    (hR : 0 < R) (hγ : 0 < γ) (hq : 0 ≤ q)
    (hblocks : q * ℓ ≤ k)
    (hchain : 2 / R ≤ (ℓ + 3) * γ) :
    q * (2 / (R * γ) - 3) ≤ k := by
  have hRγ : 0 < R * γ := mul_pos hR hγ
  have htwo : 2 ≤ R * ((ℓ + 3) * γ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (div_le_iff₀ hR).mp hchain
  have hℓ : 2 / (R * γ) - 3 ≤ ℓ := by
    rw [sub_le_iff_le_add, div_le_iff₀ hRγ]
    nlinarith
  exact (mul_le_mul_of_nonneg_left hℓ hq).trans hblocks

/-- Basis-path form of the deterministic content of Bach--Huiberts Lemma 56.
The geometric incidence hypotheses say that active normals in one basis have
diameter at most `γ`, the endpoint objective rays are within `γ` of the active
normals of their endpoint bases, and the two rays are at least `2/R` apart.
The theorem constructs the shared-index chain and derives the published path
lower bound. -/
theorem bachHuiberts_basis_path_length_lower_bounded
    {ι E : Type} [DecidableEq ι] [NormedAddCommGroup E]
    (a : ι → E) (B : ℕ → Finset ι)
    (d k : ℕ) (zPlus zMinus : E) (R γ : ℝ)
    (hd : 2 ≤ d) (hR : 0 < R) (hγ : 0 < γ)
    (hcard : ∀ t ≤ k, (B t).card = d)
    (hinter : ∀ t < k, (B t ∩ B (t + 1)).card = d - 1)
    (hfaceDiam : ∀ t ≤ k, ∀ i, i ∈ B t → ∀ j, j ∈ B t → ‖a i - a j‖ ≤ γ)
    (hstart : ∀ i ∈ B 0, ‖zPlus - a i‖ ≤ γ)
    (hfinish : ∀ i ∈ B k, ‖a i - zMinus‖ ≤ γ)
    (hfar : 2 / R ≤ ‖zPlus - zMinus‖) :
    ((d - 1 : ℕ) : ℝ) * (2 / (R * γ) - 3) ≤ (k : ℝ) := by
  classical
  let q : ℕ := d - 1
  let ℓ : ℕ := k / q
  have hqpos : 0 < q := by simp [q]; omega
  have hqd : q < d := by simp [q]; omega
  have hblocksNat : q * ℓ ≤ k := by
    simpa [ℓ] using Nat.mul_div_le k q
  have hterminal : (B (q * ℓ) ∩ B k).Nonempty := by
    exact quotient_block_endpoint_inter_nonempty_bounded B d q k hcard hinter hqpos hqd
  let terminal : ι := Classical.choose hterminal
  have hterminalMem : terminal ∈ B (q * ℓ) ∩ B k := Classical.choose_spec hterminal
  have hterminalParts := Finset.mem_inter.mp hterminalMem
  have hblock : ∀ t < ℓ, (B (q * t) ∩ B (q * (t + 1))).Nonempty := by
    intro t ht
    have hend : q * t + q ≤ k := by
      rw [← Nat.mul_succ]
      exact (Nat.mul_le_mul_left q (by omega)).trans hblocksNat
    simpa [Nat.mul_add] using
      adjacent_basis_chain_inter_nonempty_at_bounded
        B d k (q * t) q hcard hinter hend hqd
  let p : ℕ → ι := fun t =>
    if ht : t < ℓ then Classical.choose (hblock t ht) else terminal
  have hpLt (t : ℕ) (ht : t < ℓ) :
      p t ∈ B (q * t) ∩ B (q * (t + 1)) := by
    simp only [p, dif_pos ht]
    exact Classical.choose_spec (hblock t ht)
  have hpGe (t : ℕ) (ht : ℓ ≤ t) : p t = terminal := by
    simp [p, not_lt_of_ge ht]
  have hpStart : p 0 ∈ B 0 := by
    by_cases hℓpos : 0 < ℓ
    · have hp := (Finset.mem_inter.mp (hpLt 0 hℓpos)).1
      simpa using hp
    · have hℓzero : ℓ = 0 := Nat.eq_zero_of_not_pos hℓpos
      rw [hpGe 0 (by omega)]
      simpa [hℓzero] using hterminalParts.1
  have hpFinish : p ℓ ∈ B k := by
    rw [hpGe ℓ (Nat.le_refl _)]
    exact hterminalParts.2
  have hpStep : ∀ t < ℓ, ‖a (p t) - a (p (t + 1))‖ ≤ γ := by
    intro t ht
    have hleft : p t ∈ B (q * (t + 1)) := (Finset.mem_inter.mp (hpLt t ht)).2
    have hright : p (t + 1) ∈ B (q * (t + 1)) := by
      by_cases hnext : t + 1 < ℓ
      · exact (Finset.mem_inter.mp (hpLt (t + 1) hnext)).1
      · have heq : t + 1 = ℓ := by omega
        rw [heq, hpGe ℓ (Nat.le_refl _)]
        simpa [heq] using hterminalParts.1
    have hindex : q * (t + 1) ≤ k := by
      exact (Nat.mul_le_mul_left q (by omega)).trans hblocksNat
    exact hfaceDiam (q * (t + 1)) hindex (p t) hleft (p (t + 1)) hright
  have hchain : 2 / R ≤ ((ℓ : ℝ) + 3) * γ := by
    apply antipodal_chain_forces_many_blocks (fun t => a (p t)) zPlus zMinus R γ ℓ hfar
    · exact hstart (p 0) hpStart
    · exact (hfinish (p ℓ) hpFinish).trans (by nlinarith)
    · intro t ht
      exact hpStep t ht
  have hblocksReal : (q : ℝ) * (ℓ : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hblocksNat
  simpa [q] using
    bachHuiberts_length_from_chain R γ (q : ℝ) (k : ℝ) (ℓ : ℝ)
      hR hγ (by positivity) hblocksReal hchain

/-- Compatibility wrapper for the earlier unbounded-chain interface. -/
theorem bachHuiberts_basis_path_length_lower
    {ι E : Type} [DecidableEq ι] [NormedAddCommGroup E]
    (a : ι → E) (B : ℕ → Finset ι)
    (d k : ℕ) (zPlus zMinus : E) (R γ : ℝ)
    (hd : 2 ≤ d) (hR : 0 < R) (hγ : 0 < γ)
    (hcard : ∀ t, (B t).card = d)
    (hinter : ∀ t, (B t ∩ B (t + 1)).card = d - 1)
    (hfaceDiam : ∀ t i, i ∈ B t → ∀ j, j ∈ B t → ‖a i - a j‖ ≤ γ)
    (hstart : ∀ i ∈ B 0, ‖zPlus - a i‖ ≤ γ)
    (hfinish : ∀ i ∈ B k, ‖a i - zMinus‖ ≤ γ)
    (hfar : 2 / R ≤ ‖zPlus - zMinus‖) :
    ((d - 1 : ℕ) : ℝ) * (2 / (R * γ) - 3) ≤ (k : ℝ) := by
  exact bachHuiberts_basis_path_length_lower_bounded a B d k zPlus zMinus R γ
    hd hR hγ (fun t _ => hcard t) (fun t _ => hinter t)
    (fun t _ => hfaceDiam t) hstart hfinish hfar

/-- Final Theorem 57 constant arithmetic specialized to `d=2`, the dimension
used in the SolveAll global-norm counterexample.  Writing
`q = σ * sqrt(log(4/σ))`, the paper has `η=8q`, `R=1+32q`, and
`γ=8*sqrt(8q)`. -/
theorem bachHuiberts_d2_final_constant
    (q : ℝ) (hq : 0 < q) (hqsmall : q ≤ 1 / 5200) :
    1 / (24 * Real.sqrt q) ≤
      2 / ((1 + 32 * q) * (8 * Real.sqrt (8 * q))) - 3 := by
  have hq0 : 0 ≤ q := hq.le
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsSq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
  have hs8 : Real.sqrt (8 * q) = Real.sqrt 8 * Real.sqrt q := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
  have hsqrt8 : Real.sqrt 8 ≤ 17 / 6 := by
    apply le_of_sq_le_sq
    · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    · positivity
  have hR : 1 + 32 * q ≤ 1007 / 1000 := by nlinarith
  have hrootProduct : (1 + 32 * q) * Real.sqrt 8 ≤ 3 := by
    calc
      (1 + 32 * q) * Real.sqrt 8 ≤ (1007 / 1000) * (17 / 6) :=
        mul_le_mul hR hsqrt8 (Real.sqrt_nonneg _) (by positivity)
      _ ≤ 3 := by norm_num
  have hdenPos : 0 < (1 + 32 * q) * (8 * Real.sqrt (8 * q)) := by positivity
  have hden : (1 + 32 * q) * (8 * Real.sqrt (8 * q)) ≤
      24 * Real.sqrt q := by
    rw [hs8]
    nlinarith
  have hrecip : 2 / (24 * Real.sqrt q) ≤
      2 / ((1 + 32 * q) * (8 * Real.sqrt (8 * q))) := by
    exact div_le_div_of_nonneg_left (by norm_num) hdenPos hden
  have hs72 : Real.sqrt q ≤ 1 / 72 := by
    by_contra hnot
    have hgt : 1 / 72 < Real.sqrt q := lt_of_not_ge hnot
    have hqUpper : q < (1 / 72 : ℝ) ^ 2 := by
      calc
        q ≤ 1 / 5200 := hqsmall
        _ < (1 / 72 : ℝ) ^ 2 := by norm_num
    nlinarith
  have hthree : 3 ≤ 1 / (24 * Real.sqrt q) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hdouble : 2 / (24 * Real.sqrt q) = 1 / (12 * Real.sqrt q) := by
    field_simp [hs.ne']
    ring
  rw [hdouble] at hrecip
  have hscale : 1 / (12 * Real.sqrt q) =
      2 * (1 / (24 * Real.sqrt q)) := by
    field_simp [hs.ne']
    ring
  linarith

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.inner_ball_subset_normalizedFeasible
#print axioms SolveAll011.Tier3.normalizedFeasible_subset_outer_ball
#print axioms SolveAll011.Tier3.bachHuiberts_roundness_sandwich
#print axioms SolveAll011.Tier3.reciprocal_roundness_bounds
#print axioms SolveAll011.Tier3.near_round_facet_point_dist
#print axioms SolveAll011.Tier3.near_round_facet_pair_dist
#print axioms SolveAll011.Tier3.two_sqrt_fourteen_mul_le_eight_sqrt
#print axioms SolveAll011.Tier3.near_round_facet_pair_dist_eight_sqrt
#print axioms SolveAll011.Tier3.norm_chain_le
#print axioms SolveAll011.Tier3.card_sdiff_triangle
#print axioms SolveAll011.Tier3.basis_chain_sdiff_card_le
#print axioms SolveAll011.Tier3.basis_chain_inter_nonempty
#print axioms SolveAll011.Tier3.adjacent_basis_chain_inter_nonempty
#print axioms SolveAll011.Tier3.adjacent_basis_chain_inter_nonempty_at
#print axioms SolveAll011.Tier3.adjacent_basis_chain_inter_nonempty_at_bounded
#print axioms SolveAll011.Tier3.exists_block_shared_indices
#print axioms SolveAll011.Tier3.quotient_block_endpoint_inter_nonempty
#print axioms SolveAll011.Tier3.quotient_block_endpoint_inter_nonempty_bounded
#print axioms SolveAll011.Tier3.antipodal_chain_forces_many_blocks
#print axioms SolveAll011.Tier3.bachHuiberts_length_from_chain
#print axioms SolveAll011.Tier3.bachHuiberts_basis_path_length_lower
#print axioms SolveAll011.Tier3.bachHuiberts_basis_path_length_lower_bounded
#print axioms SolveAll011.Tier3.bachHuiberts_d2_final_constant
