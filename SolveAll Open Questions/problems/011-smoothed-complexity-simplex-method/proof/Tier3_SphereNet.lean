/-
SolveAll #11 — finite sphere-net construction for the Bach--Huiberts lower
bound.

This module supplies the volume-packing estimate behind their Lemma 54.  It is
kept independent of the LP geometry and works in every finite-dimensional real
normed space.
-/
import Mathlib

namespace SolveAll011.Tier3

open Metric Set MeasureTheory
open scoped ENNReal NNReal Function

/-- A finite `η`-separated subset of the unit ball has cardinality at most
`(4/η)^dim` when `0 < η ≤ 2`.  This is the volume estimate used to construct
the dense sphere net in Bach--Huiberts Lemma 54. -/
theorem card_le_four_div_pow_finrank_of_separated
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (η : ℝ) (hη : 0 < η) (hηtwo : η ≤ 2)
    (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → η ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ (4 / η) ^ Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := η / 2
  let ρ : ℝ := 1 + η / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have hdisjoint : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have h := hsep c hc d hd hcd
    dsimp [δ]
    linarith
  have hsubset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (hs x hx)
      _ = ρ := by simp [δ, ρ]; ring
  have hmeasure :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset hdisjoint fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsubset
      _ = ENNReal.ofReal (ρ ^ Module.finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hρ]
  have hcancel :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ Module.finrank ℝ E) ≤
        ENNReal.ofReal (ρ ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hmeasure
  have hreal : (s.card : ℝ) * δ ^ Module.finrank ℝ E ≤ ρ ^ Module.finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hcancel
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] at h
    exact h
  have hδpow : 0 < δ ^ Module.finrank ℝ E := pow_pos hδ _
  have hratio : (s.card : ℝ) ≤ (ρ / δ) ^ Module.finrank ℝ E := by
    rw [div_pow, le_div_iff₀ hδpow]
    exact hreal
  have hbase : ρ / δ ≤ 4 / η := by
    dsimp [ρ, δ]
    field_simp [hη.ne']
    nlinarith
  exact hratio.trans (pow_le_pow_left₀ (by positivity) hbase _)

/-- Existence form of Bach--Huiberts Lemma 54: the unit sphere admits an
internal `η`-net with at most `(4/η)^dim` points. -/
theorem exists_dense_unit_sphere_finset
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (η : ℝ) (hη : 0 < η) (hηtwo : η ≤ 2) :
    ∃ s : Finset E,
      (∀ x ∈ s, ‖x‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 → ∃ x ∈ s, ‖u - x‖ ≤ η) ∧
      (s.card : ℝ) ≤ (4 / η) ^ Module.finrank ℝ E := by
  classical
  let ε : ℝ≥0 := ⟨η, hη.le⟩
  let S : Set E := sphere (0 : E) 1
  have htot : TotallyBounded S := (isCompact_sphere (0 : E) 1).totallyBounded
  have hhalf : (ε / 2 : ℝ≥0) ≠ 0 := by
    apply div_ne_zero
    · have hepsReal : (ε : ℝ) ≠ 0 := by
        change η ≠ 0
        exact hη.ne'
      exact NNReal.coe_ne_zero.mp hepsReal
    · norm_num
  obtain ⟨N, hNsub, hNfinite, hNcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded hhalf htot
  have hpackLe : Metric.packingNumber ε S ≤ N.encard := by
    calc
      Metric.packingNumber ε S = Metric.packingNumber (2 * (ε / 2)) S := by
        congr 2
        field_simp
      _ ≤ Metric.externalCoveringNumber (ε / 2) S :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) S
      _ ≤ N.encard := hNcover.externalCoveringNumber_le_encard
  have hNtop : N.encard ≠ ⊤ := Set.encard_ne_top_iff.mpr hNfinite
  have hpackTop : Metric.packingNumber ε S ≠ ⊤ := by
    exact ne_top_of_le_ne_top hNtop hpackLe
  let C : Set E := Metric.maximalSeparatedSet ε S
  have hCsubset : C ⊆ S := Metric.maximalSeparatedSet_subset
  have hCcover : Metric.IsCover ε S C := Metric.isCover_maximalSeparatedSet hpackTop
  have hCencard : C.encard = Metric.packingNumber ε S :=
    Metric.encard_maximalSeparatedSet hpackTop
  have hCfinite : C.Finite := Set.encard_ne_top_iff.mp (by rw [hCencard]; exact hpackTop)
  let s : Finset E := hCfinite.toFinset
  have hscoe : (s : Set E) = C := by simp [s]
  have hsSphere : ∀ x ∈ s, ‖x‖ = 1 := by
    intro x hx
    have hxC : x ∈ C := by rw [← hscoe]; exact hx
    have hxS : x ∈ S := hCsubset hxC
    simpa [S, mem_sphere] using hxS
  have hsDense : ∀ u : E, ‖u‖ = 1 → ∃ x ∈ s, ‖u - x‖ ≤ η := by
    intro u hu
    have huS : u ∈ S := by simpa [S, mem_sphere] using hu
    obtain ⟨x, hxC, hux⟩ := hCcover huS
    refine ⟨x, ?_, ?_⟩
    · have hxset : x ∈ (s : Set E) := by rw [hscoe]; exact hxC
      exact hxset
    · change edist u x ≤ (ε : ℝ≥0∞) at hux
      have hdist : dist u x ≤ η := by
        have ht := ENNReal.toReal_mono (by simp) hux
        simp only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at ht
        dsimp [ε] at ht
        exact_mod_cast ht
      simpa [dist_eq_norm] using hdist
  have hsSeparated : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → η ≤ ‖c - d‖ := by
    intro c hc d hd hcd
    have hcC : c ∈ C := by rw [← hscoe]; exact hc
    have hdC : d ∈ C := by rw [← hscoe]; exact hd
    have hsep := Metric.isSeparated_maximalSeparatedSet hcC hdC hcd
    change (ε : ℝ≥0∞) < edist c d at hsep
    have hlt : η < dist c d := by
      have ht := (ENNReal.toReal_lt_toReal (by simp) (edist_ne_top c d)).2 hsep
      simp only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at ht
      dsimp [ε] at ht
      exact ht
    exact hlt.le.trans_eq (dist_eq_norm c d)
  refine ⟨s, hsSphere, hsDense, ?_⟩
  exact card_le_four_div_pow_finrank_of_separated s η hη hηtwo
    (fun c hc => (hsSphere c hc).le) hsSeparated

/-- Natural-floor cardinal form used to index the net by the paper's number of
constraints. -/
theorem exists_dense_unit_sphere_finset_natFloor
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (η : ℝ) (hη : 0 < η) (hηtwo : η ≤ 2) :
    ∃ s : Finset E,
      (∀ x ∈ s, ‖x‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 → ∃ x ∈ s, ‖u - x‖ ≤ η) ∧
      s.card ≤ ⌊(4 / η) ^ Module.finrank ℝ E⌋₊ := by
  obtain ⟨s, hsSphere, hsDense, hcard⟩ :=
    exists_dense_unit_sphere_finset (E := E) η hη hηtwo
  refine ⟨s, hsSphere, hsDense, ?_⟩
  rw [Nat.le_floor_iff (pow_nonneg (div_nonneg (by norm_num) hη.le) _)]
  exact hcard

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.card_le_four_div_pow_finrank_of_separated
#print axioms SolveAll011.Tier3.exists_dense_unit_sphere_finset
#print axioms SolveAll011.Tier3.exists_dense_unit_sphere_finset_natFloor
