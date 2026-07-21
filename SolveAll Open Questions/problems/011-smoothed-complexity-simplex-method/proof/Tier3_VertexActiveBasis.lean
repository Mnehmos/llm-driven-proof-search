/-
SolveAll #11 — extreme points have full active bases.

For a finite inequality polyhedron, an extreme point cannot have active
normals spanning a proper subspace: an orthogonal direction would permit a
small feasible displacement in both signs.  This is the missing deterministic
bridge from Mathlib's `extremePoints` to the concrete basis representation used
by the Bach--Huiberts path argument.
-/
import Mathlib

namespace SolveAll011.Tier3

open scoped RealInnerProductSpace

noncomputable def inequalityFeasible
    {ι E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) : Set E :=
  {x | ∀ i, ⟪a i, x⟫ ≤ 1}

noncomputable def activeConstraints
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (x : E) : Finset ι :=
  Finset.univ.filter fun i => ⟪a i, x⟫ = 1

/-- Every active normal belongs to the span of the active-normal family. -/
theorem active_normal_mem_span
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ι → E) (x : E) (i : ι) (hi : i ∈ activeConstraints a x) :
    a i ∈ Submodule.span ℝ
      (Set.range fun j : {j // j ∈ activeConstraints a x} => a j) := by
  apply Submodule.subset_span
  exact ⟨⟨i, hi⟩, rfl⟩

/-- At an extreme point of a finite inequality polyhedron, the active normals
span the whole ambient space. -/
theorem activeNormals_span_eq_top_of_extremePoint
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (x : E)
    (hx : x ∈ (inequalityFeasible a).extremePoints ℝ) :
    Submodule.span ℝ
      (Set.range fun i : {i // i ∈ activeConstraints a x} => a i) = ⊤ := by
  classical
  let W : Submodule ℝ E := Submodule.span ℝ
    (Set.range fun i : {i // i ∈ activeConstraints a x} => a i)
  by_contra hW
  have horth : Wᗮ ≠ ⊥ := by
    intro hbot
    exact hW ((Submodule.orthogonal_eq_bot_iff).mp hbot)
  obtain ⟨v, hvorth, hvne⟩ := (Submodule.ne_bot_iff Wᗮ).mp horth
  let U : Set E := ⋂ i : ι,
    if i ∈ activeConstraints a x then Set.univ else {y | ⟪a i, y⟫ < 1}
  have hUopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact isOpen_univ
    · exact isOpen_lt (by fun_prop) continuous_const
  have hxU : x ∈ U := by
    rw [Set.mem_iInter]
    intro i
    by_cases hi : i ∈ activeConstraints a x
    · simp [hi]
    · have hle := hx.1 i
      have hne : ⟪a i, x⟫ ≠ 1 := by
        simpa [activeConstraints] using hi
      have hlt : ⟪a i, x⟫ < 1 := lt_of_le_of_ne hle hne
      simpa [U, hi] using hlt
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  let t : ℝ := ε / (2 * ‖v‖)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have htv : ‖t • v‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp
    nlinarith
  have hplusU : x + t • v ∈ U := hεU (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact htv)
  have hminusU : x - t • v ∈ U := hεU (by
    rw [Metric.mem_ball, dist_eq_norm]
    have : x - t • v - x = -(t • v) := by abel
    rw [this, norm_neg]
    exact htv)
  have hactive_orth : ∀ i ∈ activeConstraints a x, ⟪a i, v⟫ = 0 := by
    intro i hi
    exact Submodule.inner_right_of_mem_orthogonal
      (show a i ∈ W from active_normal_mem_span a x i hi) hvorth
  have hplus : x + t • v ∈ inequalityFeasible a := by
    intro i
    by_cases hi : i ∈ activeConstraints a x
    · have hxi : ⟪a i, x⟫ = 1 := by simpa [activeConstraints] using hi
      rw [inner_add_right, inner_smul_right, hactive_orth i hi, mul_zero, add_zero, hxi]
    · have hiU := Set.mem_iInter.mp hplusU i
      have hilt : ⟪a i, x + t • v⟫ < 1 := by simpa [U, hi] using hiU
      exact hilt.le
  have hminus : x - t • v ∈ inequalityFeasible a := by
    intro i
    by_cases hi : i ∈ activeConstraints a x
    · have hxi : ⟪a i, x⟫ = 1 := by simpa [activeConstraints] using hi
      rw [inner_sub_right, inner_smul_right, hactive_orth i hi, mul_zero, sub_zero, hxi]
    · have hiU := Set.mem_iInter.mp hminusU i
      have hilt : ⟪a i, x - t • v⟫ < 1 := by simpa [U, hi] using hiU
      exact hilt.le
  have heq := hx.2 hminus hplus (mem_openSegment_sub_add (𝕜 := ℝ) x (t • v))
  have htvzero : t • v = 0 := sub_eq_self.mp heq
  exact hvne (smul_eq_zero.mp htvzero |>.resolve_left (ne_of_gt ht))

/-- Hence an extreme point contains an injectively indexed, linearly independent
active family of exactly `finrank E` normals. -/
theorem exists_active_basis_indexing_of_extremePoint
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (x : E)
    (hx : x ∈ (inequalityFeasible a).extremePoints ℝ) :
    ∃ g : Fin (Module.finrank ℝ E) → ι,
      Function.Injective g ∧
      (∀ j, g j ∈ activeConstraints a x) ∧
      LinearIndependent ℝ (fun j => a (g j)) := by
  classical
  let S : Set E := Set.range fun i : {i // i ∈ activeConstraints a x} => a i
  have hspan : Submodule.span ℝ S = ⊤ := by
    simpa [S] using activeNormals_span_eq_top_of_extremePoint a x hx
  obtain ⟨f, hfmem, -, hfli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  have hfinrank : Module.finrank ℝ (Submodule.span ℝ S) = Module.finrank ℝ E := by
    rw [hspan, finrank_top]
  let e : Fin (Module.finrank ℝ E) ≃ Fin (Module.finrank ℝ (Submodule.span ℝ S)) :=
    finCongr hfinrank.symm
  let f' : Fin (Module.finrank ℝ E) → E := f ∘ e
  have hf'mem : ∀ j, f' j ∈ S := fun j => hfmem (e j)
  have hf'li : LinearIndependent ℝ f' := hfli.comp e e.injective
  have hex : ∀ j, ∃ i : {i // i ∈ activeConstraints a x}, a i = f' j := by
    intro j
    simpa [S] using hf'mem j
  choose g hgf using hex
  refine ⟨fun j => g j, ?_, fun j => (g j).property, ?_⟩
  · intro j k hjk
    apply hf'li.injective
    rw [← hgf j, ← hgf k]
    exact congrArg a hjk
  · simpa only [hgf] using hf'li

/-- If no `dim+1` constraints can be simultaneously active, the full active
set of an extreme point has exactly `dim` members.  Affine general position of
the augmented rows is a sufficient source of this hypothesis. -/
theorem activeConstraints_card_eq_finrank_of_extremePoint
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (x : E)
    (hx : x ∈ (inequalityFeasible a).extremePoints ℝ)
    (hno : ∀ S : Finset ι, S.card = Module.finrank ℝ E + 1 →
      ¬ (∀ i ∈ S, ⟪a i, x⟫ = 1)) :
    (activeConstraints a x).card = Module.finrank ℝ E := by
  classical
  have hspan := activeNormals_span_eq_top_of_extremePoint a x hx
  have hlower : Module.finrank ℝ E ≤ (activeConstraints a x).card := by
    have := finrank_le_of_span_eq_top
      (v := fun i : {i // i ∈ activeConstraints a x} => a i) hspan
    simpa using this
  have hupper : (activeConstraints a x).card ≤ Module.finrank ℝ E := by
    by_contra hnot
    have hsucc : Module.finrank ℝ E + 1 ≤ (activeConstraints a x).card := by omega
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hsucc
    apply hno S hScard
    intro i hi
    have hiactive : i ∈ activeConstraints a x := hSsub hi
    simpa [activeConstraints] using hiactive
  omega

/-- Under the same nondegeneracy hypothesis, the entire active set is a
linearly independent full basis.  Thus a vertex has a canonical basis rather
than merely an existentially chosen one. -/
theorem activeNormals_linearIndependent_of_extremePoint
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (x : E)
    (hx : x ∈ (inequalityFeasible a).extremePoints ℝ)
    (hno : ∀ S : Finset ι, S.card = Module.finrank ℝ E + 1 →
      ¬ (∀ i ∈ S, ⟪a i, x⟫ = 1)) :
    LinearIndependent ℝ
      (fun i : {i // i ∈ activeConstraints a x} => a i) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · exact le_of_eq (activeNormals_span_eq_top_of_extremePoint a x hx).symm
  · simpa using activeConstraints_card_eq_finrank_of_extremePoint a x hx hno

#print axioms active_normal_mem_span
#print axioms activeNormals_span_eq_top_of_extremePoint
#print axioms exists_active_basis_indexing_of_extremePoint
#print axioms activeConstraints_card_eq_finrank_of_extremePoint
#print axioms activeNormals_linearIndependent_of_extremePoint

end SolveAll011.Tier3
