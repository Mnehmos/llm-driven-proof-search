/-
SolveAll #11 — affine genericity and active-constraint cardinality.

This module supplies the deterministic bridge from nonvanishing augmented
constraint minors to the simple-polytope semantics used by simplex paths.  It
is independent of the probability proof that Gaussian perturbations satisfy
the genericity hypothesis almost surely.
-/
import Mathlib

namespace SolveAll011.Tier3

open scoped RealInnerProductSpace

/-- Affine general position: every `finrank(E)+1` augmented constraint vectors
`(aᵢ,bᵢ)` are linearly independent in `E × ℝ`. -/
def AffineGeneralPosition
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (b : ι → ℝ) : Prop :=
  ∀ S : Finset ι, S.card = Module.finrank ℝ E + 1 →
    LinearIndependent ℝ (fun i : {i // i ∈ S} => (a i, b i))

/-- No `dim+1` affinely generic constraints can all be active at one point.
Indeed their augmented vectors would span `E × ℝ` while all lying in the
proper hyperplane orthogonal to `(x,-1)`. -/
theorem no_finrank_succ_active_of_affineGeneralPosition
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (b : ι → ℝ) (x : E)
    (hgp : AffineGeneralPosition a b)
    (S : Finset ι) (hcard : S.card = Module.finrank ℝ E + 1)
    (hactive : ∀ i ∈ S, ⟪a i, x⟫ = b i) : False := by
  let f : {i // i ∈ S} → E × ℝ := fun i => (a i, b i)
  let L : E × ℝ →ₗ[ℝ] ℝ :=
    (innerSL ℝ x).toLinearMap.comp (LinearMap.fst ℝ E ℝ) - LinearMap.snd ℝ E ℝ
  have hli : LinearIndependent ℝ f := hgp S hcard
  have hdim : Fintype.card {i // i ∈ S} = Module.finrank ℝ (E × ℝ) := by
    rw [Fintype.card_coe, hcard, Module.finrank_prod]
    simp
  have hspan : Submodule.span ℝ (Set.range f) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' hdim
  have hrange : Set.range f ⊆ LinearMap.ker L := by
    rintro y ⟨i, rfl⟩
    change L (f i) = 0
    simp only [L, f, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    change ⟪x, a i⟫ - b i = 0
    rw [real_inner_comm, hactive i i.property]
    simp
  have hspanKer : Submodule.span ℝ (Set.range f) ≤ LinearMap.ker L :=
    Submodule.span_le.2 hrange
  have honeKer : ((0 : E), (1 : ℝ)) ∈ LinearMap.ker L := by
    apply hspanKer
    rw [hspan]
    exact Submodule.mem_top
  have hzero : L ((0 : E), (1 : ℝ)) = 0 := by
    simpa [LinearMap.mem_ker] using honeKer
  simp [L] at hzero

/-- Consequently every active set has at most `finrank(E)` constraints. -/
theorem active_card_le_finrank_of_affineGeneralPosition
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (b : ι → ℝ) (x : E)
    (hgp : AffineGeneralPosition a b)
    (S : Finset ι) (hactive : ∀ i ∈ S, ⟪a i, x⟫ = b i) :
    S.card ≤ Module.finrank ℝ E := by
  by_contra hnot
  have hsucc : Module.finrank ℝ E + 1 ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hsucc
  exact no_finrank_succ_active_of_affineGeneralPosition a b x hgp T hTcard
    (fun i hi => hactive i (hTS hi))

/-- If a vertex comes equipped with a full-dimensional active basis, affine
general position makes that basis the entire active set. -/
theorem active_set_eq_basis_of_affineGeneralPosition
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E) (b : ι → ℝ) (x : E)
    (hgp : AffineGeneralPosition a b)
    (active basis : Finset ι)
    (hbasis : basis ⊆ active)
    (hactive : ∀ i ∈ active, ⟪a i, x⟫ = b i)
    (hbasisCard : basis.card = Module.finrank ℝ E) :
    active = basis := by
  apply Finset.Subset.antisymm ?_ hbasis
  have hle := active_card_le_finrank_of_affineGeneralPosition a b x hgp active hactive
  rw [← hbasisCard] at hle
  exact Finset.eq_of_subset_of_card_le hbasis hle |>.symm.subset

/-- Positive row normalization preserves affine general position: scaling
`(Aᵢ,bᵢ)` by `bᵢ⁻¹` produces `(bᵢ⁻¹Aᵢ,1)`. -/
theorem affineGeneralPosition_normalized
    {ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A : ι → E) (b : ι → ℝ) (hb : ∀ i, b i ≠ 0)
    (hgp : AffineGeneralPosition A b) :
    AffineGeneralPosition (fun i => (b i)⁻¹ • A i) (fun _ => 1) := by
  intro S hcard
  have hli := hgp S hcard
  let u : {i // i ∈ S} → ℝˣ := fun i =>
    Units.mk0 (b i)⁻¹ (inv_ne_zero (hb i))
  have hscaled := hli.units_smul u
  convert hscaled using 1
  funext i
  apply Prod.ext
  · simp [u]
  · simp [u, hb i]

#print axioms AffineGeneralPosition
#print axioms no_finrank_succ_active_of_affineGeneralPosition
#print axioms active_card_le_finrank_of_affineGeneralPosition
#print axioms active_set_eq_basis_of_affineGeneralPosition
#print axioms affineGeneralPosition_normalized

end SolveAll011.Tier3
