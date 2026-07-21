/-
SolveAll #11 — probability induction for affine general position.

An absolutely continuous random vector avoids the span of any fixed family of
fewer than `dim` vectors.  Consequently adjoining such a vector to an almost
surely linearly independent family preserves linear independence almost surely.
This is the measure-theoretic induction step needed for Gaussian affine
genericity of every fixed augmented constraint subset.
-/
import Mathlib

namespace SolveAll011.Tier3

open MeasureTheory

/-- An absolutely continuous law assigns measure zero to the span of a family
whose cardinality is below the ambient dimension. -/
theorem absolutelyContinuous_span_range_measure_zero
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (νref μ : Measure E)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hμ : μ ≪ νref) (v : ι → E)
    (hcard : Fintype.card ι < Module.finrank ℝ E) :
    μ (Submodule.span ℝ (Set.range v) : Set E) = 0 := by
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hW : W ≠ ⊤ := by
    intro htop
    have hdim : Module.finrank ℝ E ≤ Fintype.card ι :=
      finrank_le_of_span_eq_top (v := v) htop
    omega
  exact hμ (hnull W hW)

/-- Product-measure induction step: if `v : Fin n → E` is linearly independent
almost surely under `Q`, and `x : E` has an absolutely continuous law `P`, then
`Fin.snoc v x` is linearly independent almost surely, provided `n < dim E`. -/
theorem ae_linearIndependent_finSnoc_of_absolutelyContinuous
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (Q : Measure (Fin n → E)) (νref P : Measure E)
    [SFinite Q] [SFinite P]
    (hQ : ∀ᵐ v ∂Q, LinearIndependent ℝ v)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hP : P ≪ νref) (hdim : n < Module.finrank ℝ E) :
    ∀ᵐ p ∂Q.prod P, LinearIndependent ℝ (Fin.snoc p.1 p.2) := by
  have hmeas : MeasurableSet
      {p : (Fin n → E) × E | LinearIndependent ℝ (Fin.snoc p.1 p.2)} := by
    apply isOpen_setOf_linearIndependent.measurableSet.preimage
    fun_prop
  rw [Measure.ae_prod_iff_ae_ae hmeas]
  filter_upwards [hQ] with v hv
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hPW : P (W : Set E) = 0 :=
    absolutelyContinuous_span_range_measure_zero νref P hnull hP v (by simpa using hdim)
  have hae : ∀ᵐ x ∂P, x ∉ W := by
    rw [ae_iff]
    simpa using hPW
  filter_upwards [hae] with x hx
  exact hv.finSnoc hx

/-- Pushforward form of the induction step, on the natural `Fin (n+1) → E`
family space. -/
theorem ae_linearIndependent_finSnoc_map_of_absolutelyContinuous
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (Q : Measure (Fin n → E)) (νref P : Measure E)
    [SFinite Q] [SFinite P]
    (hQ : ∀ᵐ v ∂Q, LinearIndependent ℝ v)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hP : P ≪ νref) (hdim : n < Module.finrank ℝ E) :
    ∀ᵐ v ∂(Q.prod P).map (fun p => Fin.snoc p.1 p.2),
      LinearIndependent ℝ v := by
  rw [ae_map_iff (by fun_prop) isOpen_setOf_linearIndependent.measurableSet]
  exact ae_linearIndependent_finSnoc_of_absolutelyContinuous n Q νref P
    hQ hnull hP hdim

/-- Iterated independent product, represented recursively by adjoining the
next coordinate at the end of a `Fin n` family. -/
noncomputable def finSnocProductMeasure
    {E : Type} [MeasurableSpace E] (P : ℕ → Measure E) :
    (n : ℕ) → Measure (Fin n → E)
  | 0 => Measure.dirac (fun i : Fin 0 => Fin.elim0 i)
  | n + 1 => ((finSnocProductMeasure P n).prod (P n)).map
      (fun p => Fin.snoc p.1 p.2)

instance finSnocProductMeasure_sfinite
    {E : Type} [MeasurableSpace E]
    (P : ℕ → Measure E) [∀ i, SFinite (P i)] (n : ℕ) :
    SFinite (finSnocProductMeasure P n) := by
  induction n with
  | zero => simp [finSnocProductMeasure]; infer_instance
  | succ n ih =>
      rw [finSnocProductMeasure]
      infer_instance

/-- Base case for the product induction: the empty vector family is linearly
independent everywhere. -/
theorem ae_linearIndependent_fin_zero
    {E : Type} [MeasurableSpace E] [AddCommMonoid E] [Module ℝ E]
    (Q : Measure (Fin 0 → E)) :
    ∀ᵐ v ∂Q, LinearIndependent ℝ v := by
  filter_upwards [] with v
  exact linearIndependent_empty_type

/-- Iterating the snoc step: independent absolutely-continuous vectors are
linearly independent almost surely up to the ambient dimension. -/
theorem ae_linearIndependent_finSnocProductMeasure
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℕ → Measure E) [∀ i, SFinite (P i)]
    (νref : Measure E)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hP : ∀ i, P i ≪ νref) (n : ℕ) (hdim : n ≤ Module.finrank ℝ E) :
    ∀ᵐ v ∂finSnocProductMeasure P n, LinearIndependent ℝ v := by
  induction n with
  | zero => exact ae_linearIndependent_fin_zero _
  | succ n ih =>
      rw [finSnocProductMeasure]
      apply ae_linearIndependent_finSnoc_map_of_absolutelyContinuous n
        (finSnocProductMeasure P n) νref (P n)
      · exact ih (Nat.le_trans (Nat.le_succ n) hdim)
      · exact hnull
      · exact hP n
      · omega

/-- Euclidean-volume specialization.  This is the form used for Gaussian
augmented constraint rows: absolute continuity with respect to Lebesgue volume
is the only distributional input. -/
theorem ae_linearIndependent_finSnocProductMeasure_volume
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℕ → Measure E) [∀ i, SFinite (P i)]
    (hP : ∀ i, P i ≪ (volume : Measure E))
    (n : ℕ) (hdim : n ≤ Module.finrank ℝ E) :
    ∀ᵐ v ∂finSnocProductMeasure P n, LinearIndependent ℝ v := by
  exact ae_linearIndependent_finSnocProductMeasure P (volume : Measure E)
    (fun W hW => Measure.addHaar_submodule (volume : Measure E) W hW) hP n hdim

/-- A finite intersection packages fixed-subset almost-sure genericity into
simultaneous genericity of every subset of the prescribed cardinality. -/
theorem ae_every_fixed_card_family_linearIndependent
    {Ω ι E : Type} [MeasurableSpace Ω] [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (X : Ω → ι → E) (k : ℕ)
    (hfixed : ∀ S : Finset ι, S.card = k →
      ∀ᵐ ω ∂μ, LinearIndependent ℝ (fun i : S => X ω i)) :
    ∀ᵐ ω ∂μ, ∀ S : Finset ι, S.card = k →
      LinearIndependent ℝ (fun i : S => X ω i) := by
  apply ae_all_iff.2
  intro S
  by_cases hS : S.card = k
  · filter_upwards [hfixed S hS] with ω hω
    exact fun _ => hω
  · exact Filter.Eventually.of_forall (fun _ h => (hS h).elim)

/-- Product-measure prepend step.  This is the coordinate order used by
`Measure.pi` when it is split at coordinate `0`. -/
theorem ae_linearIndependent_finCons_of_absolutelyContinuous
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (Q : Measure (Fin n → E)) (νref P : Measure E)
    [SFinite Q] [SFinite P]
    (hQ : ∀ᵐ v ∂Q, LinearIndependent ℝ v)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hP : P ≪ νref) (hdim : n < Module.finrank ℝ E) :
    ∀ᵐ p ∂P.prod Q, LinearIndependent ℝ (Fin.cons p.1 p.2) := by
  have hmeas : MeasurableSet
      {p : E × (Fin n → E) | LinearIndependent ℝ (Fin.cons p.1 p.2)} := by
    apply isOpen_setOf_linearIndependent.measurableSet.preimage
    fun_prop
  rw [Measure.ae_prod_iff_ae_ae hmeas]
  rw [Measure.ae_ae_comm hmeas]
  filter_upwards [hQ] with v hv
  let W : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hPW : P (W : Set E) = 0 :=
    absolutelyContinuous_span_range_measure_zero νref P hnull hP v (by simpa using hdim)
  have hae : ∀ᵐ x ∂P, x ∉ W := by
    rw [ae_iff]
    simpa using hPW
  filter_upwards [hae] with x hx
  exact hv.finCons hx

/-- The genuine finite independent product law has an a.s. linearly independent
coordinate family whenever its size does not exceed the ambient dimension. -/
theorem ae_linearIndependent_piFin_of_absolutelyContinuous
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (νref : Measure E)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0) :
    ∀ (n : ℕ) (P : Fin n → Measure E) [∀ i, SigmaFinite (P i)],
      (∀ i, P i ≪ νref) → n ≤ Module.finrank ℝ E →
      ∀ᵐ v ∂Measure.pi P, LinearIndependent ℝ v := by
  intro n
  induction n with
  | zero =>
      intro P hPsf hP hdim
      letI : ∀ i, SigmaFinite (P i) := hPsf
      exact ae_linearIndependent_fin_zero _
  | succ n ih =>
      intro P hPsf hP hdim
      letI : ∀ j, SigmaFinite (P j) := hPsf
      let i : Fin (n + 1) := 0
      let Q : Measure (Fin n → E) := Measure.pi (fun j => P (i.succAbove j))
      have hQ : ∀ᵐ v ∂Q, LinearIndependent ℝ v := by
        apply ih (fun j => P (i.succAbove j))
        · exact fun j => hP (i.succAbove j)
        · omega
      have hprod : ∀ᵐ p ∂(P i).prod Q,
          LinearIndependent ℝ (Fin.cons p.1 p.2) := by
        apply ae_linearIndependent_finCons_of_absolutelyContinuous n Q νref (P i)
        · exact hQ
        · exact hnull
        · exact hP i
        · omega
      have hmp := measurePreserving_piFinSuccAbove P i
      have hpull := hmp.quasiMeasurePreserving.ae hprod
      filter_upwards [hpull] with v hv
      simpa [i, Q] using hv

/-- Reindex the `Fin n` result to an arbitrary finite coordinate type. -/
theorem ae_linearIndependent_pi_of_absolutelyContinuous
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ι → Measure E) [∀ i, SigmaFinite (P i)]
    (νref : Measure E)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hP : ∀ i, P i ≪ νref)
    (hdim : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∀ᵐ v ∂Measure.pi P, LinearIndependent ℝ v := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Q : Fin (Fintype.card ι) → Measure E := fun j => P (e j)
  have hfin : ∀ᵐ v ∂Measure.pi Q, LinearIndependent ℝ v := by
    exact ae_linearIndependent_piFin_of_absolutelyContinuous νref hnull
      (Fintype.card ι) Q (fun j => hP (e j)) hdim
  have hmp := measurePreserving_piCongrLeft P e
  rw [← hmp.map_eq, ae_map_iff hmp.aemeasurable
    isOpen_setOf_linearIndependent.measurableSet]
  filter_upwards [hfin] with v hv
  apply (linearIndependent_equiv e).mp
  have heq : ((MeasurableEquiv.piCongrLeft (fun _ : ι => E) e) v) ∘ e = v := by
    funext j
    exact Equiv.piCongrLeft_apply_apply (P := fun _ : ι => E) e v j
  rw [heq]
  exact hv

/-- Projectivity of finite product measures: under one joint independent
sample, the coordinates in any fixed subset are linearly independent almost
surely whenever the selected row laws are absolutely continuous. -/
theorem ae_linearIndependent_restrict_finset_pi
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (νref : Measure E)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hP : ∀ i, P i ≪ νref)
    (I J : Finset ι) (hJI : J ⊆ I)
    (hdim : J.card ≤ Module.finrank ℝ E) :
    ∀ᵐ v ∂Measure.pi (fun i : I => P i),
      LinearIndependent ℝ (fun j : J => v ⟨j, hJI j.property⟩) := by
  have hJ : ∀ᵐ v ∂Measure.pi (fun j : J => P j),
      LinearIndependent ℝ v := by
    apply ae_linearIndependent_pi_of_absolutelyContinuous
      (fun j : J => P j) νref hnull
    · exact fun j => hP j
    · simpa using hdim
  have hproj := isProjectiveMeasureFamily_pi P I J hJI
  change Measure.pi (fun j : J => P j) =
    (Measure.pi (fun i : I => P i)).map
      (Finset.restrict₂ (π := fun _ => E) hJI) at hproj
  have hmp : MeasurePreserving
      (Finset.restrict₂ (π := fun _ => E) hJI)
      (Measure.pi (fun i : I => P i))
      (Measure.pi (fun j : J => P j)) :=
    ⟨Finset.measurable_restrict₂ hJI, hproj.symm⟩
  exact hmp.quasiMeasurePreserving.ae hJ

/-- Finite intersection of the projective marginal result: one joint product
sample is simultaneously in linear general position on every selected subset
whose size is at most the ambient dimension. -/
theorem ae_every_restrict_finset_linearIndependent_pi
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (νref : Measure E)
    (hnull : ∀ W : Submodule ℝ E, W ≠ ⊤ → νref (W : Set E) = 0)
    (hP : ∀ i, P i ≪ νref) (I : Finset ι) :
    ∀ᵐ v ∂Measure.pi (fun i : I => P i),
      ∀ J : Finset ι, ∀ hJI : J ⊆ I,
        J.card ≤ Module.finrank ℝ E →
        LinearIndependent ℝ (fun j : J => v ⟨j, hJI j.property⟩) := by
  apply ae_all_iff.2
  intro J
  by_cases hJI : J ⊆ I
  · by_cases hdim : J.card ≤ Module.finrank ℝ E
    · filter_upwards [ae_linearIndependent_restrict_finset_pi
        P νref hnull hP I J hJI hdim] with v hv
      intro hJI' _
      simpa using hv
    · exact Filter.Eventually.of_forall (fun _ _ h => (hdim h).elim)
  · exact Filter.Eventually.of_forall (fun _ h => (hJI h).elim)

/-- Euclidean-volume interface for the exact joint product theorem.  Translated
nondegenerate Gaussian row laws satisfy precisely the displayed absolute-
continuity premise. -/
theorem ae_every_restrict_finset_linearIndependent_pi_volume
    {ι E : Type} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ι → Measure E) [∀ i, IsProbabilityMeasure (P i)]
    (hP : ∀ i, P i ≪ (volume : Measure E)) (I : Finset ι) :
    ∀ᵐ v ∂Measure.pi (fun i : I => P i),
      ∀ J : Finset ι, ∀ hJI : J ⊆ I,
        J.card ≤ Module.finrank ℝ E →
        LinearIndependent ℝ (fun j : J => v ⟨j, hJI j.property⟩) := by
  exact ae_every_restrict_finset_linearIndependent_pi P volume
    (fun W hW => Measure.addHaar_submodule (volume : Measure E) W hW) hP I

#print axioms absolutelyContinuous_span_range_measure_zero
#print axioms ae_linearIndependent_finSnoc_of_absolutelyContinuous
#print axioms ae_linearIndependent_fin_zero
#print axioms ae_linearIndependent_finSnoc_map_of_absolutelyContinuous
#print axioms ae_linearIndependent_finSnocProductMeasure
#print axioms ae_linearIndependent_finSnocProductMeasure_volume
#print axioms ae_every_fixed_card_family_linearIndependent
#print axioms ae_linearIndependent_finCons_of_absolutelyContinuous
#print axioms ae_linearIndependent_piFin_of_absolutelyContinuous
#print axioms ae_linearIndependent_pi_of_absolutelyContinuous
#print axioms ae_linearIndependent_restrict_finset_pi
#print axioms ae_every_restrict_finset_linearIndependent_pi
#print axioms ae_every_restrict_finset_linearIndependent_pi_volume

end SolveAll011.Tier3
