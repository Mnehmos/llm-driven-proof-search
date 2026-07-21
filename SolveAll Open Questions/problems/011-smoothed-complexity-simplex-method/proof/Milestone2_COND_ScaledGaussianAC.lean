/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone M2-COND-3b(a)-SCALED (Tier 1, A-COND): the perturbed-column law of the Gaussian
smoothed model is absolutely continuous w.r.t. Lebesgue, and avoids any fixed proper subspace a.s.

NOT the open conjecture; general/probabilistic measure theory IN THE EXACT PERTURBATION MODEL.
For any center `c`, nonzero `σ`, the law of a perturbed column `c + σ·G` (`G` standard Gaussian) —
i.e. `(stdGaussian).map (g ↦ c + σ • g)`, precisely the smoothed model's column `A_col = Ābar_col
+ σ·G` — is `≪ volume`. Corollary `scaled_gaussian_subspace_measure_zero`: it assigns measure 0
to any proper submodule `W ≠ ⊤`, via `Measure.addHaar_submodule`. This is the a.s.-nonsingularity
core the Rudelson–Vershynin σ_min argument needs: each Gaussian-perturbed column misses the fixed
span of the other columns a.s. (that span is proper since `n−1` vectors cannot span `ℝⁿ`), so
`det ≠ 0` a.s.

The proof AVOIDS the CFC machinery of `multivariateGaussian`: `stdGaussian ≪ volume` (this
campaign's `stdGaussian_absolutelyContinuous`, inlined, built on the finite-product a.c.
gap-filler); the scaling `g ↦ σ • g` is a measurable equivalence (`Homeomorph.smulOfNeZero`) under
which `volume` maps to a nonzero scalar multiple (`Measure.map_addHaar_smul`), so a.c. transports
(`absolutelyContinuous_map` + `Measure.smul_absolutelyContinuous`); the translation `y ↦ c + y`
preserves `volume` (`IsAddLeftInvariant.map_add_left_eq_self`), so a.c. transports again.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  scaled_gaussian_ac
    problem_version  7683b09b-47e4-46cc-9d03-eb7da0442d9f
    episode          4ec96081-0c19-476a-a078-f48e5148b540
    statement_hash   91f742e1bba1cb96a461b1cdf7b3b4691499a78b4a50ae8c3d742ab8e1f2dd62
    module_source_hash 6b165ce0fd09d9783a2a2c18075a601f8468d8a596e29649896287580a64cfc1
    declaration_manifest_hash 278159091161f67a49ba8d2609ca0b03a8937ca7ba7b5ca10cfa5aeb6a1856ea
    obligation_id    a140c9fc-bea8-4e4f-bf14-027a8a03742c
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` on both = [propext, Classical.choice, Quot.sound]. Reproduce: `lake env lean`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory WithLp

namespace SolveAll011.M2COND

/-- **The perturbed-column law `c + σ·(standard Gaussian)` is absolutely continuous w.r.t.
Lebesgue** — the exact column law of the Gaussian-smoothed model. -/
theorem scaled_gaussian_ac (n : ℕ) (c : EuclideanSpace ℝ (Fin n)) (σ : ℝ) (hσ : σ ≠ 0) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun g => c + σ • g)
      ≪ (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have piac : ∀ {k : ℕ} (μ ν : Fin k → Measure ℝ)
      [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
      (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν := by
    intro k
    induction k with
    | zero =>
      intro μ ν _ _ _
      haveI : Subsingleton (Fin 0 → ℝ) := inferInstance
      haveI : IsProbabilityMeasure (Measure.pi ν) := by
        constructor
        have h := Measure.pi_pi ν (fun _ => Set.univ)
        simpa using h
      intro s hs
      have hsub : s = ∅ := by
        rcases Set.eq_empty_or_nonempty s with h | ⟨x, hx⟩
        · exact h
        · exfalso
          have huniv : s = Set.univ :=
            Set.eq_univ_of_forall (fun y => by rw [Subsingleton.elim y x]; exact hx)
          rw [huniv, measure_univ] at hs
          exact one_ne_zero hs
      rw [hsub]; simp
    | succ k ih =>
      intro μ ν _ _ h
      let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (0 : Fin (k + 1))
      have hmpμ := measurePreserving_piFinSuccAbove μ (0 : Fin (k + 1))
      have hmpν := measurePreserving_piFinSuccAbove ν (0 : Fin (k + 1))
      have hrest := ih (fun j => μ ((0 : Fin (k + 1)).succAbove j))
        (fun j => ν ((0 : Fin (k + 1)).succAbove j)) (fun j => h _)
      have hprod := (h 0).prod hrest
      have hμeq : Measure.pi μ
          = ((μ 0).prod (Measure.pi (fun j => μ ((0 : Fin (k + 1)).succAbove j)))).map E.symm :=
        (MeasurePreserving.symm E hmpμ).map_eq.symm
      have hνeq : Measure.pi ν
          = ((ν 0).prod (Measure.pi (fun j => ν ((0 : Fin (k + 1)).succAbove j)))).map E.symm :=
        (MeasurePreserving.symm E hmpν).map_eq.symm
      rw [hμeq, hνeq]
      exact E.symm.measurableEmbedding.absolutelyContinuous_map hprod
  have hstd : stdGaussian (EuclideanSpace ℝ (Fin n)) ≪ volume := by
    have hpi : Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≪ (volume : Measure (Fin n → ℝ)) := by
      rw [volume_pi]
      exact piac _ _ (fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero)
    rw [← map_pi_eq_stdGaussian]
    have hac := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding.absolutelyContinuous_map hpi
    rw [MeasurableEquiv.coe_toLp] at hac
    have hmp := PiLp.volume_preserving_toLp (ι := Fin n)
    rw [hmp.map_eq] at hac
    exact hac
  have hsm : Measurable (fun g : EuclideanSpace ℝ (Fin n) => σ • g) := by fun_prop
  have htr : Measurable (fun y : EuclideanSpace ℝ (Fin n) => c + y) := by fun_prop
  have hsm_emb : MeasurableEmbedding (fun g : EuclideanSpace ℝ (Fin n) => σ • g) :=
    (Homeomorph.smulOfNeZero σ hσ).measurableEmbedding
  have htr_emb : MeasurableEmbedding (fun y : EuclideanSpace ℝ (Fin n) => c + y) :=
    (Homeomorph.addLeft c).measurableEmbedding
  have h1 : (stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun g => σ • g) ≪ volume := by
    have hh := hsm_emb.absolutelyContinuous_map hstd
    rw [Measure.map_addHaar_smul (volume : Measure (EuclideanSpace ℝ (Fin n))) hσ] at hh
    exact hh.trans Measure.smul_absolutelyContinuous
  have hcomp : (fun g : EuclideanSpace ℝ (Fin n) => c + σ • g)
      = (fun y => c + y) ∘ (fun g => σ • g) := rfl
  rw [hcomp, ← Measure.map_map htr hsm]
  have h2 := htr_emb.absolutelyContinuous_map h1
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin n))).map (fun y => c + y) = volume :=
    (inferInstance : (volume : Measure (EuclideanSpace ℝ (Fin n))).IsAddLeftInvariant).map_add_left_eq_self c
  rwa [hvol] at h2

/-- **a.s.-nonsingularity core, smoothed model.** A perturbed column `c + σ·(standard Gaussian)`
avoids any fixed proper subspace almost surely. -/
theorem scaled_gaussian_subspace_measure_zero (n : ℕ) (c : EuclideanSpace ℝ (Fin n)) (σ : ℝ)
    (hσ : σ ≠ 0) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hW : W ≠ ⊤) :
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).map (fun g => c + σ • g))
        (W : Set (EuclideanSpace ℝ (Fin n))) = 0 :=
  scaled_gaussian_ac n c σ hσ (Measure.addHaar_submodule volume W hW)

end SolveAll011.M2COND

#print axioms SolveAll011.M2COND.scaled_gaussian_ac
#print axioms SolveAll011.M2COND.scaled_gaussian_subspace_measure_zero
