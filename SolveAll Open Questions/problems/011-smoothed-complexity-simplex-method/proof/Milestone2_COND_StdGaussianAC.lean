/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone M2-COND-3b(a)-STD (Tier 1, A-COND): the standard Gaussian on Euclidean space is
absolutely continuous w.r.t. Lebesgue, and (corollary) avoids any fixed proper subspace a.s.

NOT the open conjecture; general/probabilistic measure theory. A fundamental Gaussian a.c. fact
absent from the pinned Mathlib. Proof: `stdGaussian = (Measure.pi (gaussianReal 0 1)).map (toLp 2)`
(`map_pi_eq_stdGaussian`); the pi-Gaussian is `≪ volume` on `Fin n → ℝ` (this campaign's
finite-product a.c. gap-filler `pi_absolutelyContinuous` + `gaussianReal_absolutelyContinuous`,
inlined); the equivalence `toLp 2` is volume-preserving (`PiLp.volume_preserving_toLp`), so a.c.
transports (`MeasurableEmbedding.absolutelyContinuous_map`).

Corollary `stdGaussian_subspace_measure_zero`: `stdGaussian W = 0` for any proper submodule
`W ≠ ⊤`, via `Measure.addHaar_submodule` (proper submodule ⇒ Lebesgue-null). This is the
a.s.-nonsingularity core: a nondegenerate Gaussian vector misses any fixed lower-dimensional
subspace a.s. — exactly what the Rudelson–Vershynin σ_min argument uses on each perturbed column
against the fixed span of the others. The general `multivariateGaussian center (σ²•1)` case
adds only the affine σ-scaling + translation transport (`map_linearMap_addHaar_eq_smul_addHaar`,
`det = σⁿ ≠ 0`).

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  stdGaussian_absolutelyContinuous
    problem_version  479268e8-ab0a-48c0-b3f2-50e46f7cded3
    episode          6459515f-1c47-40b5-823a-f4be393e8110
    statement_hash   c1b64ee96569b182af2faddd7eac107bc939e98876220b3ee1fc5ae220e4b2f7
    module_source_hash 4b98333cb1f7368eebc015bbe822bebccb1e4adaa2bf5cf902acb2a6fb807ee8
    declaration_manifest_hash 3cbf5f256b005834b842457941b8c61aa5b38a39b956ad6abe501111eb441992
    obligation_id    3f9bf528-b91d-445d-aa86-8e0060747f28
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` on both = [propext, Classical.choice, Quot.sound]. Reproduce: `lake env lean`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory WithLp

namespace SolveAll011.M2COND

/-- **The standard Gaussian on Euclidean space is absolutely continuous w.r.t. Lebesgue.** -/
theorem stdGaussian_absolutelyContinuous (n : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n))
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
  have hpi : Measure.pi (fun _ : Fin n => gaussianReal 0 1) ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [volume_pi]
    exact piac _ _ (fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero)
  rw [← map_pi_eq_stdGaussian]
  have hac := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding.absolutelyContinuous_map hpi
  rw [MeasurableEquiv.coe_toLp] at hac
  have hmp := PiLp.volume_preserving_toLp (ι := Fin n)
  rw [hmp.map_eq] at hac
  exact hac

/-- **a.s.-nonsingularity core.** A standard Gaussian vector avoids any fixed proper subspace
almost surely: `stdGaussian W = 0` for any proper submodule `W ≠ ⊤`. -/
theorem stdGaussian_subspace_measure_zero (n : ℕ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hW : W ≠ ⊤) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) (W : Set (EuclideanSpace ℝ (Fin n))) = 0 :=
  stdGaussian_absolutelyContinuous n (Measure.addHaar_submodule volume W hW)

end SolveAll011.M2COND

#print axioms SolveAll011.M2COND.stdGaussian_absolutelyContinuous
#print axioms SolveAll011.M2COND.stdGaussian_subspace_measure_zero
