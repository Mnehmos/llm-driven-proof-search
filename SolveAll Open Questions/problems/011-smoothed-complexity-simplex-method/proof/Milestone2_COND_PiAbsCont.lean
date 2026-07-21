/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone M2-COND-3b(a)-AC (Tier 1, A-COND): finite-product absolute continuity — a gap-filler
for the pinned Mathlib, and the key building block for multivariate-Gaussian absolute continuity.

NOT the open conjecture; general measure theory. If each factor `μ i ≪ ν i` (all σ-finite), the
finite product `Measure.pi μ ≪ Measure.pi ν`. Proof by induction on `n` via the `piFinSuccAbove`
measurable equivalence (`Measure.pi` over `Fin (n+1)` ≅ `(μ 0).prod (Measure.pi of the rest)`),
combining the head a.c. with the tail a.c. (induction hypothesis) through `AbsolutelyContinuous.prod`
and transporting back through the measurable-embedding equivalence (`absolutelyContinuous_map`).

Role in the σ_min lower-tail: with `gaussianReal_absolutelyContinuous` (each coordinate a.c.) and
`volume_pi` (`Measure.pi volume = volume` on `Fin n → ℝ`), this gives
`Measure.pi (gaussianReal …) ≪ volume`; pushing forward through the affine isometry defining
`stdGaussian`/`multivariateGaussian` yields `multivariateGaussian ≪ volume`, which with
`addHaar_submodule` (a proper submodule is Lebesgue-null) closes `det ≠ 0` a.s. — the single
remaining obstruction of the A-COND route.

Missing-Mathlib finding: the pinned Mathlib has the BINARY `AbsolutelyContinuous.prod` but NO
finite-product / `Measure.pi` absolute-continuity lemma (confirmed by exhaustive search); this
fills that gap and is reusable well beyond this campaign.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  pi_absolutelyContinuous
    problem_version  417c70aa-fa41-4b76-b3c9-7cf1c7248e69
    episode          5f8f7d06-c07e-48ae-8e45-7ee7a7ee1b41
    statement_hash   98902641cf9c38cdf0756373f28f27e07e2296dfc8003d2652e82736b12160bb
    module_source_hash 25e8e79b10502f4176f644657dce601ea9599717d94832a3cd5add92b99b8aa7
    declaration_manifest_hash e510fe3debecdfc0dc6300452044067c416830b51d16bf23ab4d8c852af94a76
    obligation_id    520ebb00-2890-4e9d-975d-1a4cbd3e2b6e
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` = [propext, Classical.choice, Quot.sound]. Reproduce: `lake env lean` this file.
-/
import Mathlib

open MeasureTheory

namespace SolveAll011.M2COND

/-- **Finite-product absolute continuity.** If each factor `μ i ≪ ν i` (all σ-finite), then the
finite product measure `Measure.pi μ ≪ Measure.pi ν`. -/
theorem pi_absolutelyContinuous : ∀ {n : ℕ} (μ ν : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)],
    (∀ i, μ i ≪ ν i) → Measure.pi μ ≪ Measure.pi ν := by
  intro n
  induction n with
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
  | succ n ih =>
    intro μ ν _ _ h
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))
    have hmpμ := measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
    have hmpν := measurePreserving_piFinSuccAbove ν (0 : Fin (n + 1))
    have hrest := ih (fun j => μ ((0 : Fin (n + 1)).succAbove j))
      (fun j => ν ((0 : Fin (n + 1)).succAbove j)) (fun j => h _)
    have hprod := (h 0).prod hrest
    have hμeq : Measure.pi μ
        = ((μ 0).prod (Measure.pi (fun j => μ ((0 : Fin (n + 1)).succAbove j)))).map E.symm :=
      (MeasurePreserving.symm E hmpμ).map_eq.symm
    have hνeq : Measure.pi ν
        = ((ν 0).prod (Measure.pi (fun j => ν ((0 : Fin (n + 1)).succAbove j)))).map E.symm :=
      (MeasurePreserving.symm E hmpν).map_eq.symm
    rw [hμeq, hνeq]
    exact E.symm.measurableEmbedding.absolutelyContinuous_map hprod

/-- **Multivariate independent-coordinate Gaussian is absolutely continuous w.r.t. Lebesgue.**
The product of nondegenerate 1-D Gaussians on `Fin n → ℝ` is `≪ volume`. Immediate from
`pi_absolutelyContinuous` + `gaussianReal_absolutelyContinuous` (per-coordinate) + `volume_pi`.
This is step (1) of the short chain closing `det ≠ 0` almost surely. (Tracked: problem
`3c4db4e8-9ca6-47fa-9526-97f6371fdf26`, episode `b9683c13-3468-4618-b8a7-65c9648ae22b`,
statement_hash `9d61c490…`; the tracked root inlines `pi_absolutelyContinuous`.) -/
theorem gaussian_pi_absolutelyContinuous {n : ℕ} (m : Fin n → ℝ) (v : Fin n → NNReal)
    (hv : ∀ i, v i ≠ 0) :
    Measure.pi (fun i => ProbabilityTheory.gaussianReal (m i) (v i))
      ≪ (volume : Measure (Fin n → ℝ)) := by
  rw [volume_pi]
  exact pi_absolutelyContinuous _ _
    (fun i => ProbabilityTheory.gaussianReal_absolutelyContinuous (m i) (hv i))

end SolveAll011.M2COND

#print axioms SolveAll011.M2COND.pi_absolutelyContinuous
#print axioms SolveAll011.M2COND.gaussian_pi_absolutelyContinuous
