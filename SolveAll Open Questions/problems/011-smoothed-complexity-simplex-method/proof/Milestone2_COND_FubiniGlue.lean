/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-COND (step 3c) (Tier 1, architecture A-COND): the Fubini conditioning glue for the
σ_min lower-tail.

NOT the open conjecture. This is the measure-theoretic step that turns a per-slice conditional
bound into a bound on a product measure: if for every value `y` of the conditioning coordinate
the conditional slice `{x | (y,x) ∈ S}` has `P`-measure `≤ c`, then `S` has `(Q.prod P)`-measure
`≤ c` (with `Q` a probability measure). Applied with `y` = the other columns of the Gaussian
matrix, `x` = column `i`, `S = {dist(column i, span(other columns)) ≤ ε}`, and `c = 2ε/(σ√2π)`
(the M2-CONDc conditional bound), this promotes the conditional inequality to the JOINT
matrix-Gaussian probability, using the column-independence product structure (M2-COND3a).

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  M2-COND-3c  prod_measure_le_of_slice_le
              problem_version  7cf633b2-2757-4f10-ab1d-ee4953c3ebb0
              episode          3a68c3c7-c2c1-49a0-a55f-f9f594059fd4
              statement_hash   14052aff1d4cf64aca08beac994dc8b53cdb37bc9bf5344222d1221ff5050acc
              module_source_hash c825c05f34cf840342be550b76f70885e99cf4d97c2e60aba00a51aae58cf897
              declaration_manifest_hash 6026c80371dc0bc67373adaa48b2525703d21e5b0e680a541be1df5167cf03ff
              obligation_id    5e64704f-329d-4c1e-a7bb-129e7a43c6f4
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa
  (tracked manifest carries `open MeasureTheory`; this snapshot opens it at file level)

`#print axioms` = [propext, Classical.choice, Quot.sound].
Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

open MeasureTheory

namespace SolveAll011.M2CONDfubini

/-- **M2-COND step 3c — Fubini conditioning glue.** If every conditional slice
`{x | (y,x) ∈ S}` has `P`-measure `≤ c`, then `(Q.prod P) S ≤ c` for a probability measure `Q`.
The measure-theoretic step promoting the per-ω conditional bound to the joint matrix-Gaussian
probability. -/
theorem prod_measure_le_of_slice_le
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (Q : Measure Ω) (P : Measure Ω') [IsProbabilityMeasure Q] [SFinite P]
    (S : Set (Ω × Ω')) (hS : MeasurableSet S) (c : ENNReal)
    (hslice : ∀ y, P (Prod.mk y ⁻¹' S) ≤ c) :
    (Q.prod P) S ≤ c := by
  rw [Measure.prod_apply hS]
  calc ∫⁻ y, P (Prod.mk y ⁻¹' S) ∂Q
      ≤ ∫⁻ _y, c ∂Q := lintegral_mono (fun y => hslice y)
    _ = c * Q Set.univ := lintegral_const c
    _ = c := by rw [measure_univ, mul_one]

end SolveAll011.M2CONDfubini

#print axioms SolveAll011.M2CONDfubini.prod_measure_le_of_slice_le
