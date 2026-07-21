/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-COND (step 3a) (Tier 1, architecture A-COND): the matrix Gaussian as a product
measure over columns, with independent columns.

NOT the open conjecture. The `m×n` Gaussian-perturbed matrix is modeled as
`Measure.pi (fun j => multivariateGaussian (center j) (σ²I_m))` on `Fin n → ℝ^m` — the `n`
columns are i.i.d.-structured isotropic Gaussians `N(center j, σ²I_m)`, matching `A = Ā + G`
with `G` entrywise `N(0,σ²)`. This file proves the columns are jointly INDEPENDENT and each has
its intended multivariate-Gaussian marginal — the product structure the σ_min conditioning step
(M2-COND) needs: conditioning on the other columns leaves column `i` with its own Gaussian law,
so the fixed-subspace bound `gaussian_dist_subspace_le` (M2-CONDc, ep b15cd230) applies with
`W = span of the other columns`.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  M2-COND-3a  matrix_gaussian_columns_iIndepFun
              problem_version  88cc675f-272b-4498-90af-9e428d8072ce
              episode          a95d1c04-1679-47ab-a799-671424348482
              statement_hash   04c6e1447e5ea23c8c4f81e0240bcfa4b6301974a45d4b64f18fe1d4df4dae5f
              module_source_hash 7e9f739f96807c453943c195a1d67e0729aae0c46bf6fbcdf9f2bc662621d0e7
              declaration_manifest_hash f08831a2d6bc74d1076f8d7ab25ff15f9eea24bf44fae85e4b56dc0ed52e2107
              obligation_id    537fda0d-28f7-4566-b7cb-baef6af69073
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` on both = [propext, Classical.choice, Quot.sound].
Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2CONDprod

/-- **M2-COND step 3a — matrix-Gaussian columns are independent.** Under the product measure
over the `n` columns (each `N(center j, σ²I_m)`), the column-evaluation maps `ω ↦ ω j` are
jointly independent (`iIndepFun_pi`). -/
theorem matrix_gaussian_columns_iIndepFun (m n : ℕ)
    (center : Fin n → EuclideanSpace ℝ (Fin m)) (σ : ℝ) :
    ProbabilityTheory.iIndepFun
      (fun (j : Fin n) (ω : Fin n → EuclideanSpace ℝ (Fin m)) => ω j)
      (MeasureTheory.Measure.pi
        (fun k : Fin n => ProbabilityTheory.multivariateGaussian (center k)
          (σ ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)))) := by
  exact ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- Each column marginal is the intended multivariate Gaussian (product-measure evaluation). -/
theorem matrix_gaussian_column_law (m n : ℕ)
    (center : Fin n → EuclideanSpace ℝ (Fin m)) (σ : ℝ) (j : Fin n) :
    (MeasureTheory.Measure.pi
        (fun k : Fin n => ProbabilityTheory.multivariateGaussian (center k)
          (σ ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)))).map (fun ω => ω j)
      = ProbabilityTheory.multivariateGaussian (center j) (σ ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  exact (MeasureTheory.measurePreserving_eval _ j).map_eq

end SolveAll011.M2CONDprod

#print axioms SolveAll011.M2CONDprod.matrix_gaussian_columns_iIndepFun
#print axioms SolveAll011.M2CONDprod.matrix_gaussian_column_law
