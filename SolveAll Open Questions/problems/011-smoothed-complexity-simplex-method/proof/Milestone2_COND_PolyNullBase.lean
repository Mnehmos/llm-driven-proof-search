/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone M2-COND-3b(a)-base (Tier 1, A-COND): base case of the "det ≠ 0 almost surely"
obstruction — a nonzero univariate real polynomial has a Lebesgue-null zero set.

NOT the open conjecture; pure measure theory. Role: the single remaining obstruction of the
A-COND route to the σ_min lower-tail (per state.md) is `det A ≠ 0` a.s. under the matrix
Gaussian — i.e. the singular locus `{A | det A = 0}`, the zero set of the polynomial `det`
(not identically zero, `det I = 1`), is Gaussian-null. Since the Gaussian is absolutely
continuous w.r.t. Lebesgue, this reduces to: the zero set of a nonzero `N`-variable polynomial
is Lebesgue-null. That multivariate statement is proved by induction on `N`; THIS is the `N = 1`
base case. The inductive step views `p ∈ MvPolynomial (Fin (N+1))` as a nonzero polynomial in
the last variable over `ℝ[X₁..X_N]`, applies the IH to a nonzero coefficient (co-null base),
notes each fibre is a nonzero 1-variable polynomial with finitely many roots (this base case),
and integrates via Fubini/Tonelli on `Measure.pi`.

Missing-Mathlib findings (this cycle): the pinned Mathlib has NO polynomial/analytic zero-set
measure-zero lemma and NO multivariate Gaussian absolute-continuity lemma (only the 1-D
`gaussianReal_absolutelyContinuous`). The complementary subspace-null tool
`addHaar_submodule` (a proper submodule of a finite-dim space has Haar/Lebesgue measure 0)
IS present.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  poly_root_set_measure_zero
    problem_version  8cf700f9-fd4f-4187-8438-740d27b3e543
    episode          1dbbeac4-2198-430e-9b0c-7ec5347d687a
    statement_hash   678dc1db8f289a91b92ef12e0ea6209669721b15105e3f05e788b6dcbe49b294
    module_source_hash 6fed5c8f4b5cd352b81425bf70c0c4b14804fa556da2fb0f66111593bbda2b52
    declaration_manifest_hash c39d435b3361970292a60c3c3169fd1b5f19c60637d534d6483a3d6e1cc9ecd3
    obligation_id    90e792ab-3ff8-4014-9008-3354a4cd9a0b
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` = [propext, Classical.choice, Quot.sound]. Reproduce: `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2COND

open MeasureTheory

/-- **Base case of the det-null theorem.** A nonzero univariate real polynomial vanishes on a
Lebesgue-null set: `volume {x | p.eval x = 0} = 0`. Its zero set is contained in the finite
root multiset `p.roots.toFinset`, hence finite, hence null (`volume` has no atoms). -/
theorem poly_root_set_measure_zero (p : Polynomial ℝ) (hp : p ≠ 0) :
    volume {x : ℝ | Polynomial.eval x p = 0} = 0 := by
  have hsub : {x : ℝ | Polynomial.eval x p = 0} ⊆ (↑p.roots.toFinset : Set ℝ) := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hp, hx⟩
  have hfin : {x : ℝ | Polynomial.eval x p = 0}.Finite :=
    Set.Finite.subset (p.roots.toFinset.finite_toSet) hsub
  exact hfin.measure_zero volume

end SolveAll011.M2COND

#print axioms SolveAll011.M2COND.poly_root_set_measure_zero
