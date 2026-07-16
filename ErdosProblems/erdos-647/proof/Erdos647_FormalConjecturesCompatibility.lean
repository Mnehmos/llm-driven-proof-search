import Erdos647_ConcreteAsymptoticDensity

/-!
# Erdős #647 — Formal Conjectures predicate compatibility

This module mechanically checks that the density campaign counts the exact
candidate expression used by `FormalConjectures/ErdosProblems/647.lean`.
It does not claim that the density theorem answers the open existential.

The two repositories currently pin different Lean/Mathlib releases, so this
portable artifact mirrors the Formal Conjectures expression verbatim and is
compiled in the campaign toolchain.  The corresponding `Candidate` and
`candidatesUpTo` API is compiled independently in the Formal Conjectures
toolchain. The candidate predicate is definitionally identical (`Iff.rfl`);
the bounded Finsets are proved equal by extensional simplification because
their conjunctions are associated differently.
-/

namespace Erdos647

/-- The exact bounded set expression appearing in the Formal Conjectures API. -/
noncomputable def formalConjecturesCandidatesUpTo (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n =>
    24 < n ∧
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2

/-- The campaign's `CandidateBound` is definitionally the same maximum bound. -/
theorem candidateBound_iff_formalConjectures_expression (n : ℕ) :
    CandidateBound n ↔
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 :=
  Iff.rfl

/-- Membership unfolds to the exact expression from the open formalization. -/
theorem mem_formalConjecturesCandidatesUpTo_iff {X n : ℕ} :
    n ∈ formalConjecturesCandidatesUpTo X ↔
      1 ≤ n ∧ n ≤ X ∧ 24 < n ∧
        (⨆ m : Fin n,
          (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  classical
  simp [formalConjecturesCandidatesUpTo, and_assoc]

/-- The two bounded candidate Finsets are extensionally identical. -/
theorem boundedCandidates_eq_formalConjecturesCandidatesUpTo (X : ℕ) :
    boundedCandidates X = formalConjecturesCandidatesUpTo X := by
  classical
  ext n
  simp [boundedCandidates, formalConjecturesCandidatesUpTo, CandidateBound,
    and_assoc]

/-- The density theorem restated for the exact Formal Conjectures expression. -/
theorem formalConjecturesCandidates_density_global (X : ℕ) :
    ((formalConjecturesCandidatesUpTo X).card : ℝ) ≤
      globalDensityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7 := by
  rw [← boundedCandidates_eq_formalConjecturesCandidatesUpTo]
  exact boundedCandidates_density_global X

end Erdos647
