/-
SolveAll #11 — charged execution / finite basis-path assembly.

This identifies the states of the repaired charged execution with the concrete
normalized basis path and rewrites the deterministic Bach--Huiberts path-length
bound onto the actual Tier-2 recursive pivot count.
-/
import Tier3_RepairedPivotSemantics
import Tier3_FinitePathLowerBoundAssembly

namespace SolveAll011.Tier3

/-- A repaired charged execution whose successive states are exactly the bases
of a concrete normalized simplex path. -/
structure NormalizedChargedExecution
    {ConstraintData Objective ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E)
    (R : ObjectiveIndependentPivotRule ConstraintData Objective (NormalizedFeasibleBasis a))
    (data : ConstraintData) (objective : Objective) (k : ℕ) where
  execution : ChargedExecution R data objective k
  path : NormalizedSimplexPath a k
  state_eq_basis : ∀ (t : ℕ) (ht : t ≤ k),
    execution.stateAt t = path.basis ⟨t, Nat.lt_succ_iff.mpr ht⟩

/-- The deterministic geometric lower bound is a lower bound on the repaired
rule's actual Tier-2 `pivotCount`, not merely on an auxiliary path length. -/
theorem NormalizedChargedExecution.pivotCount_bachHuiberts_lower
    {ConstraintData Objective ι E : Type} [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (a : ι → E)
    {R : ObjectiveIndependentPivotRule ConstraintData Objective (NormalizedFeasibleBasis a)}
    {data : ConstraintData} {objective : Objective} {k : ℕ}
    (run : NormalizedChargedExecution a R data objective k)
    (zPlus zMinus : E) (radius γ : ℝ)
    (hd : 2 ≤ Module.finrank ℝ E) (hR : 0 < radius) (hγ : 0 < γ)
    (hfaceDiam : ∀ t ≤ k, ∀ i, i ∈ run.path.indicesAt t →
      ∀ j, j ∈ run.path.indicesAt t → ‖a i - a j‖ ≤ γ)
    (hstart : ∀ i ∈ run.path.indicesAt 0, ‖zPlus - a i‖ ≤ γ)
    (hfinish : ∀ i ∈ run.path.indicesAt k, ‖a i - zMinus‖ ≤ γ)
    (hfar : 2 / radius ≤ ‖zPlus - zMinus‖) :
    (((Module.finrank ℝ E - 1 : ℕ) : ℝ) *
      (2 / (radius * γ) - 3) ≤
      (SolveAll011.Tier2.pivotCount (R.step data objective) k (R.init data) : ℝ)) := by
  have hpath := normalizedSimplexPath_bachHuiberts_length_lower
    a run.path zPlus zMinus radius γ hd hR hγ hfaceDiam hstart hfinish hfar
  rw [run.execution.pivotCount_eq]
  exact hpath

#print axioms NormalizedChargedExecution.pivotCount_bachHuiberts_lower

end SolveAll011.Tier3
