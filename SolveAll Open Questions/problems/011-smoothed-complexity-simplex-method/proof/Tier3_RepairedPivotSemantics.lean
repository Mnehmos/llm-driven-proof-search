/-
SolveAll #11 — repaired objective-independent initialization semantics.

The initializer receives only the constraint data.  The objective is supplied
to the charged transition rule afterwards.  A finite execution records exactly
`k` charged transitions, and those transitions are proved equal to the existing
Tier-2 recursive `pivotCount`.
-/
import Tier2_PivotCount

namespace SolveAll011.Tier3

/-- A deterministic pivot rule with an objective-independent Phase-I start. -/
structure ObjectiveIndependentPivotRule
    (ConstraintData Objective State : Type) where
  init : ConstraintData → State
  step : ConstraintData → Objective → State → Option State

/-- A concrete execution of exactly `k` charged pivots. -/
structure ChargedExecution
    {ConstraintData Objective State : Type}
    (R : ObjectiveIndependentPivotRule ConstraintData Objective State)
    (data : ConstraintData) (objective : Objective) (k : ℕ) where
  stateAt : ℕ → State
  starts_at_init : stateAt 0 = R.init data
  charged_step : ∀ t < k,
    R.step data objective (stateAt t) = some (stateAt (t + 1))

/-- Following `k` certified charged transitions makes the recursive Tier-2
counter return exactly `k` when run with fuel `k`. -/
theorem pivotCount_eq_of_charged_steps
    {State : Type} (step : State → Option State) (stateAt : ℕ → State) :
    ∀ k : ℕ, (∀ t < k, step (stateAt t) = some (stateAt (t + 1))) →
      SolveAll011.Tier2.pivotCount step k (stateAt 0) = k := by
  intro k
  induction k generalizing stateAt with
  | zero => simp [SolveAll011.Tier2.pivotCount]
  | succ k ih =>
      intro hstep
      rw [SolveAll011.Tier2.pivotCount, hstep 0 (by omega)]
      have htail : ∀ t < k,
          step ((fun s => stateAt (s + 1)) t) =
            some ((fun s => stateAt (s + 1)) (t + 1)) := by
        intro t ht
        simpa [Nat.add_assoc] using hstep (t + 1) (by omega)
      change SolveAll011.Tier2.pivotCount step k (stateAt 1) + 1 = k + 1
      have hrec := ih (fun s => stateAt (s + 1)) htail
      simpa using congrArg Nat.succ hrec

/-- The abstract Tier-2 pivot count of a charged execution is its recorded
finite path length. -/
theorem ChargedExecution.pivotCount_eq
    {ConstraintData Objective State : Type}
    {R : ObjectiveIndependentPivotRule ConstraintData Objective State}
    {data : ConstraintData} {objective : Objective} {k : ℕ}
    (exec : ChargedExecution R data objective k) :
    SolveAll011.Tier2.pivotCount (R.step data objective) k (R.init data) = k := by
  rw [← exec.starts_at_init]
  exact pivotCount_eq_of_charged_steps _ exec.stateAt k exec.charged_step

/-- Two Phase-II executions on the same constraints, including objectives
`c` and `-c`, start at the same state because initialization cannot inspect the
objective. -/
theorem ChargedExecution.common_start
    {ConstraintData Objective State : Type}
    {R : ObjectiveIndependentPivotRule ConstraintData Objective State}
    {data : ConstraintData} {objective₁ objective₂ : Objective} {k₁ k₂ : ℕ}
    (e₁ : ChargedExecution R data objective₁ k₁)
    (e₂ : ChargedExecution R data objective₂ k₂) :
    e₁.stateAt 0 = e₂.stateAt 0 := by
  rw [e₁.starts_at_init, e₂.starts_at_init]

#print axioms pivotCount_eq_of_charged_steps
#print axioms ChargedExecution.pivotCount_eq
#print axioms ChargedExecution.common_start

end SolveAll011.Tier3
