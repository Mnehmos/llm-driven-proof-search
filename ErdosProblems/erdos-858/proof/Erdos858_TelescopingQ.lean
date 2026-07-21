/-
Erdős Problem #858 — telescoping (ℚ-valued analogue, Chojecki 2026).

`ℚ-valued telescoping`: for any `S : ℕ → ℚ` and `m ≤ n`,

  `S(n) − S(m) = Σ_{a ∈ Ioc m n} (S(a) − S(a−1))`.

Direct rational analogue of the already-verified `erdos858_thm12_telescoping`
(ℝ-valued, `Erdos858_Thm12_Telescoping.lean`), needed to bridge the frontier
sweep machinery (natively ℚ-valued: `S_N`, `C_N`, `frontier_sweep_step`,
`frontier_base_zero`, `erdos858_frontier_top_zero`) toward the parent-counting
identity `Σ_a C_N(a) = H_N−1` feeding Prop 5.1 (Theorem 1.2 assembly atom A2,
which works over ℝ, requiring an eventual cast bridge).

Proof: identical to the ℝ version (the tactic sequence is type-agnostic, working
in any `AddCommGroup`) — `Nat.le_induction`; base `Ioc m m = ∅` (`simp`); step via
`Finset.sum_Ioc_succ_top` + the induction hypothesis + `(n+1)−1=n`
(`Nat.add_sub_cancel`), then `ring`.

Kernel-verified via the proofsearch MCP:
  episode 9823a8ed-3a45-4c84-8138-1dcf7239eb33,
  problem_version_id aafe04c0-af27-4586-b4eb-7e3ba4278f9f.
Outcome: kernel_verified / root_kernel_verified (1st submission — verbatim
tactic port from the ℝ version worked directly, confirming the proof strategy
is type-agnostic as expected).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 9b6f9a237a63557efbafac81084a0c6f6b2b76e6dc21547bb01594949d604b74.
-/
import Mathlib

namespace Erdos858

/-- ℚ-valued telescoping: `S(n)−S(m) = Σ_{a∈Ioc m n}(S(a)−S(a−1))` for `m≤n`.
Rational analogue of `erdos858_thm12_telescoping`, needed for the natively-ℚ
frontier sweep machinery. `Nat.le_induction`+`Finset.sum_Ioc_succ_top`. -/
theorem erdos858_telescoping_Q :
    ∀ (S : ℕ → ℚ) (m n : ℕ), m ≤ n →
      ∑ a ∈ Finset.Ioc m n, (S a - S (a-1)) = S n - S m := by
  intro S m n hmn
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [Finset.sum_Ioc_succ_top (by omega), ih]; simp only [Nat.add_sub_cancel]; ring

end Erdos858
