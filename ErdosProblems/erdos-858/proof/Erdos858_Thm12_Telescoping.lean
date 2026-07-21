/-
Erdős Problem #858 — Theorem 1.2 assembly, Prop 5.1 telescoping core (Chojecki 2026).

`frontier telescoping`: for any `S : ℕ → ℝ` and `m ≤ n`,

  `S(n) − S(m) = Σ_{a ∈ Ioc m n} (S(a) − S(a−1))`.

This is the mechanism turning the frontier maximum `M(N) = S_N(K*)` into a sum of
per-step increments `q_N(a) = S_N(a) − S_N(a−1) = (R_N(a) − 1)/a` (Prop 3.2 + Prop 5.1
increment) — the bridge from the frontier sweep to the tail sum
`Σ_{K*<a≤√N} (1 − R_N(a))/a` of the Prop 5.1 frontier identity.

Proof: induction on `n` from `m` (`Nat.le_induction`); base `Ioc m m = ∅`
(`simp`); step via `Finset.sum_Ioc_succ_top` + the induction hypothesis +
`(n+1) − 1 = n` (`Nat.add_sub_cancel`), then `ring`.

Kernel-verified via the proofsearch MCP:
  episode cbe5a4e4-a4ad-4069-ad78-fa02cc01fd34,
  problem_version_id 9f1d6a58-add9-4ad6-a1b1-189c5901b920.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c1909182c1523fc1a30aef4c288fb5ad2defaab3a8a7b170d83b2fce584fb615.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 / Prop 5.1 telescoping core: `S(n) − S(m) = Σ_{a∈Ioc m n}(S(a)−S(a−1))`
for `m ≤ n` — the frontier sweep telescopes its per-step increments. `Nat.le_induction`
+ `Finset.sum_Ioc_succ_top`. -/
theorem erdos858_thm12_telescoping :
    ∀ (S : ℕ → ℝ) (m n : ℕ), m ≤ n →
      ∑ a ∈ Finset.Ioc m n, (S a - S (a-1)) = S n - S m := by
  intro S m n hmn
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [Finset.sum_Ioc_succ_top (by omega), ih]; simp only [Nat.add_sub_cancel]; ring

end Erdos858
