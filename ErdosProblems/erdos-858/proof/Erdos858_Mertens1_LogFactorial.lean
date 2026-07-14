/-
Erdős Problem #858 — §5 analytic foundation: Mertens' first theorem, building
block (1). The log-factorial identity that bridges the Mertens log-sum to
Stirling.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 quantitative-Mertens / exact-constant c₂ development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP episode aa47c1d1-43c0-4ce1-89aa-4bf1aba7dd26,
problem_version_id d54372e7-53d5-4d52-affc-cb659238705c.
Outcome: kernel_verified / root_proved (root_kernel_verified).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 86b2bc57322113c7dd2539ac86b56d0ded1799501a6992ab8bc06df5ace7b435.

Content: the exact constant c₂ of #858 needs Mertens' first theorem
  Σ_{p≤x} (log p)/p = log x + O(1),
which is NOT assembled in this Mathlib pin. Its classical elementary proof rests
on three building blocks Mathlib DOES have:
  (1) the log-factorial identity  log(N!) = Σ_{n≤N} log n   [THIS FILE],
  (2) log n = Σ_{d|n} Λ(d)                                  [ArithmeticFunction.vonMangoldt_sum],
  (3) ψ(x) = Σ_{n≤x} Λ(n) = O(x)                            [Chebyshev.psi_le / le bounds].
This atom formalizes (1) in its cleanest exact form:

  ∀ N, Σ_{n ∈ Finset.Icc 1 N} log n = log (N!).

Proof: rewrite Icc 1 N = Ico 1 (N+1) (ext + omega), rewrite the factorial as the
product  (↑N! : ℝ) = ∏_{x ∈ Ico 1 (N+1)} (↑x : ℝ)  via
`Finset.prod_Ico_id_eq_factorial` and `Nat.cast_prod`, then push `Real.log`
through the product with `Real.log_prod` (whose nonzero side-condition
`(↑x : ℝ) ≠ 0` for x ≥ 1 is discharged by `Nat.cast_ne_zero.mpr (by omega)`).
The resulting sums are syntactically identical, so the equation closes by rfl.

Note on the O(x) error term of Mertens-1: this pin provides only the ONE-SIDED
unconditional Stirling lower bound `Stirling.le_log_factorial_stirling`
  N·log N − N + (log N)/2 + (log 2π)/2 ≤ log(N!),
with the matching upper bound available only asymptotically via
`Stirling.factorial_isEquivalent_stirling` (large N). A closed two-sided
|log(N!) − (N·log N − N)| = O(log N) bound therefore requires a large-N
threshold argument; this identity is the clean, unconditional bridge to it.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens-1 building block (1): the sum of `log n` over the
integers `1 ≤ n ≤ N` equals `log (N!)`. This is the elementary identity that
connects the Mertens log-sum to Stirling's estimate of `log (N!)`. -/
theorem erdos858_mertens1_log_sum_eq_log_factorial :
    ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) = Real.log (N.factorial : ℝ) := by
  intro N
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have key : ((N.factorial : ℝ)) = ∏ x ∈ Finset.Ico 1 (N + 1), (x : ℝ) := by
    rw [← Finset.prod_Ico_id_eq_factorial N, Nat.cast_prod]
  rw [hset, key, Real.log_prod]
  intro x hx
  rw [Finset.mem_Ico] at hx
  exact Nat.cast_ne_zero.mpr (by omega)

end Erdos858
