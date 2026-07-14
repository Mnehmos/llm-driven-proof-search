/-
Erdős Problem #858 — §5 analytic foundation: Mertens' first theorem building
block. The clean unconditional Stirling UPPER bound on log(N!).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 quantitative-Mertens / exact-constant c₂ development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP episode 4f5d3658-39b3-4a18-be9e-99e8420b5126,
problem_version_id 91dccbad-d0f8-4bef-baef-ad962b2a31af.
Outcome: kernel_verified / root_proved (root_kernel_verified).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 5cce647842ad7bdef55c6efe23372e0f3352dc20dcbcc16123d648a53ce866b7.

Content: the exact constant c₂ of #858 needs Mertens' first theorem
  Σ_{p≤x} (log p)/p = log x + O(1),
whose classical elementary proof needs a two-sided estimate on log(N!). This
Mathlib pin provides the unconditional Stirling LOWER bound
  `Stirling.le_log_factorial_stirling` : N·log N − N + (log N)/2 + (log 2π)/2 ≤ log(N!)
but the matching UPPER bound is only ASYMPTOTIC
  (`Stirling.factorial_isEquivalent_stirling`, large N;
   `sqrt_pi_le_stirlingSeq` effectively delivers only the lower side).

This atom supplies the cleanest UNCONDITIONAL upper companion, reachable by a
crude but true termwise estimate rather than the asymptotic machinery:

  log(N!) = Σ_{n=1}^{N} log n ≤ Σ_{n=1}^{N} log N = N · log N,

since log is increasing and every n ≤ N in the range. Target:

  ∀ N ≥ 1,  log (N!) ≤ N · log N.

Together with the sibling `erdos858_mertens1_stirling_lower`
  (∀ N ≥ 1, N·log N − N ≤ log (N!))
this pins log(N!) between two elementary, fully unconditional inequalities:
  N·log N − N ≤ log(N!) ≤ N·log N,
i.e. an unconditional |log(N!) − N·log N| ≤ N bound. (The sharp
N·log N − N + O(log N) upper term is NOT reachable unconditionally in this pin —
it would need the asymptotic Stirling equivalence + an N₀ threshold, or an
integral comparison Σ log n ≤ ∫₁^{N+1} log.)

Proof: (1) inline the log-factorial identity log(N!) = Σ_{n∈Icc 1 N} log n via
`Finset.prod_Ico_id_eq_factorial` + `Nat.cast_prod`, pushing `Real.log` through
the product with `Real.log_prod` (nonzero side-condition (↑x:ℝ) ≠ 0 for x ≥ 1
discharged by `Nat.cast_ne_zero.mpr`). (2) bound the sum termwise:
`Finset.sum_le_sum` with `Real.log_le_log` (0 < ↑i from i ≥ 1, ↑i ≤ ↑N from
i ≤ N). (3) collapse the constant sum Σ_{Icc 1 N} log N = #(Icc 1 N) • log N =
N · log N via `Finset.sum_const`, `Nat.card_Icc` (= N+1−1), `Nat.add_sub_cancel`,
`nsmul_eq_mul`. Threshold needed: N ≥ 1 (statement holds for N = 0 too — both
sides are 0 — but N ≥ 1 mirrors the lower-bound atom for the two-sided assembly).
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens-1 building block: the clean unconditional Stirling upper
bound on `log (N!)`. For every natural `N ≥ 1`,
  `log (N!) ≤ N · log N`.
Obtained from the termwise bound `log n ≤ log N` (n ≤ N, log increasing) applied
to the log-factorial identity `log (N!) = Σ_{n≤N} log n`. This is the upper half
of the log-factorial estimate feeding the exact-constant `c₂` development; paired
with `erdos858_mertens1_stirling_lower` it gives the unconditional sandwich
`N·log N − N ≤ log(N!) ≤ N·log N`. -/
theorem erdos858_mertens1_stirling_upper :
    ∀ (N : ℕ), 1 ≤ N → Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log (N : ℝ) := by
  intro N hN
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have key : ((N.factorial : ℝ)) = ∏ x ∈ Finset.Ico 1 (N + 1), (x : ℝ) := by
    rw [← Finset.prod_Ico_id_eq_factorial N, Nat.cast_prod]
  have hlog : Real.log (N.factorial : ℝ) = ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) := by
    rw [key, Real.log_prod, ← hset]
    intro x hx
    rw [Finset.mem_Ico] at hx
    exact Nat.cast_ne_zero.mpr (by omega)
  have hbound : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Icc] at hi
    exact Real.log_le_log (by exact_mod_cast (show 0 < i by omega)) (by exact_mod_cast hi.2)
  have hconst : ∑ _n ∈ Finset.Icc 1 N, Real.log (N : ℝ) = (N : ℝ) * Real.log (N : ℝ) := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  rw [hlog, ← hconst]
  exact hbound

end Erdos858
