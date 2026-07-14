/-
Erdős Problem #858 — §5 analytic foundation: Mertens' first theorem building
block. The clean unconditional Stirling LOWER bound on log(N!).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 quantitative-Mertens / exact-constant c₂ development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP episode 962a746a-41eb-40cc-ab54-bb33e85e4fb2,
problem_version_id fa9a52db-11eb-4b8e-a772-1a492561c599.
Outcome: kernel_verified / root_proved (root_kernel_verified).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bd6757b0337e65fd7e8b8b676b0d82ba117821b02d0e042e9ebf171b21df60da.

Content: the exact constant c₂ of #858 needs Mertens' first theorem
  Σ_{p≤x} (log p)/p = log x + O(1),
whose classical elementary proof needs a lower bound on log(N!). This Mathlib
pin provides the unconditional Stirling lower bound
  `Stirling.le_log_factorial_stirling {n : ℕ} (hn : n ≠ 0) :`
  `    n * log n - n + log n / 2 + log (2 * π) / 2 ≤ log n !`
(Mathlib/Analysis/SpecialFunctions/Stirling.lean:285; itself a log of
`le_factorial_stirling (n) : √(2 * π * n) * (n / exp 1) ^ n ≤ n !`, line 268).
NOTE: this is a ONE-SIDED bound — the matching upper bound is only asymptotic
(`Stirling.factorial_isEquivalent_stirling`, large N), so a closed two-sided
|log(N!) − (N·log N − N)| bound needs a large-N threshold argument.

This atom extracts the cleanest unconditional consequence, obtained by dropping
the nonnegative tail (log N)/2 + (log 2π)/2 ≥ 0:

  ∀ N ≥ 1,  N·log N − N ≤ log (N!).

Proof: from `hN : 1 ≤ N` get `hn : N ≠ 0` (omega). Apply the Stirling lemma. The
dropped tail is nonnegative: `Real.log N ≥ 0` since `1 ≤ (N : ℝ)` (from N ≥ 1),
and `Real.log (2 * π) ≥ 0` since `1 ≤ 2 * π` (2π > 6 from `Real.pi_gt_three`).
`linarith` then cancels the shared nonlinear atom `N · log N` and closes the
inequality. Threshold needed: N ≥ 1 (the source lemma needs only n ≠ 0).
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens-1 building block: the clean unconditional Stirling lower
bound on `log (N!)`. For every natural `N ≥ 1`,
  `N · log N − N ≤ log (N!)`.
Obtained from `Stirling.le_log_factorial_stirling` by dropping the nonnegative
tail `(log N)/2 + (log 2π)/2`. This is the lower half of the log-factorial
estimate feeding the exact-constant `c₂` development. -/
theorem erdos858_mertens1_stirling_lower :
    ∀ (N : ℕ), 1 ≤ N → (N : ℝ) * Real.log (N : ℝ) - (N : ℝ) ≤ Real.log (N.factorial : ℝ) := by
  intro N hN
  have hn : N ≠ 0 := (by omega)
  have hstir := Stirling.le_log_factorial_stirling hn
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hlog2pi : (0 : ℝ) ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith

end Erdos858
