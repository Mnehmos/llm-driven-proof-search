/-
Erdős Problem #858 — §5.4 harmonic Riemann sum, ladder rung 1 (Chojecki 2026).

`logCoordinate_mem_unitInterval`: the normalized log-coordinate lands in `(0,1]`.
For `1 < a ≤ N`, `0 < log a / log N ≤ 1` (log a > 0 since a > 1; log a ≤ log N
since a ≤ N; log N > 0). This is the coordinate map `{1 < a ≤ N} → (0,1]` over which
the harmonic Riemann sum `(1/log N) Σ f(log a/log N)/a → ∫₀¹ f` is taken (toward
Theorem 1.2). Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 6da5fb7f-e9c0-4d46-ae4e-0eb77a26a25b,
  problem_version_id b282c094-8f46-4d7c-b6fa-5cb3f676a6cd.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash cc5694c8f86fde5618230d66aa1eadbe2e2bad80d0ce41dc54808093e6d3ec37.
-/
import Mathlib

namespace Erdos858

/-- Ladder rung 1: for `1 < a ≤ N`, the normalized log-coordinate
`log a / log N ∈ (0, 1]`. The coordinate map for the §5.4 harmonic Riemann sum. -/
theorem erdos858_logcoord_mem_unitInterval :
    ∀ (N a : ℕ), 1 < a → a ≤ N → (0:ℝ) < Real.log a / Real.log N ∧ Real.log a / Real.log N ≤ 1 := by
  intro N a ha haN
  have ha1 : (1:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hloga : (0:ℝ) < Real.log a := Real.log_pos ha1
  have haN' : (a:ℝ) ≤ (N:ℝ) := by exact_mod_cast haN
  have hlogaN : Real.log a ≤ Real.log N := Real.log_le_log (by linarith) haN'
  have hlogN : (0:ℝ) < Real.log N := lt_of_lt_of_le hloga hlogaN
  exact ⟨div_pos hloga hlogN, by rw [div_le_one hlogN]; exact hlogaN⟩

end Erdos858
