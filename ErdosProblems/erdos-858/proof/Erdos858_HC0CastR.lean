/-
Erdős Problem #858 — frontier fact hC0 cast to ℝ (Chojecki 2026).

Cast bridge: `erdos858_frontier_CN_zero_above_sqrt`'s (#177) ℚ-valued
conclusion `C_N(a) = 0` (for `N < a·a`, i.e. `a` above `√N`) transported to ℝ
via `congrArg`+`push_cast` — the 4th application of the reusable pattern
proven in #181/#182/#184. Produces atom A2's `hC0` hypothesis in ℝ
(`Erdos858_Thm12_A2_Prop51Identity.lean`, per individual `a` above `√N`).

Kernel-verified via the proofsearch MCP:
  episode 9e48740a-06a1-48ce-acc7-0984c89543c8,
  problem_version_id 48f5c606-1a1a-4826-8d0e-85091fcf3426.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c718f486c8479573dd1b0d1b0721f711cc33d6287d55eb69c771d99daaa97d05.
-/
import Mathlib

namespace Erdos858

/-- Frontier fact hC0 cast to ℝ: `C_N(a)=0` for `N<a·a` transported from ℚ
(`erdos858_frontier_CN_zero_above_sqrt`) via `congrArg`+`push_cast`.
Discharges A2's `hC0` hypothesis (per-`a`) unconditionally in ℝ. -/
theorem erdos858_hC0_cast_R :
    ∀ (π : ℕ → ℕ) (N a : ℕ),
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℚ)/(n:ℚ)) = 0) →
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) = 0) := by
  intro π N a hQ
  have hR := congrArg (fun x : ℚ => (x:ℝ)) hQ
  push_cast at hR
  exact hR

end Erdos858
