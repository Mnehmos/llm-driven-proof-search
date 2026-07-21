/-
Erdős Problem #858 — frontier sweep step cast to ℝ (Chojecki 2026).

Cast bridge: the frontier sweep step identity
`S_N(K+1)=S_N(K)+(C_N(K+1)−1/(K+1))`, proven natively over ℚ
(`frontier_sweep_step`, `Erdos858_FrontierSweepStep.lean`), transported to ℝ via
`Rat.cast`, using the reusable `congrArg`+`push_cast` pattern proven in
`erdos858_parent_counting_cast_R` (#181). Needed alongside the parent-counting
cast for the eventual full ℚ→ℝ bridge of the Prop 5.1 identity's `hSK`
hypothesis (Theorem 1.2 assembly, atom A2).

Proof: identical pattern to #181 — `congrArg (fun x:ℚ=>(x:ℝ)) hQ` forces the
cast, `push_cast` distributes it through the sums/subtraction/division, `exact`
closes directly.

Kernel-verified via the proofsearch MCP:
  episode 76adfeec-a70f-469c-a693-de67ffcb5d0d,
  problem_version_id b6b94ef4-52b6-4623-bc8f-b7254c115fe2.
Outcome: kernel_verified / root_kernel_verified (1st submission — confirms the
#181 cast pattern is fully reusable, not a one-off).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 8d5954b296761882a7218dd7da3c80c16833e131c3dc6105f82a37807baf4c0d.
-/
import Mathlib

namespace Erdos858

/-- Frontier sweep step cast to ℝ: `S_N(K+1)=S_N(K)+(C_N(K+1)−1/(K+1))`
transported from ℚ via `congrArg`+`push_cast` (the #181 pattern, confirmed
reusable). -/
theorem erdos858_sweep_step_cast_R :
    ∀ (π : ℕ → ℕ) (N K : ℕ),
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K + 1 ∧ K + 1 < n), (1:ℚ)/(n:ℚ))
          = (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ))
            + ((∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = K + 1), (1:ℚ)/(n:ℚ)) - (1:ℚ)/((K:ℚ) + 1))) →
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K + 1 ∧ K + 1 < n), (1:ℝ)/(n:ℝ))
          = (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℝ)/(n:ℝ))
            + ((∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = K + 1), (1:ℝ)/(n:ℝ)) - (1:ℝ)/((K:ℝ) + 1))) := by
  intro π N K hQ
  have hR := congrArg (fun x : ℚ => (x:ℝ)) hQ
  push_cast at hR
  exact hR

end Erdos858
