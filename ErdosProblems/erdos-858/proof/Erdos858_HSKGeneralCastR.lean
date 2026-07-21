/-
Erdős Problem #858 — general-K frontier recursion cast to ℝ (Chojecki 2026).

Cast bridge: `erdos858_hSK_general`'s (#183) ℚ-valued conclusion
`S_N(K) = H_N − H_K − Σ_{K<a≤N} C_N(a)` transported to ℝ via
`congrArg`+`push_cast` — the 3rd application of the reusable pattern proven
in #181/#182. This produces atom A2's exact `hSK` hypothesis in ℝ
(`Erdos858_Thm12_A2_Prop51Identity.lean`), completing the ℚ→ℝ bridge for
A2's parent-counting-based input.

Kernel-verified via the proofsearch MCP:
  episode 95ed1c46-f3cb-489a-9a93-e6a187762cae,
  problem_version_id 9cab66a0-4257-4347-b4d8-5fab7a8eb97f.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash e3215fd9dadf284778c97beb72ec4bf649a746a71b9599c6cfa3ace450156129.
-/
import Mathlib

namespace Erdos858

/-- General-K frontier recursion cast to ℝ: `S_N(K)=H_N−H_K−Σ_{K<a≤N}C_N(a)`
transported from ℚ (`erdos858_hSK_general`) via `congrArg`+`push_cast`.
Discharges A2's `hSK` hypothesis unconditionally in ℝ. -/
theorem erdos858_hSK_general_cast_R :
    ∀ (π : ℕ → ℕ) (N K : ℕ),
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℚ)/(n:ℚ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℚ)/(n:ℚ)) - (∑ n ∈ Finset.Icc 1 K, (1:ℚ)/(n:ℚ))
          - (∑ a ∈ Finset.Ioc K N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℚ)/(n:ℚ))) →
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n), (1:ℝ)/(n:ℝ))
        = (∑ n ∈ Finset.Icc 1 N, (1:ℝ)/(n:ℝ)) - (∑ n ∈ Finset.Icc 1 K, (1:ℝ)/(n:ℝ))
          - (∑ a ∈ Finset.Ioc K N, ∑ n ∈ (Finset.Icc 1 N).filter (fun m => π m = a), (1:ℝ)/(n:ℝ))) := by
  intro π N K hQ
  have hR := congrArg (fun x : ℚ => (x:ℝ)) hQ
  push_cast at hR
  exact hR

end Erdos858
