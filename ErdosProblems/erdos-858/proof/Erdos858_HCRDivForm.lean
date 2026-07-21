/-
Erdős Problem #858 — Theorem 1.2 assembly, `hCR` div-form reshape (Chojecki 2026).

Reshapes `lemma45_CN_eq_RN_over_a_cast_R`'s (`Erdos858_Lemma45_CNEqualsRNOverACastR.lean`)
`(1/a)*x` form into the `x/a` form atom A2's `hCR` hypothesis
(`Erdos858_Thm12_A2_Prop51Identity.lean`, `CN a = RN a/(a:ℝ)`) literally
expects. Pure algebra — `ring` closes `(1/a)*x = x/a` directly (division in
a field is multiplication by the inverse, so `ring` normalizes both sides
to the same form).

With this, **A2's `hCR` hypothesis is available in EXACTLY the form A2
needs**, completing the reshape of all four of A2's hypotheses
(`hSK`/`erdos858_hSK_general_cast_R`, `hC0`/`erdos858_hC0_cast_R`,
`hHdiff`/`erdos858_icc_sum_diff_eq_sum_Ioc`, `hCR`/this atom) into their
exact required shapes.

Kernel-verified via the proofsearch MCP:
  episode e5fb81f6-4043-4f70-a445-72b3e9a16de5,
  problem_version_id a6f500b0-4b2d-481c-af96-a11d3119a70a.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 6dce5ee3327161ad59d7de2d9ff9e6c1a7603d357202d9c8d9c4ee405cf3901a.
-/
import Mathlib

namespace Erdos858

/-- `hCR` div-form reshape: `(1/a)*(P_N(a)+Q_N(a)) = (P_N(a)+Q_N(a))/a`, via
`ring`. Puts the Lemma 4.5 capstone into A2's exact `CN a = RN a/a` shape. -/
theorem lemma45_CN_eq_RN_div_a :
    ∀ (π : ℕ → ℕ) (N a : ℕ),
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) =
        (1/(a:ℝ)) * ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℝ)/(p:ℝ))
          + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
              (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ))))) →
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) =
        ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℝ)/(p:ℝ))
          + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
              (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ)))) / (a:ℝ)) := by
  intro π N a hQ
  rw [hQ]
  ring

end Erdos858
