/-
Erdős Problem #858 — Lemma 4.5 CAPSTONE cast to ℝ (Chojecki 2026).

Cast bridge: `lemma45_CN_eq_RN_over_a`'s (#202) ℚ-valued conclusion
`Σ_{n:π n=a}1/n = (1/a)(P_N(a)+Q_N(a))` transported to ℝ via
`congrArg`+`push_cast` — the reusable pattern proven throughout this
session (#181/#182/#184/#185). Produces atom A2's exact `hCR` hypothesis
in ℝ (`Erdos858_Thm12_A2_Prop51Identity.lean`) — **the LAST piece needed
before A2's Prop 5.1 identity is fully unconditional.**

Kernel-verified via the proofsearch MCP:
  episode a77df46a-e0ea-4718-95da-307cfc004cde,
  problem_version_id c1f4d8e2-6d57-4cc1-b7f2-fd6139f94573.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash d291d3ca3a68ea15d3e5f2962ece222ff5ae4910688d2537d72ce142d236147d.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 capstone cast to ℝ: `Σ_{n:π n=a}1/n=(1/a)(P_N(a)+Q_N(a))`
transported from ℚ (`lemma45_CN_eq_RN_over_a`) via `congrArg`+`push_cast`.
Discharges A2's `hCR` hypothesis unconditionally in ℝ — the final piece of
A2's four hypotheses. -/
theorem lemma45_CN_eq_RN_over_a_cast_R :
    ∀ (π : ℕ → ℕ) (N a : ℕ),
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℚ)/(n:ℚ)) =
        (1/(a:ℚ)) * ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℚ)/(p:ℚ))
          + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
              (1:ℚ)/((pq.1:ℚ)*(pq.2:ℚ))))) →
      ((∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) =
        (1/(a:ℝ)) * ((∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℝ)/(p:ℝ))
          + (∑ pq ∈ ((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N),
              (1:ℝ)/((pq.1:ℝ)*(pq.2:ℝ)))) := by
  intro π N a hQ
  have hR := congrArg (fun x : ℚ => (x:ℝ)) hQ
  push_cast at hR
  exact hR

end Erdos858
