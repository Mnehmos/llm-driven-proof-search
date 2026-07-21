/-
Erdős Problem #858 — §5.3 o(1)-Mertens arc, atom 5 (Chojecki 2026).

`interval prime-sum split` (pure Finset): for naturals `m ≤ n`,

  `Σ_{p≤n} 1/p − Σ_{p≤m} 1/p = Σ_{m<p≤n} 1/p`  (prime-filtered sums).

Together with the Mertens-2 split identity (#118) applied at both endpoints,
this expresses the interval prime sum `Σ_{N^s<p≤N^t} 1/p` in Abel form — the
sum side of the §5.3 prime block masses. No measure theory: `Finset.sum_filter`
to if-forms, `Icc 1 k = Ioc 0 k`, and #103's own `Finset.sum_Ioc_consecutive`.

Kernel-verified via the proofsearch MCP:
  episode 7806870c-0cb5-453a-ba37-f4c87efd9c32,
  problem_version_id e3581189-3086-4f1e-aada-b433baacbc48.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash b310064cbc1c3000d65610856d88444edbaeeba20474b456721f5859ca628244.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 5 (interval prime-sum split): for `m ≤ n`,
`Σ_{p≤n} 1/p − Σ_{p≤m} 1/p = Σ_{m<p≤n} 1/p`. Pure Finset bookkeeping. -/
theorem erdos858_interval_prime_sum_split :
    ∀ m n : ℕ, m ≤ n →
      (∑ p ∈ Finset.Icc 1 n with p.Prime, (1:ℝ) / (p:ℝ)) - (∑ p ∈ Finset.Icc 1 m with p.Prime, (1:ℝ) / (p:ℝ))
        = ∑ p ∈ Finset.Ioc m n with p.Prime, (1:ℝ) / (p:ℝ) := by
  intro m n hmn
  have hIcc : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := fun k => by ext j; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit := Finset.sum_Ioc_consecutive (fun k : ℕ => if k.Prime then (1:ℝ)/(k:ℝ) else 0) (Nat.zero_le m) hmn
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, hIcc n, hIcc m]
  linarith [hsplit]

end Erdos858
