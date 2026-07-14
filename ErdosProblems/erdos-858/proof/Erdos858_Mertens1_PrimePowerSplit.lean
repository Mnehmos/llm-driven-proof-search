/-
Erdős problem #858 — Chojecki 2026, analytic §5 building block toward the exact
constant c₂ via Mertens' first theorem  Σ_{p≤x}(log p)/p = log x + O(1).

Prime-power split identity (option a): the full von Mangoldt Mertens sum splits
exactly into the prime-indexed Mertens sum plus the non-prime (proper prime
power, k≥2) tail,

    Σ_{d ≤ N} Λ(d)/d
      = Σ_{p ≤ N, p prime} (log p)/p  +  Σ_{d ≤ N, d not prime} Λ(d)/d.

This isolates the k≥2 prime-power tail term whose uniform-in-N boundedness
(option c) is the remaining analytic input converting the von Mangoldt
Mertens-1 into the sharp prime-sum Mertens-1 for the exact c₂ of #858. It is the
exact-identity companion to the inequality atom
`erdos858_mertens1_prime_le_vonMangoldt` (option b): dropping the nonnegative
tail on the RHS here recovers that inequality.

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : 33195785-db9b-4f8c-93a6-f61e9b49aca1
  episode_id         : 92133fcc-6c98-4f9a-adfe-53d05344f2eb
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 1
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 773e3b63bb969f18c725ed59378ddbf4f11f78789821df83f2ff9348d8fdebbf

Proof sketch.
  (1) `Finset.sum_filter_add_sum_filter_not (Icc 1 N) Nat.Prime f`, used as a
      right-to-left rewrite, partitions the whole-set sum Σ_{d≤N} Λ(d)/d into
      (Σ over primes Λ(d)/d) + (Σ over non-primes Λ(d)/d).
  (2) `congr 1` peels off the addition; the non-prime block is syntactically
      identical on both sides and closes by rfl, leaving the prime block.
  (3) `Finset.sum_congr rfl` + `ArithmeticFunction.vonMangoldt_apply_prime`
      rewrite Λ p = Real.log p on each prime index, matching the RHS log-form.

Exact lemma for Λ(p) = log p on primes:
  `ArithmeticFunction.vonMangoldt_apply_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log p`
  (Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean:89).
-/
import Mathlib

namespace Erdos858

open scoped BigOperators

theorem erdos858_mertens1_prime_power_split :
    ∀ N : ℕ, ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / (d : ℝ)
      = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ))
        + ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ Nat.Prime d),
            ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
  intro N
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime
        (fun d => ArithmeticFunction.vonMangoldt d / (d : ℝ))]
  congr 1
  exact Finset.sum_congr rfl (fun p hp => by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2])

end Erdos858
