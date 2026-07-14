/-
Erdős problem #858 — Chojecki 2026, analytic §5 building block toward the exact
constant c₂ via Mertens' first theorem  Σ_{p≤x}(log p)/p = log x + O(1).

Prime-power-tail atom (option b): the prime-indexed Mertens sum is bounded above
by the full von Mangoldt sum,

    Σ_{p ≤ N, p prime} (log p)/p  ≤  Σ_{d ≤ N} Λ(d)/d.

Since Λ = ArithmeticFunction.vonMangoldt is supported on prime powers and
Λ(p) = log p on primes, the prime terms (log p)/p are exactly the prime-indexed
subset of the nonnegative von Mangoldt sum. Combined with the already
kernel-verified two-sided Λ-sum Mertens-1 (Σ_{d≤N} Λ(d)/d = log N + O(1)), this
converts the von Mangoldt Mertens-1 into the UPPER direction of the prime-sum
Mertens-1 — an input to the exact c₂ of #858. (The sharp lower direction needs
the k≥2 prime-power tail bound, option (c), which is not proved here.)

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : 1179f381-2737-4cd1-9be0-a5eb0ec33ab2
  episode_id         : 3dd8b5db-0e62-439e-b8a6-1a8b5aeaf989
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 1
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: c3243e3e3587e802d647709820bdd3efaea0830d285e7de234d6436807a34594

Proof sketch.
  (1) `Finset.sum_congr rfl` + `ArithmeticFunction.vonMangoldt_apply_prime`:
      on the filter set `(Icc 1 N).filter Nat.Prime` every index p is prime, so
      Λ p = Real.log p, rewriting each prime term (log p)/p as Λ p / p. The
      prime-indexed sum thus becomes the prime-indexed slice of the Λ-sum.
  (2) `Finset.sum_le_sum_of_subset_of_nonneg` with the subset
      `Finset.filter_subset _ _ : (Icc 1 N).filter Nat.Prime ⊆ Icc 1 N` and the
      nonnegativity witness `div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg d)`
      (Λ d ≥ 0 and d ≥ 0 ⇒ Λ d / d ≥ 0) closes the subset inequality.

Exact lemma for Λ(p) = log p on primes:
  `ArithmeticFunction.vonMangoldt_apply_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log p`
  (Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean:89).
-/
import Mathlib

namespace Erdos858

open scoped BigOperators

theorem erdos858_mertens1_prime_le_vonMangoldt :
    ∀ N : ℕ, ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
  intro N
  have hcongr : ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
      = ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt p / (p : ℝ) :=
    Finset.sum_congr rfl (fun p hp => by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2])
  rw [hcongr]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun d _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))

end Erdos858
