/-
Erdős Problem #858 — divergence of the prime harmonic sum to +∞.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5; the crude lower-order fact underlying the sharp
Mertens-second-theorem constant that governs the asymptotic constant c₂.)

The exact #858 constant is refined from Mertens' second theorem,
Σ_{p≤x} 1/p = log log x + M + o(1) (leading coefficient exactly 1). This
snapshot records the qualitative backbone: the partial sums of the reciprocals
of the primes below n diverge to +∞. It is the Tendsto-atTop packaging of
Mathlib's `not_summable_one_div_on_primes` (Erdős's proof, "Proofs from THE
BOOK"), obtained through the tracked proofsearch MCP pipeline on 2026-07-14.

  problem_version_id  e6c1bdf5-9036-420b-a76e-59bd2e6b49d3
  episode_id          3a0df92d-5894-4170-9d56-8720cbd86e0f
  root_statement_hash 5de3fa964abd30d794626ee25f7ee58ff95572d85ea06a110434054cde5f0819
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
  mathlib             360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Result:  Tendsto (fun n => Σ_{p ∈ range n, p prime} 1/p) atTop atTop.

Scouting note: this is the STRONGEST prime-reciprocal statement reachable in this
Mathlib pin. The SHARP leading constant 1 of Mertens' second theorem is NOT
reachable here — there is no PrimeNumberTheorem module, no θ(x) = x + o(x), no
Chebyshev lower bound (an explicit TODO in Mathlib/NumberTheory/Chebyshev.lean),
and no Mertens first/second theorem. Only Chebyshev UPPER bounds
(θ x ≤ log 4 · x) and the π–θ Abel-summation bridges exist, which give at best a
log2..log4 bracket on the leading constant, never the exact value 1.

Proof outline:
  1. f := Set.indicator {p | p.Prime} (fun m => (1:ℝ)/m) is nonnegative.
  2. Mathlib's `not_summable_one_div_on_primes` gives ¬ Summable f.
  3. `not_summable_iff_tendsto_nat_atTop_of_nonneg` converts (2) into
     Tendsto (fun n => Σ_{i∈range n} f i) atTop atTop.
  4. `Filter.Tendsto.congr` + `Finset.sum_filter` + per-term
     `Set.indicator_apply` (by_cases on Nat.Prime i) identify the indicator
     partial sum with the filtered prime-reciprocal sum.
-/

import Mathlib

namespace Erdos858

theorem erdos858_prime_reciprocal_diverges :
    Filter.Tendsto (fun n : ℕ => ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      Filter.atTop Filter.atTop := by
  have hf : ∀ n : ℕ, 0 ≤ Set.indicator {p | p.Prime} (fun m : ℕ => (1 : ℝ) / (m : ℝ)) n :=
    fun n => Set.indicator_nonneg (fun p _ => by positivity) n
  have key := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp not_summable_one_div_on_primes
  refine Filter.Tendsto.congr (fun n => ?_) key
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hp : Nat.Prime i <;> simp [Set.indicator_apply, Set.mem_setOf_eq, hp]

end Erdos858
