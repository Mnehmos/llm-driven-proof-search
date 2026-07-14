/-
Erdős problem #858 — Chojecki 2026, analytic §5 building block toward the exact
constant c₂ via Mertens' first theorem  Σ_{p≤x}(log p)/p = log x + O(1).

Prime-power (non-prime) tail NONNEGATIVITY — the trivial-but-required LOWER half
of the `0 ≤ T ≤ 1` tail hypothesis discharged by the prime Mertens-1 lower
assembly (campaign atom #51, `erdos858_prime_mertens1_lower_assembly`):

    0  ≤  Σ_{d ≤ N, d not prime} Λ(d)/d          (option: NONNEG fallback)

where Λ = ArithmeticFunction.vonMangoldt is supported on prime powers p^k with
Λ(p^k) = log p, so the non-prime support is exactly the k≥2 prime powers. The
true limit of the tail is ≈ 0.7554 (Σ_p (log p)/(p(p-1))), well under 1, but the
sharp upper bound `T ≤ 1` needs prime-restricted convergent-series machinery not
present in this Mathlib pin (see note below). This atom supplies the `0 ≤ T`
half, which follows term by term from Λ ≥ 0 and d ≥ 0.

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : f4dcc48c-5364-4f87-af15-d53434edaae8
  episode_id         : 3eb98829-ba19-4393-a509-fd11a9aea664
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 1
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 160036671378de1eee77a5c408caa9b29530d573ff6fc2b1fb002143200bb1fc

Proof.
  `Finset.sum_nonneg`, discharging each summand with
  `div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d)`
  (Λ d ≥ 0 and (d : ℝ) ≥ 0 ⇒ Λ d / d ≥ 0). Same nonneg-witness idiom as the
  verified atom `erdos858_mertens1_prime_le_vonMangoldt`.

Exact lemma for Λ ≥ 0:
  `ArithmeticFunction.vonMangoldt_nonneg {n : ℕ} : 0 ≤ Λ n`
  (Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean:80).

Note on the sharp upper bound `T ≤ 1` (NOT proved here — genuine wall).
  Reindexing the non-prime tail by (p, k) is available
  (`Chebyshev.sum_PrimePow_eq_sum_sum`, `Nat.Primes.prodNatEquiv`), and the
  per-prime geometric tail Σ_{k≥2} (log p)/p^k = (log p)/(p(p-1)) is reachable
  (`tsum_geometric_of_lt_one`). The blocker is the TERMINAL numeric bound
      Σ_{p prime} (log p)/(p(p-1))  ≤  1
  (true value ≈ 0.7554): this Mathlib pin has p-series summability
  (`summable_one_div_nat_pow`, `summable_one_div_nat_rpow`) but NO explicit
  numeric value/bound on any Σ (log n)/n^s. Crucially the over-estimate over ALL
  integers, Σ_{n≥2} (log n)/(n(n-1)) ≈ 1.26, EXCEEDS 1, so the prime restriction
  is essential and the all-integer comparison route does not certify `≤ 1`. A
  rigorous `≤ 1` therefore requires either explicit evaluation of finitely many
  primes plus a rigorous prime tail bound, or a Mertens-style prime-series
  estimate — neither turnkey in this pin.
-/
import Mathlib

namespace Erdos858

open scoped BigOperators

/-- The k≥2 prime-power (non-prime) tail of the von Mangoldt Mertens sum is
nonnegative:  `0 ≤ Σ_{d ≤ N, d not prime} Λ(d)/d`. This is the LOWER half of the
`0 ≤ T ≤ 1` tail hypothesis of the prime Mertens-1 lower assembly. -/
theorem erdos858_mertens1_prime_power_tail_nonneg :
    ∀ N : ℕ,
      0 ≤ ∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ Nat.Prime d),
            ArithmeticFunction.vonMangoldt d / (d : ℝ) := by
  intro N
  exact Finset.sum_nonneg
    (fun d _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))

end Erdos858
