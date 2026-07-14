/-
Erdős problem #858 — Chojecki 2026, analytic §5 building block toward the exact
constant c₂ via Mertens' first theorem  Σ_{p≤x}(log p)/p = log x + O(1).

This is the elementary double-counting identity that underpins Mertens I:

    Σ_{n=1}^{N} log n  =  Σ_{d=1}^{N} Λ(d) · ⌊N/d⌋

where Λ = ArithmeticFunction.vonMangoldt and ⌊N/d⌋ = N / d is Nat division, i.e.
the count of multiples of d in [1,N]. Combined with Stirling's
log(N!) = Σ_{n≤N} log n = N log N − N + O(log N) and Chebyshev's ψ(x) = O(x),
this yields Σ_{p≤x}(log p)/p = log x + O(1) — the input to the exact c₂ of #858.

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : 79cf884a-dcaf-44c2-b64a-bb4c1bbf1326
  episode_id         : 7346fd64-45e3-4521-a20e-4c75355af49e
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 1
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 8cb2596844de37deb989db184026e53cc9c722c9179dc405425f3759c9e4c48d

Proof sketch.
  (1) `ArithmeticFunction.vonMangoldt_sum` : Σ_{d∣n} Λ d = Real.log n, applied
      pointwise under the outer sum.
  (2) For 1 ≤ n ≤ N, `n.divisors = (Icc 1 N).filter (· ∣ n)` — every divisor of
      a positive n ≤ N lies in [1,N] (`Nat.pos_of_mem_divisors`, `Nat.le_of_dvd`,
      `omega`); this lets the inner divisor sum be written as an indicator sum
      over the *fixed* index set `Icc 1 N` via `Finset.sum_filter`.
  (3) `Finset.sum_comm` swaps the two identical `Icc 1 N` sums.
  (4) For fixed d, `← Finset.sum_filter` + `Finset.sum_const` collapse
      Σ_{n≤N} [d∣n] Λ(d) to  #{n ∈ Icc 1 N : d∣n} • Λ(d).
  (5) `Icc 1 N = Ioc 0 N` (`omega`), so `Nat.Ioc_filter_dvd_card_eq_div` gives the
      cardinality as N / d; `nsmul_eq_mul` + `ring` finish.
-/
import Mathlib

namespace Erdos858

open scoped BigOperators

theorem erdos858_mertens1_log_sum_vonMangoldt :
    ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ)
      = ∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  intro N
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have key : ∀ n ∈ Finset.Icc 1 N,
      Real.log (n : ℝ)
        = ∑ d ∈ Finset.Icc 1 N,
            (if d ∣ n then ArithmeticFunction.vonMangoldt d else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hset : (Finset.Icc 1 N).filter (fun d => d ∣ n) = n.divisors := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hd⟩
        exact ⟨hd, by omega⟩
      · rintro ⟨hd, hn0⟩
        have hdpos : 0 < d :=
          Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hd, hn0⟩)
        have hdle : d ≤ n := Nat.le_of_dvd (by omega) hd
        exact ⟨⟨by omega, by omega⟩, hd⟩
    rw [← ArithmeticFunction.vonMangoldt_sum, ← hset, Finset.sum_filter]
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [← Finset.sum_filter, hIcc, Finset.sum_const,
      Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
  ring

end Erdos858
