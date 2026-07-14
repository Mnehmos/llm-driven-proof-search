/-
Erdős problem #858 — Chojecki 2026, §5 analytic building block toward the exact
constant c₂ via Mertens' first theorem  Σ_{p≤x}(log p)/p = log x + O(1).

The floor(N/d) vs N/d truncation-error bound. With Λ = ArithmeticFunction.vonMangoldt
and ψ(N) = Σ_{d=1}^{N} Λ(d), for every N : ℕ this proves the conjunction

  (i)   (Σ_{d≤N} Λ(d)·(N/d)) − (Σ_{d≤N} Λ(d)·⌊N/d⌋)  ≤  Σ_{d≤N} Λ(d)  = ψ(N),
  (ii)  Σ_{d≤N} Λ(d)·⌊N/d⌋  ≤  Σ_{d≤N} Λ(d)·(N/d),

where (N/d) is real division and ⌊N/d⌋ = (N / d : ℕ) is Nat (floor) division.

Bound (i) is the fractional-part error term controlling the passage from the exact
double-counting identity  Σ_{n≤N} log n = Σ_{d≤N} Λ(d)·⌊N/d⌋  (see
Erdos858_Mertens1_LogSumVonMangoldt.lean) to  N·Σ_{d≤N} Λ(d)/d : replacing ⌊N/d⌋
by N/d costs at most Σ_{d≤N} Λ(d)·(N/d − ⌊N/d⌋) ≤ Σ_{d≤N} Λ(d) = ψ(N), since
0 ≤ N/d − ⌊N/d⌋ < 1 and Λ ≥ 0. Bound (ii) is the one-sided ⌊N/d⌋ ≤ N/d weighted by
Λ ≥ 0. Combined with Stirling (log(N!) = N log N − N + O(log N)) and Chebyshev's
ψ(N) = O(N) (Erdos858_Mertens1_PsiLinear.lean), (i) yields Mertens' first theorem,
the input to the exact c₂ of #858.

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : 84344737-a1f6-4afd-85dd-8452174062a8
  episode_id         : bb2ca63e-6387-4493-bc8e-1e3b88cacee3
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 1
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 8f66b36665c8e5736bd5390a0c890a0856c45c7b0c62835c437d83352bbbf7ca

Proof sketch.
  Conjunct (i): `Finset.sum_sub_distrib` (backwards) fuses the two Icc-sums into
    Σ_{d} (Λ d·(N/d) − Λ d·⌊N/d⌋); `Finset.sum_le_sum` reduces to a termwise bound.
    Per term: `ring` rewrites to Λ d·((N/d) − ⌊N/d⌋); `mul_le_mul_of_nonneg_left`
    with the fractional bound and `ArithmeticFunction.vonMangoldt_nonneg` gives
    ≤ Λ d·1, closed by `mul_one`. The fractional bound
    (N:ℝ)/d − (N/d:ℕ) ≤ 1 comes from `Nat.lt_floor_add_one ((N:ℝ)/(d:ℝ))`,
    rewritten by `Nat.floor_div_natCast` then `Nat.floor_natCast` to
    (N:ℝ)/d < ↑(N/d) + 1, then `linarith`. No d>0 side condition is needed: the
    div-by-zero convention keeps every lemma valid at d = 0.
  Conjunct (ii): `Finset.sum_le_sum` termwise via `mul_le_mul_of_nonneg_left`
    applied to `Nat.cast_div_le` (↑(N/d) ≤ ↑N/↑d) and `vonMangoldt_nonneg`.

Self-contained; verified against the pinned Mathlib. The proof term below is the
exact byte-for-byte tactic block accepted by the kernel via episode_step.
-/
import Mathlib

namespace Erdos858

open scoped BigOperators

theorem erdos858_mertens1_floor_error :
    ∀ N : ℕ,
      ((∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)))
          - (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ))
        ≤ (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d))
      ∧ ((∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ))
        ≤ (∑ d ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)))) := by
  intro N
  refine ⟨?_, ?_⟩
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum ?_
    intro d _
    have hfrac : (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) ≤ 1 := by
      have h := Nat.lt_floor_add_one ((N : ℝ) / (d : ℝ))
      rw [Nat.floor_div_natCast, Nat.floor_natCast] at h
      linarith
    have hnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    calc ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ)) - ArithmeticFunction.vonMangoldt d * ((N / d : ℕ) : ℝ)
          = ArithmeticFunction.vonMangoldt d * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)) := by ring
      _ ≤ ArithmeticFunction.vonMangoldt d * 1 := mul_le_mul_of_nonneg_left hfrac hnn
      _ = ArithmeticFunction.vonMangoldt d := mul_one _
  · refine Finset.sum_le_sum ?_
    intro d _
    have hnn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt d := ArithmeticFunction.vonMangoldt_nonneg
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le hnn

end Erdos858
