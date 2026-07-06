import Mathlib

/-!
# Arithmetic kit (issue #89)

Reusable number-theory scaffolding for Erdős-style and contest problems that
turn on divisor sums, multiplicativity, prime-power valuations, modular
periodicity, and Pell-type recurrences — the arithmetic that generic
`omega`/`norm_num`/`ring` calls cannot reach on their own.

## Epistemic status

Everything in this kit is **kernel-verified Lean** backed by Mathlib — there
are no empirical or certificate-backed claims here. (Certificate-backed
finite search is deliberately out of scope; that is issue #88's
ExtremalCombinatoricsKit design surface.)

## Target problem families

- Divisor-sum and perfect-number style problems (`σ` bridges below).
- Prime-power divisibility and valuation arguments (`prime_pow_dvd_iff`).
- Pell-style equations and solution recurrences (`pell_step`).
- Modular periodicity / last-digit arguments (period-cycle fixture below).

## Route notes

The v1 layer normalizes the vocabulary (σ as plain divisor sums,
multiplicativity as one rewrite, valuations as `factorization` inequalities).
Deliberately out of scope for v1: descent schemas, general multiplicative
function induction over factorizations, and Pell fundamental-solution
existence — those get scoped when a concrete target problem needs them.
-/

namespace LeanChecker.ArithmeticKit

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- **Divisor-sum normalization**: `σ 1` as a plain divisor sum, without the
`^ 1` that `sigma_apply` leaves behind — the shape perfect-number style
statements actually use. -/
theorem sigma_one_eq_sum_divisors (n : ℕ) : σ 1 n = ∑ d ∈ n.divisors, d := by
  rw [sigma_apply]
  exact Finset.sum_congr rfl fun d _ => pow_one d

/-- **Multiplicativity bridge**: divisor-power sums split across coprime
factorizations in one rewrite. -/
theorem sigma_mul_of_coprime {k m n : ℕ} (h : Nat.Coprime m n) :
    σ k (m * n) = σ k m * σ k n :=
  isMultiplicative_sigma.map_mul_of_coprime h

/-- **Prime-power valuation bridge**: `p ^ k ∣ n` as a `factorization`
inequality, the form valuation arguments chain through. -/
theorem prime_pow_dvd_iff {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p :=
  hp.pow_dvd_iff_le_factorization hn

/-- **Pell recurrence step** for `x² − 2y² = 1`: solutions propagate through
`(x, y) ↦ (3x + 4y, 2x + 3y)`. One `linear_combination` — no `nlinarith`
search over the quadratic atoms. -/
theorem pell_step {x y : ℤ} (h : x ^ 2 - 2 * y ^ 2 = 1) :
    (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = 1 := by
  linear_combination h

/-- Fixture (issue #89 acceptance): **multiplicativity in action** — `28` is
perfect (`σ₁ 28 = 56 = 2·28`), computed through the coprime factorization
`4 · 7` rather than raw enumeration. -/
example : σ 1 28 = 56 := by
  rw [show (28 : ℕ) = 4 * 7 by norm_num, sigma_mul_of_coprime (by decide)]
  decide

/-- Fixture (issue #89 acceptance): **modular periodicity beyond one-shot
normalization** — the last digit of `3 ^ 2026` via the period-4 cycle, a
number far past what direct evaluation handles. -/
example : 3 ^ 2026 % 10 = 9 := by
  have h : (3 : ℕ) ^ 2026 = (3 ^ 4) ^ 506 * 3 ^ 2 := by
    rw [← pow_mul, ← pow_add]
  rw [h, Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- Fixture: **Pell chain** — from the fundamental solution `(3, 2)`, the
recurrence step certifies the next solution `(17, 12)` structurally. -/
example : ((3 : ℤ) * 3 + 4 * 2) ^ 2 - 2 * (2 * 3 + 3 * 2) ^ 2 = 1 :=
  pell_step (by norm_num)

end LeanChecker.ArithmeticKit
