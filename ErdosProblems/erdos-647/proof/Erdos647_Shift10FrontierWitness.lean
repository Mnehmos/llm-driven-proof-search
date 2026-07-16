import Mathlib

open ArithmeticFunction

/-!
# Erdős #647 — exact consistency witness beyond shift 10

For `N = 6,970,590` and `n = 2520N = 17,565,886,800`, all seven linear forms
used by the density theorem are prime and every divisor budget through shift
10 holds.  Shift 11 fails: `σ₀(n-11)=24>13`.

This is a negative search certificate, not a candidate for Erdős #647.  It
proves that the seven-form prime tuple together with the refined shift-9 and
shift-10 interfaces cannot by themselves close the remaining `sorry`.

The direct `native_decide` attempt exhausted memory because expanding
`Nat.divisors` at this scale is inappropriate.  The checked proof below uses
the explicit prime factorisations and multiplicativity of `sigma`, leaving
only concrete primality and coprimality decisions to native evaluation.

Proof-search provenance:

* verification job `cb08bbc6-5675-4ba7-a381-e4bdedaf5ffe`: `kernel_pass`;
* problem version `b9a96621-fc15-42af-bf3d-8b330a1cc0f0`;
* episode `1dbde32d-4fb7-4377-931d-df32607e5a6a`:
  `kernel_verified` (`root_proved`).
-/

theorem erdos647_survives_ten_fails_eleven :
    let N : ℕ := 6970590
    let n : ℕ := 2520 * N
    (∀ k ∈ Finset.Icc 1 10, sigma 0 (n - k) ≤ k + 2) ∧
      13 < sigma 0 (n - 11) ∧
      Nat.Prime (210 * N - 1) ∧
      Nat.Prime (315 * N - 1) ∧
      Nat.Prime (420 * N - 1) ∧
      Nat.Prime (630 * N - 1) ∧
      Nat.Prime (840 * N - 1) ∧
      Nat.Prime (1260 * N - 1) ∧
      Nat.Prime (2520 * N - 1) := by
  have hsigma_prime : ∀ p : ℕ, p.Prime → sigma 0 p = 2 := by
    intro p hp
    simpa using (sigma_zero_apply_prime_pow (i := 1) hp)
  have hs1 : sigma 0 17565886799 = 2 :=
    hsigma_prime 17565886799 (by native_decide)
  have hs2 : sigma 0 17565886798 = 4 := by
    rw [show 17565886798 = 2 * 8782943399 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 8782943399 (by native_decide)]
    norm_num
  have hs3 : sigma 0 17565886797 = 4 := by
    rw [show 17565886797 = 3 * 5855295599 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 5855295599 (by native_decide)]
    norm_num
  have hs4 : sigma 0 17565886796 = 6 := by
    rw [show 17565886796 = 2 ^ 2 * 4391471699 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 4391471699 (by native_decide)]
    norm_num
  have hs5 : sigma 0 17565886795 = 4 := by
    rw [show 17565886795 = 5 * 3513177359 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 5 (by norm_num),
      hsigma_prime 3513177359 (by native_decide)]
    norm_num
  have hs6 : sigma 0 17565886794 = 8 := by
    rw [show 17565886794 = (2 * 3) * 2927647799 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 2927647799 (by native_decide)]
    norm_num
  have hs7 : sigma 0 17565886793 = 8 := by
    rw [show 17565886793 = (7 * 13) * 193031723 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 7 (by norm_num),
      hsigma_prime 13 (by norm_num),
      hsigma_prime 193031723 (by native_decide)]
    norm_num
  have hs8 : sigma 0 17565886792 = 8 := by
    rw [show 17565886792 = 2 ^ 3 * 2195735849 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 2195735849 (by native_decide)]
    norm_num
  have hs9 : sigma 0 17565886791 = 6 := by
    rw [show 17565886791 = 3 ^ 2 * 1951765199 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_three,
      hsigma_prime 1951765199 (by native_decide)]
    norm_num
  have hs10 : sigma 0 17565886790 = 8 := by
    rw [show 17565886790 = (2 * 5) * 1756588679 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 5 (by norm_num),
      hsigma_prime 1756588679 (by native_decide)]
    norm_num
  have hs11 : sigma 0 17565886789 = 24 := by
    rw [show 17565886789 = ((11 * 37 ^ 2) * 677) * 1723 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 11 (by norm_num),
      sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 37),
      hsigma_prime 677 (by norm_num),
      hsigma_prime 1723 (by norm_num)]
    norm_num
  dsimp
  constructor
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hk10 : k ≤ 10 := hk.2
    interval_cases k <;> norm_num at * <;> omega
  constructor
  · rw [hs11]
    norm_num
  · native_decide
