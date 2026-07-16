import Mathlib

open ArithmeticFunction

/-!
# Erdős #647 — exact depth-12 frontier witness

N = 244692464302 and n = 2520*N = 616625010041040 survive all
divisor-count budgets through shift 12 and fail first at shift 13.  Directly
evaluating `Nat.divisors` at this scale is inappropriate, so the proof exposes
the prime factorizations and uses multiplicativity of `sigma`.

Proof-search provenance for the complete budget/failure/prime certificate:

* verification job `53b29f01-0ce5-43fb-be4d-77d8b562c418`: `kernel_pass`;
* problem version `3bf407ed-5a59-49d8-9791-9cf6f73b81d8`;
* episode `3eb4731d-d0c9-4b7d-9e06-d44934b19c30`:
  `kernel_verified` (`root_proved`).

The seven-prime sub-conjunction was also independently tracked under problem
`942cd91e-ae66-46da-97f5-2cf2a39b89da`, episode
`8f021bf2-9e4b-4f46-b6b5-09e59e8c0d78`.
-/

theorem erdos647_survives_twelve_fails_thirteen :
    let N : ℕ := 244692464302
    let n : ℕ := 2520 * N
    (∀ k ∈ Finset.Icc 1 12, sigma 0 (n - k) ≤ k + 2) ∧
      15 < sigma 0 (n - 13) ∧
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
  have hs1 : sigma 0 616625010041039 = 2 :=
    hsigma_prime 616625010041039 (by native_decide)
  have hs2 : sigma 0 616625010041038 = 4 := by
    rw [show 616625010041038 = 2 * 308312505020519 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 308312505020519 (by native_decide)]
    norm_num
  have hs3 : sigma 0 616625010041037 = 4 := by
    rw [show 616625010041037 = 3 * 205541670013679 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 205541670013679 (by native_decide)]
    norm_num
  have hs4 : sigma 0 616625010041036 = 6 := by
    rw [show 616625010041036 = 2 ^ 2 * 154156252510259 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 154156252510259 (by native_decide)]
    norm_num
  have hs5 : sigma 0 616625010041035 = 4 := by
    rw [show 616625010041035 = 5 * 123325002008207 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 5 (by norm_num),
      hsigma_prime 123325002008207 (by native_decide)]
    norm_num
  have hs6 : sigma 0 616625010041034 = 8 := by
    rw [show 616625010041034 = (2 * 3) * 102770835006839 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 102770835006839 (by native_decide)]
    norm_num
  have hs7 : sigma 0 616625010041033 = 4 := by
    rw [show 616625010041033 = 7 * 88089287148719 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 7 (by norm_num),
      hsigma_prime 88089287148719 (by native_decide)]
    norm_num
  have hs8 : sigma 0 616625010041032 = 8 := by
    rw [show 616625010041032 = 2 ^ 3 * 77078126255129 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 77078126255129 (by native_decide)]
    norm_num
  have hs9 : sigma 0 616625010041031 = 10 := by
    rw [show 616625010041031 = 3 ^ 4 * 7612654444951 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_three,
      hsigma_prime 7612654444951 (by native_decide)]
    norm_num
  have hs10 : sigma 0 616625010041030 = 8 := by
    rw [show 616625010041030 = (2 * 5) * 61662501004103 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 5 (by norm_num),
      hsigma_prime 61662501004103 (by native_decide)]
    norm_num
  have hs11 : sigma 0 616625010041029 = 12 := by
    rw [show 616625010041029 = (11 ^ 2 * 167) * 30515415947 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 11),
      hsigma_prime 167 (by norm_num),
      hsigma_prime 30515415947 (by native_decide)]
    norm_num
  have hs12 : sigma 0 616625010041028 = 12 := by
    rw [show 616625010041028 = (2 ^ 2 * 3) * 51385417503419 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 51385417503419 (by native_decide)]
    norm_num
  have hs13 : sigma 0 616625010041027 = 16 := by
    rw [show 616625010041027 = ((13 * 251) * 1481) * 127599509 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 13 (by norm_num),
      hsigma_prime 251 (by norm_num),
      hsigma_prime 1481 (by native_decide),
      hsigma_prime 127599509 (by native_decide)]
    norm_num
  dsimp
  constructor
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hk12 : k ≤ 12 := hk.2
    interval_cases k <;> norm_num at * <;> omega
  constructor
  · rw [hs13]
    norm_num
  · native_decide
