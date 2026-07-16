import Mathlib

open ArithmeticFunction

/-!
# Erdős #647 — exact depth-15 frontier witness

For `N = 1,609,299,930,876` and `n = 2520N = 4,055,435,825,807,520`,
all seven linear forms used by the density theorem are prime and every
divisor-count budget through shift 15 holds.  Shift 16 fails, with
`σ₀(n - 16) = 40 > 18`.

This is a negative search certificate, not a candidate for Erdős #647.  It
kernel-certifies that the seven-form prime tuple and all shift constraints
through 15 remain jointly consistent, so no closure argument using only those
constraints can suffice.  The computational search supplied the integer and
factorizations; the theorem below independently checks every arithmetic fact.

Direct evaluation of `Nat.divisors` at this scale is inappropriate.  The
proof instead exposes complete prime factorizations and uses multiplicativity
of `sigma`, leaving concrete primality and coprimality decisions to native
evaluation.

Proof-search provenance for the complete budget/exact-failure/prime
certificate:

* verification job `acbab4bb-5da2-452d-99be-1220f28eaf99`:
  `kernel_pass`;
* problem version `5877a4da-5df9-44f3-8f53-76835eb3a6c6`;
* episode `5378a703-7458-4156-a4fc-547b3f11c93f`:
  `kernel_verified` (`root_proved`);
* root statement hash
  `8eb21142f84a5baab8ce0c3787b93cdf0b6c744c130c8265a72bd503af632a6f`.
-/

theorem erdos647_survives_fifteen_fails_sixteen :
    let N : ℕ := 1609299930876
    let n : ℕ := 2520 * N
    (∀ k ∈ Finset.Icc 1 15, sigma 0 (n - k) ≤ k + 2) ∧
      sigma 0 (n - 16) = 40 ∧
      18 < sigma 0 (n - 16) ∧
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
  have hs1 : sigma 0 4055435825807519 = 2 :=
    hsigma_prime 4055435825807519 (by native_decide)
  have hs2 : sigma 0 4055435825807518 = 4 := by
    rw [show 4055435825807518 = 2 * 2027717912903759 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 2027717912903759 (by native_decide)]
    norm_num
  have hs3 : sigma 0 4055435825807517 = 4 := by
    rw [show 4055435825807517 = 3 * 1351811941935839 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 1351811941935839 (by native_decide)]
    norm_num
  have hs4 : sigma 0 4055435825807516 = 6 := by
    rw [show 4055435825807516 = 2 ^ 2 * 1013858956451879 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 1013858956451879 (by native_decide)]
    norm_num
  have hs5 : sigma 0 4055435825807515 = 4 := by
    rw [show 4055435825807515 = 5 * 811087165161503 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 5 (by norm_num),
      hsigma_prime 811087165161503 (by native_decide)]
    norm_num
  have hs6 : sigma 0 4055435825807514 = 8 := by
    rw [show 4055435825807514 = (2 * 3) * 675905970967919 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 675905970967919 (by native_decide)]
    norm_num
  have hs7 : sigma 0 4055435825807513 = 8 := by
    rw [show 4055435825807513 = (7 * 43) * 13473208723613 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 7 (by norm_num),
      hsigma_prime 43 (by norm_num),
      hsigma_prime 13473208723613 (by native_decide)]
    norm_num
  have hs8 : sigma 0 4055435825807512 = 8 := by
    rw [show 4055435825807512 = 2 ^ 3 * 506929478225939 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 506929478225939 (by native_decide)]
    norm_num
  have hs9 : sigma 0 4055435825807511 = 6 := by
    rw [show 4055435825807511 = 3 ^ 2 * 450603980645279 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_three,
      hsigma_prime 450603980645279 (by native_decide)]
    norm_num
  have hs10 : sigma 0 4055435825807510 = 8 := by
    rw [show 4055435825807510 = (2 * 5) * 405543582580751 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 5 (by norm_num),
      hsigma_prime 405543582580751 (by native_decide)]
    norm_num
  have hs11 : sigma 0 4055435825807509 = 8 := by
    rw [show 4055435825807509 = (11 * 13) * 28359691089563 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 11 (by norm_num),
      hsigma_prime 13 (by norm_num),
      hsigma_prime 28359691089563 (by native_decide)]
    norm_num
  have hs12 : sigma 0 4055435825807508 = 12 := by
    rw [show 4055435825807508 = (2 ^ 2 * 3) * 337952985483959 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 337952985483959 (by native_decide)]
    norm_num
  have hs13 : sigma 0 4055435825807507 = 4 := by
    rw [show 4055435825807507 = 1409 * 2878236923923 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 1409 (by native_decide),
      hsigma_prime 2878236923923 (by native_decide)]
    norm_num
  have hs14 : sigma 0 4055435825807506 = 16 := by
    rw [show 4055435825807506 = ((2 * 7) * 19) * 15245999345141 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 2 Nat.prime_two,
      hsigma_prime 7 (by norm_num),
      hsigma_prime 19 (by norm_num),
      hsigma_prime 15245999345141 (by native_decide)]
    norm_num
  have hs15 : sigma 0 4055435825807505 = 16 := by
    rw [show 4055435825807505 = ((3 * 5) * 8831) * 30615149857 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      hsigma_prime 3 Nat.prime_three,
      hsigma_prime 5 (by norm_num),
      hsigma_prime 8831 (by native_decide),
      hsigma_prime 30615149857 (by native_decide)]
    norm_num
  have hs16 : sigma 0 4055435825807504 = 40 := by
    rw [show 4055435825807504 = (((2 ^ 4) * 17) * 392759) * 37961423 by norm_num,
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      isMultiplicative_sigma.map_mul_of_coprime (by native_decide),
      sigma_zero_apply_prime_pow Nat.prime_two,
      hsigma_prime 17 (by norm_num),
      hsigma_prime 392759 (by native_decide),
      hsigma_prime 37961423 (by native_decide)]
    norm_num
  dsimp
  constructor
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : 1 ≤ k := hk.1
    have hk15 : k ≤ 15 := hk.2
    interval_cases k <;> norm_num at * <;> omega
  constructor
  · exact hs16
  constructor
  · rw [hs16]
    norm_num
  · native_decide
