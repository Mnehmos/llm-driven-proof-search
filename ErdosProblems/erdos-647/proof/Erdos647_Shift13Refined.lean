import Erdos647_ShiftDepthInterface

/-!
# Erdős #647 — refined shift-13 interface

The shift-13 budget is `σ₀(2520 N - 13) ≤ 15`.  Unlike the earlier
fixed-factor shifts, 13 need not divide `2520 N - 13`, so the useful generic
classification is by the number of distinct prime factors.  A divisor count
at most 15 permits at most three distinct prime factors.

The reusable power-of-two/cardinality lemma and the final 13-adic frontier
were independently prechecked by the proof-search verifier (`kernel_pass`
jobs `3cdb7844-20ad-48c4-96c5-7cc944a50b96` and
`11b055f2-5165-4b68-8c92-24c88c6df290`) and then proved through tracked
episodes:

* generic lemma: problem `0da6c01d-4e97-4b86-96f8-52e95b3b70db`, episode
  `9499a13b-25db-45f6-a492-8b357900aade`;
* 13-adic frontier: problem `284723a7-d5b3-4417-b8d2-84dca18bf894`, episode
  `1e79ece8-14f0-43d2-b24a-f5cb43152f38`.

Both tracked outcomes are `kernel_verified` (`root_proved`).  The middle
candidate theorem was source-checked as part of this file and the final
tracked frontier rederived its needed shift budget directly from the original
maximum condition, so the tracked result does not rely on an unverified local
bridge.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- If `σ₀(x)` is below the next power of two, then `x` has at most the
corresponding number of distinct prime factors. -/
theorem primeFactors_card_le_of_sigma_zero_lt_two_pow :
    ∀ x r : ℕ, x ≠ 0 →
      ArithmeticFunction.sigma 0 x < 2 ^ (r + 1) →
      x.primeFactors.card ≤ r := by
  intro x r hx hsigma
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hx] at hsigma
  have hpow : 2 ^ x.primeFactors.card ≤
      ∏ p ∈ x.primeFactors, (x.factorization p + 1) := by
    apply Finset.pow_card_le_prod
    intro p hp
    have hp' : p ∈ x.factorization.support := by
      simpa using hp
    have hfac : x.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    omega
  by_contra hcard
  have hsucc : r + 1 ≤ x.primeFactors.card := by omega
  have hmono : 2 ^ (r + 1) ≤ 2 ^ x.primeFactors.card :=
    pow_le_pow_right' (by norm_num) hsucc
  omega

/-- Every hypothetical candidate's shift-13 value has at most three distinct
prime factors, avoids the four primes already forced into `2520`, and is
divisible by 13 exactly when the reindexing parameter is. -/
theorem candidate_shift13_refined :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      ArithmeticFunction.sigma 0 (2520 * N - 13) ≤ 15 ∧
      (2520 * N - 13).primeFactors.card ≤ 3 ∧
      ¬ 2 ∣ 2520 * N - 13 ∧
      ¬ 3 ∣ 2520 * N - 13 ∧
      ¬ 5 ∣ 2520 * N - 13 ∧
      ¬ 7 ∣ 2520 * N - 13 ∧
      (13 ∣ 2520 * N - 13 ↔ 13 ∣ N) := by
  intro n N hn H hnN
  have hN : 1 ≤ N := by omega
  have h13n : 13 < n := by omega
  have hbudget := full_max_implies_shift_budgets n H 13 (by omega) h13n
  have hvalue : n - 13 = 2520 * N - 13 := by omega
  rw [hvalue] at hbudget
  have hx0 : 2520 * N - 13 ≠ 0 := by omega
  refine ⟨hbudget,
    primeFactors_card_le_of_sigma_zero_lt_two_pow _ 3 hx0 (by norm_num; omega),
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, ha⟩
    omega
  · rintro ⟨a, ha⟩
    omega
  · rintro ⟨a, ha⟩
    omega
  · rintro ⟨a, ha⟩
    omega
  · constructor
    · intro h13
      have hsum : (2520 * N - 13) + 13 = 2520 * N := by omega
      have hprod : 13 ∣ 2520 * N := by
        rw [← hsum]
        exact dvd_add h13 (dvd_refl 13)
      have h13prime : Nat.Prime 13 := by norm_num
      rcases h13prime.dvd_mul.mp hprod with hbad | hN13
      · norm_num at hbad
      · exact hN13
    · rintro ⟨M, hM⟩
      have hMpos : 1 ≤ M := by omega
      refine ⟨2520 * M - 1, ?_⟩
      rw [hM]
      omega

/-- Exact first 13-adic split for shift 13.  Either 13 does not divide `N`,
or `N = 13 M`; in that latter branch the unique exceptional lift is
`M ≡ 6 (mod 13)` (equivalently `N ≡ 78 (mod 169)`).  Outside that residue,
removing the forced factor 13 leaves a cofactor with at most seven divisors
and at most two distinct prime factors. -/
theorem candidate_shift13_adic_frontier :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      (¬ 13 ∣ N) ∨
      ∃ M : ℕ, N = 13 * M ∧
        (M % 13 = 6 ∨
          (ArithmeticFunction.sigma 0 (2520 * M - 1) ≤ 7 ∧
            (2520 * M - 1).primeFactors.card ≤ 2)) := by
  intro n N hn H hnN
  by_cases h13N : 13 ∣ N
  · right
    obtain ⟨M, hNM⟩ := h13N
    refine ⟨M, hNM, ?_⟩
    by_cases hMres : M % 13 = 6
    · exact Or.inl hMres
    right
    have hN : 1 ≤ N := by omega
    have hM : 1 ≤ M := by omega
    have hfront := candidate_shift13_refined n N hn H hnN
    have hbudget := hfront.1
    have hx : 2520 * N - 13 = 13 * (2520 * M - 1) := by
      rw [hNM]
      omega
    have hr0 : 2520 * M - 1 ≠ 0 := by omega
    have hnot13 : ¬ 13 ∣ 2520 * M - 1 := by
      rintro ⟨a, ha⟩
      have hmodlt : M % 13 < 13 := Nat.mod_lt M (by norm_num)
      have hdecomp := Nat.mod_add_div M 13
      apply hMres
      omega
    have h13prime : Nat.Prime 13 := by norm_num
    have hcop : Nat.Coprime 13 (2520 * M - 1) :=
      (h13prime.coprime_iff_not_dvd).mpr hnot13
    have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 13) =
        2 * ArithmeticFunction.sigma 0 (2520 * M - 1) := by
      rw [hx, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
      have hs13 : ArithmeticFunction.sigma 0 13 = 2 := by native_decide
      rw [hs13]
    rw [hsigma] at hbudget
    have hcofactor : ArithmeticFunction.sigma 0 (2520 * M - 1) ≤ 7 := by
      omega
    exact ⟨hcofactor,
      primeFactors_card_le_of_sigma_zero_lt_two_pow _ 2 hr0 (by norm_num; omega)⟩
  · exact Or.inl h13N

end Erdos647
