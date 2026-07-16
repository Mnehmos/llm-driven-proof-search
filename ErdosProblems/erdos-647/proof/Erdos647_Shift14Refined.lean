import Erdos647_Shift13Refined

/-!
# Erdős #647 — refined shift-14 interface

For a hypothetical candidate `n = 2520 N`, shift 14 has the forced
factorization

`n - 14 = 2 * (1260 N - 7) = 2 * 7 * (180 N - 1)`.

The shift budget is at most 16.  Since the first cofactor is odd, removing
the factor 2 shows that `1260 N - 7` has at most eight divisors and at most
three distinct prime factors.  Removing the forced factor 7 gives a sharper
7-adic split:

* if `N ≢ 3 (mod 7)`, then `180 N - 1` has at most four divisors and at
  most two distinct prime factors;
* if `N ≡ 3 (mod 7)` but `N ≢ 3 (mod 49)`, then, writing `N = 7 M + 3`,
  the cofactor `180 M + 77` is prime;
* the only branch not further classified here is `N ≡ 3 (mod 49)`.

This is a reusable frontier, not a contradiction.

The direct-budget frontier was independently prechecked by the pinned
proof-search verifier (`kernel_pass`, job
`bbd9c68e-bece-4de3-82f3-5e729641d81d`) and then proved through the tracked
pipeline:

* problem version: `0524467f-fcdf-45ea-a439-7c0709a50d95`;
* episode: `0ccca717-0a99-42b3-82cb-7011619cfb73`;
* root statement hash:
  `b00329953936283eece7db3d82fac498f5621564f38fb01b7455f92be39fde41`;
* outcome: `kernel_verified` (`root_proved`).
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- A positive integer with at most two divisors is prime. -/
theorem prime_of_two_le_of_sigma_zero_le_two :
    ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
  intro x hx hs
  rw [ArithmeticFunction.sigma_zero_apply] at hs
  have hx0 : x ≠ 0 := by omega
  have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Nat.mem_divisors]
    rcases hy with rfl | rfl
    · exact ⟨one_dvd _, hx0⟩
    · exact ⟨dvd_rfl, hx0⟩
  have hc2 : ({1, x} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have heq : x.divisors = {1, x} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
  rw [Nat.prime_def_lt]
  refine ⟨by omega, ?_⟩
  intro m hmlt hmdvd
  have hmem : m ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
  rw [heq] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact h1
  · omega

/-- The basic shift-14 factorization and cofactor bounds, isolated from the
candidate interface. -/
theorem shift14_budget_cofactor :
    ∀ N : ℕ, 1 ≤ N →
      ArithmeticFunction.sigma 0 (2520 * N - 14) ≤ 16 →
      ArithmeticFunction.sigma 0 (2520 * N - 14) ≤ 16 ∧
      2520 * N - 14 = 2 * (1260 * N - 7) ∧
      Odd (1260 * N - 7) ∧
      ArithmeticFunction.sigma 0 (1260 * N - 7) ≤ 8 ∧
      (1260 * N - 7).primeFactors.card ≤ 3 ∧
      1260 * N - 7 = 7 * (180 * N - 1) := by
  intro N hN hbudget
  have hfull : 2520 * N - 14 = 2 * (1260 * N - 7) := by omega
  have hqpos : 0 < 1260 * N - 7 := by omega
  have hqodd : Odd (1260 * N - 7) := by
    refine ⟨630 * N - 4, by omega⟩
  have hnot2 : ¬ 2 ∣ 1260 * N - 7 := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hqodd
    omega
  have hcop2 : Nat.Coprime 2 (1260 * N - 7) :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2
  have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 14) =
      2 * ArithmeticFunction.sigma 0 (1260 * N - 7) := by
    rw [hfull,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2]
    have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
    rw [hs2]
  have hqbudget : ArithmeticFunction.sigma 0 (1260 * N - 7) ≤ 8 := by
    rw [hsigma] at hbudget
    omega
  have hq0 : 1260 * N - 7 ≠ 0 := by omega
  refine ⟨hbudget, hfull, hqodd, hqbudget,
    primeFactors_card_le_of_sigma_zero_lt_two_pow _ 3 hq0
      (by norm_num; omega), by omega⟩

/-- Candidate-facing form of the basic shift-14 cofactor theorem. -/
theorem candidate_shift14_cofactor :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      ArithmeticFunction.sigma 0 (2520 * N - 14) ≤ 16 ∧
      2520 * N - 14 = 2 * (1260 * N - 7) ∧
      Odd (1260 * N - 7) ∧
      ArithmeticFunction.sigma 0 (1260 * N - 7) ≤ 8 ∧
      (1260 * N - 7).primeFactors.card ≤ 3 ∧
      1260 * N - 7 = 7 * (180 * N - 1) := by
  intro n N hn H hnN
  have hN : 1 ≤ N := by omega
  have hbudget := full_max_implies_shift_budgets n H 14 (by omega) (by omega)
  have hn14 : n - 14 = 2520 * N - 14 := by omega
  rw [hn14] at hbudget
  exact shift14_budget_cofactor N hN hbudget

/-- The exact first two 7-adic layers of the shift-14 frontier, assuming only
the numerical shift-14 budget. -/
theorem shift14_budget_seven_adic_frontier :
    ∀ N : ℕ, 1 ≤ N →
      ArithmeticFunction.sigma 0 (2520 * N - 14) ≤ 16 →
      ((N % 7 ≠ 3 ∧
          ArithmeticFunction.sigma 0 (180 * N - 1) ≤ 4 ∧
          (180 * N - 1).primeFactors.card ≤ 2) ∨
        N % 49 = 3 ∨
        ∃ M : ℕ, N = 7 * M + 3 ∧ M % 7 ≠ 0 ∧
          Nat.Prime (180 * M + 77) ∧
          (N % 49 = 10 ∨ N % 49 = 17 ∨ N % 49 = 24 ∨
            N % 49 = 31 ∨ N % 49 = 38 ∨ N % 49 = 45)) := by
  intro N hN hbudget
  have hbase := shift14_budget_cofactor N hN hbudget
  have hqbudget := hbase.2.2.2.1
  have hqfactor := hbase.2.2.2.2.2
  by_cases hNres : N % 7 = 3
  · have hNmodlt : N % 7 < 7 := Nat.mod_lt N (by norm_num)
    have hNdecomp := Nat.mod_add_div N 7
    let M := N / 7
    have hNM : N = 7 * M + 3 := by
      dsimp [M]
      omega
    by_cases hMres : M % 7 = 0
    · exact Or.inr <| Or.inl <| by
        have hMdecomp := Nat.mod_add_div M 7
        have hN49lt : N % 49 < 49 := Nat.mod_lt N (by norm_num)
        have hN49decomp := Nat.mod_add_div N 49
        omega
    · right
      right
      refine ⟨M, hNM, hMres, ?_, ?_⟩
      · have htpos : 2 ≤ 180 * M + 77 := by omega
        have hnot7t : ¬ 7 ∣ 180 * M + 77 := by
          rintro ⟨a, ha⟩
          have hMmodlt : M % 7 < 7 := Nat.mod_lt M (by norm_num)
          have hMdecomp := Nat.mod_add_div M 7
          apply hMres
          omega
        have hcop7t : Nat.Coprime 7 (180 * M + 77) :=
          ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr hnot7t
        have hcop49t : Nat.Coprime 49 (180 * M + 77) := by
          simpa using hcop7t.pow_left 2
        have hq49 : 1260 * N - 7 = 49 * (180 * M + 77) := by
          rw [hNM]
          omega
        have hsigma49 : ArithmeticFunction.sigma 0 (1260 * N - 7) =
            3 * ArithmeticFunction.sigma 0 (180 * M + 77) := by
          rw [hq49,
            ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop49t]
          have hs49 : ArithmeticFunction.sigma 0 49 = 3 := by native_decide
          rw [hs49]
        have htbudget : ArithmeticFunction.sigma 0 (180 * M + 77) ≤ 2 := by
          rw [hsigma49] at hqbudget
          omega
        exact prime_of_two_le_of_sigma_zero_le_two _ htpos htbudget
      · have hMmodlt : M % 7 < 7 := Nat.mod_lt M (by norm_num)
        have hMdecomp := Nat.mod_add_div M 7
        have hN49lt : N % 49 < 49 := Nat.mod_lt N (by norm_num)
        have hN49decomp := Nat.mod_add_div N 49
        omega
  · left
    have hrpos : 0 < 180 * N - 1 := by omega
    have hnot7r : ¬ 7 ∣ 180 * N - 1 := by
      rintro ⟨a, ha⟩
      have hNmodlt : N % 7 < 7 := Nat.mod_lt N (by norm_num)
      have hNdecomp := Nat.mod_add_div N 7
      apply hNres
      omega
    have hcop7r : Nat.Coprime 7 (180 * N - 1) :=
      ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr hnot7r
    have hsigma7 : ArithmeticFunction.sigma 0 (1260 * N - 7) =
        2 * ArithmeticFunction.sigma 0 (180 * N - 1) := by
      rw [hqfactor,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop7r]
      have hs7 : ArithmeticFunction.sigma 0 7 = 2 := by native_decide
      rw [hs7]
    have hrbudget : ArithmeticFunction.sigma 0 (180 * N - 1) ≤ 4 := by
      rw [hsigma7] at hqbudget
      omega
    exact ⟨hNres, hrbudget,
      primeFactors_card_le_of_sigma_zero_lt_two_pow _ 2 (by omega)
        (by norm_num; omega)⟩

/-- Candidate-facing form of the exact first two 7-adic layers. -/
theorem candidate_shift14_seven_adic_frontier :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      ((N % 7 ≠ 3 ∧
          ArithmeticFunction.sigma 0 (180 * N - 1) ≤ 4 ∧
          (180 * N - 1).primeFactors.card ≤ 2) ∨
        N % 49 = 3 ∨
        ∃ M : ℕ, N = 7 * M + 3 ∧ M % 7 ≠ 0 ∧
          Nat.Prime (180 * M + 77) ∧
          (N % 49 = 10 ∨ N % 49 = 17 ∨ N % 49 = 24 ∨
            N % 49 = 31 ∨ N % 49 = 38 ∨ N % 49 = 45)) := by
  intro n N hn H hnN
  have hN : 1 ≤ N := by omega
  have hbudget := full_max_implies_shift_budgets n H 14 (by omega) (by omega)
  have hn14 : n - 14 = 2520 * N - 14 := by omega
  rw [hn14] at hbudget
  exact shift14_budget_seven_adic_frontier N hN hbudget

end Erdos647
