import Erdos647_ShiftDepthInterface

/-!
# Erdős #647 — refined shift-15 interface

For a hypothetical candidate `n = 2520 * N`, shift 15 factors as

`n - 15 = 3 * (5 * (168 * N - 1))`.

The factor 3 is always coprime to the remaining cofactor.  The shift budget
therefore gives `σ₀(5 * (168 * N - 1)) ≤ 8`.  Resolving the first two
5-adic layers yields the following frontier:

* away from `N ≡ 2 (mod 5)`, `168 * N - 1` has at most four divisors and at
  most two distinct prime factors;
* in the first 5-adic layer, the residual cofactor is prime;
* in the second 5-adic layer, the residual cofactor is prime;
* the only branch left unresolved by this theorem is `N ≡ 32 (mod 125)`.

This is a reusable candidate refinement, not a contradiction.

The generic prime-power peeling kernel was independently prechecked by the
proof-search verifier (`kernel_pass` job
`1e95337f-a946-46e2-839c-8a1d68ba619b`) and then proved in tracked episode
`718d1350-8ff2-4069-8527-5474a1dddd16` (problem
`e12fd70e-31e9-48c6-8be8-4cd02ad2d949`).  The full two-layer shift-15
frontier was independently prechecked (`kernel_pass` job
`2868175c-9cbb-4d3b-b2fe-2c3fb237a068`) and then proved in tracked episode
`4a1060e5-3f9e-4a72-8ccf-ed7ae231d3be` (problem
`9bee03bb-dbb7-43e3-91d7-eebc2b32c0d5`).  Both tracked outcomes are
`kernel_verified` (`root_proved`).
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- Generic factor-peeling step for divisor-count budgets.  This is the
induction kernel behind every prime-adic shift refinement: once a prime-power
factor is known to be coprime to the residual cofactor, its exact divisor
count multiplies the residual divisor count. -/
theorem erdos647_sigma_zero_peel_prime_pow :
    ∀ p e m B : ℕ, Nat.Prime p → Nat.Coprime (p ^ e) m →
      ArithmeticFunction.sigma 0 (p ^ e * m) ≤ B →
      (e + 1) * ArithmeticFunction.sigma 0 m ≤ B := by
  intro p e m B hp hcop hbudget
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp] at hbudget
  exact hbudget

/-- A positive integer with at most two divisors is prime. -/
theorem erdos647_prime_of_sigma_zero_le_two :
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

/-- If `σ₀(x) ≤ 4`, then `x` has at most two distinct prime factors. -/
theorem erdos647_primeFactors_card_le_two_of_sigma_zero_le_four :
    ∀ x : ℕ, x ≠ 0 → ArithmeticFunction.sigma 0 x ≤ 4 →
      x.primeFactors.card ≤ 2 := by
  intro x hx hsigma
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
  have hthree : 3 ≤ x.primeFactors.card := by omega
  have hmono : 2 ^ 3 ≤ 2 ^ x.primeFactors.card :=
    pow_le_pow_right' (by norm_num) hthree
  norm_num at hmono
  omega

/-- The factor 3 in the shift-15 factorization is always coprime to the
remaining cofactor. -/
theorem erdos647_shift15_coprime_three :
    ∀ N : ℕ, 1 ≤ N → Nat.Coprime 3 (5 * (168 * N - 1)) := by
  intro N hN
  apply ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr
  rintro ⟨a, ha⟩
  omega

/-- Away from `N ≡ 2 (mod 5)`, the factor 5 is also coprime to the residual
cofactor. -/
theorem erdos647_shift15_coprime_five :
    ∀ N : ℕ, 1 ≤ N → N % 5 ≠ 2 → Nat.Coprime 5 (168 * N - 1) := by
  intro N hN hNres
  apply ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr
  rintro ⟨a, ha⟩
  have hmodlt : N % 5 < 5 := Nat.mod_lt N (by norm_num)
  have hdecomp := Nat.mod_add_div N 5
  apply hNres
  omega

/-- Basic shift-15 factorization and the sharp eight-divisor bound after
removing the universally coprime factor 3. -/
theorem candidate_shift15_cofactor :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      ArithmeticFunction.sigma 0 (2520 * N - 15) ≤ 17 ∧
      2520 * N - 15 = 3 * (5 * (168 * N - 1)) ∧
      Nat.Coprime 3 (5 * (168 * N - 1)) ∧
      ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) ≤ 8 := by
  intro n N hn H hnN
  have hN : 1 ≤ N := by omega
  have h15n : 15 < n := by omega
  have hbudget := full_max_implies_shift_budgets n H 15 (by omega) h15n
  have hn15 : n - 15 = 2520 * N - 15 := by omega
  rw [hn15] at hbudget
  have hfactor : 2520 * N - 15 = 3 * (5 * (168 * N - 1)) := by omega
  have hcop3 := erdos647_shift15_coprime_three N hN
  have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 15) =
      2 * ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) := by
    rw [hfactor,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop3]
    have hs3 : ArithmeticFunction.sigma 0 3 = 2 := by native_decide
    rw [hs3]
  have hcofactor : ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) ≤ 8 := by
    rw [hsigma] at hbudget
    omega
  exact ⟨hbudget, hfactor, hcop3, hcofactor⟩

/-- Exact first two 5-adic layers of the shift-15 frontier. -/
theorem candidate_shift15_five_adic_frontier :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      ((N % 5 ≠ 2 ∧
          ArithmeticFunction.sigma 0 (168 * N - 1) ≤ 4 ∧
          (168 * N - 1).primeFactors.card ≤ 2) ∨
        (∃ M : ℕ, N = 5 * M + 2 ∧ M % 5 ≠ 1 ∧
          Nat.Prime (168 * M + 67)) ∨
        (∃ Q : ℕ, N = 25 * Q + 7 ∧ Q % 5 ≠ 1 ∧
          Nat.Prime (168 * Q + 47)) ∨
        N % 125 = 32) := by
  intro n N hn H hnN
  -- Keep the capstone self-contained for tracked proof-search replay: campaign
  -- theorem references are not available across independent submissions.
  have hshift : ∀ n : ℕ,
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      ∀ k : ℕ, 0 < k → k < n →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro n H k hk0 hkn
    let f : Fin n → ℕ := fun x =>
      (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let m : Fin n := ⟨n - k, by omega⟩
    have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) H
    dsimp [f, m] at hm
    omega
  have hprime : ∀ x : ℕ, 2 ≤ x →
      ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
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
  have hcard : ∀ x : ℕ, x ≠ 0 → ArithmeticFunction.sigma 0 x ≤ 4 →
      x.primeFactors.card ≤ 2 := by
    intro x hx hsigma
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hx] at hsigma
    have hpow : 2 ^ x.primeFactors.card ≤
        ∏ p ∈ x.primeFactors, (x.factorization p + 1) := by
      apply Finset.pow_card_le_prod
      intro p hp
      have hp' : p ∈ x.factorization.support := by simpa using hp
      have hfac : x.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
      omega
    by_contra hcard'
    have hthree : 3 ≤ x.primeFactors.card := by omega
    have hmono : 2 ^ 3 ≤ 2 ^ x.primeFactors.card :=
      pow_le_pow_right' (by norm_num) hthree
    norm_num at hmono
    omega
  have hcop3 : ∀ N : ℕ, 1 ≤ N →
      Nat.Coprime 3 (5 * (168 * N - 1)) := by
    intro N hN
    apply ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr
    rintro ⟨a, ha⟩
    omega
  have hcop5 : ∀ N : ℕ, 1 ≤ N → N % 5 ≠ 2 →
      Nat.Coprime 5 (168 * N - 1) := by
    intro N hN hNres
    apply ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr
    rintro ⟨a, ha⟩
    have hmodlt : N % 5 < 5 := Nat.mod_lt N (by norm_num)
    have hdecomp := Nat.mod_add_div N 5
    apply hNres
    omega
  have hN : 1 ≤ N := by omega
  have hbase :
      ArithmeticFunction.sigma 0 (2520 * N - 15) ≤ 17 ∧
      2520 * N - 15 = 3 * (5 * (168 * N - 1)) ∧
      Nat.Coprime 3 (5 * (168 * N - 1)) ∧
      ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) ≤ 8 := by
    have h15n : 15 < n := by omega
    have hbudget := hshift n H 15 (by omega) h15n
    have hn15 : n - 15 = 2520 * N - 15 := by omega
    rw [hn15] at hbudget
    have hfactor : 2520 * N - 15 = 3 * (5 * (168 * N - 1)) := by omega
    have hcop3' := hcop3 N hN
    have hsigma : ArithmeticFunction.sigma 0 (2520 * N - 15) =
        2 * ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) := by
      rw [hfactor,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop3']
      have hs3 : ArithmeticFunction.sigma 0 3 = 2 := by native_decide
      rw [hs3]
    have hcofactor : ArithmeticFunction.sigma 0
        (5 * (168 * N - 1)) ≤ 8 := by
      rw [hsigma] at hbudget
      omega
    exact ⟨hbudget, hfactor, hcop3', hcofactor⟩
  have hbudget := hbase.2.2.2
  by_cases hNres : N % 5 = 2
  · have hNmodlt : N % 5 < 5 := Nat.mod_lt N (by norm_num)
    have hNdecomp := Nat.mod_add_div N 5
    let M := N / 5
    have hNM : N = 5 * M + 2 := by
      dsimp [M]
      omega
    by_cases hMres : M % 5 = 1
    · have hMmodlt : M % 5 < 5 := Nat.mod_lt M (by norm_num)
      have hMdecomp := Nat.mod_add_div M 5
      let Q := M / 5
      have hMQ : M = 5 * Q + 1 := by
        dsimp [Q]
        omega
      have hNQ : N = 25 * Q + 7 := by omega
      by_cases hQres : Q % 5 = 1
      · right
        right
        right
        have hQmodlt : Q % 5 < 5 := Nat.mod_lt Q (by norm_num)
        have hQdecomp := Nat.mod_add_div Q 5
        have hN125lt : N % 125 < 125 := Nat.mod_lt N (by norm_num)
        have hN125decomp := Nat.mod_add_div N 125
        omega
      · right
        right
        left
        refine ⟨Q, hNQ, hQres, ?_⟩
        have hu : 168 * N - 1 = 25 * (168 * Q + 47) := by
          rw [hNQ]
          omega
        have hfull : 5 * (168 * N - 1) =
            125 * (168 * Q + 47) := by rw [hu]; ring
        have hu2 : 2 ≤ 168 * Q + 47 := by omega
        have hnot5u : ¬ 5 ∣ 168 * Q + 47 := by
          rintro ⟨a, ha⟩
          have hQmodlt : Q % 5 < 5 := Nat.mod_lt Q (by norm_num)
          have hQdecomp := Nat.mod_add_div Q 5
          apply hQres
          omega
        have hcop5u : Nat.Coprime 5 (168 * Q + 47) :=
          ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hnot5u
        have hcop125u : Nat.Coprime 125 (168 * Q + 47) := by
          simpa using hcop5u.pow_left 3
        have hsigma : ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) =
            4 * ArithmeticFunction.sigma 0 (168 * Q + 47) := by
          rw [hfull,
            ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
              hcop125u]
          have hs125 : ArithmeticFunction.sigma 0 125 = 4 := by native_decide
          rw [hs125]
        have hubudget : ArithmeticFunction.sigma 0 (168 * Q + 47) ≤ 2 := by
          rw [hsigma] at hbudget
          omega
        exact hprime _ hu2 hubudget
    · right
      left
      refine ⟨M, hNM, hMres, ?_⟩
      have ht : 168 * N - 1 = 5 * (168 * M + 67) := by
        rw [hNM]
        omega
      have hfull : 5 * (168 * N - 1) =
          25 * (168 * M + 67) := by rw [ht]; ring
      have ht2 : 2 ≤ 168 * M + 67 := by omega
      have hnot5t : ¬ 5 ∣ 168 * M + 67 := by
        rintro ⟨a, ha⟩
        have hMmodlt : M % 5 < 5 := Nat.mod_lt M (by norm_num)
        have hMdecomp := Nat.mod_add_div M 5
        apply hMres
        omega
      have hcop5t : Nat.Coprime 5 (168 * M + 67) :=
        ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr hnot5t
      have hcop25t : Nat.Coprime 25 (168 * M + 67) := by
        simpa using hcop5t.pow_left 2
      have hsigma : ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) =
          3 * ArithmeticFunction.sigma 0 (168 * M + 67) := by
        rw [hfull,
          ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25t]
        have hs25 : ArithmeticFunction.sigma 0 25 = 3 := by native_decide
        rw [hs25]
      have htbudget : ArithmeticFunction.sigma 0 (168 * M + 67) ≤ 2 := by
        rw [hsigma] at hbudget
        omega
      exact hprime _ ht2 htbudget
  · left
    have hr0 : 168 * N - 1 ≠ 0 := by omega
    have hcop5' := hcop5 N hN hNres
    have hsigma : ArithmeticFunction.sigma 0 (5 * (168 * N - 1)) =
        2 * ArithmeticFunction.sigma 0 (168 * N - 1) := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop5']
      have hs5 : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
      rw [hs5]
    have hrbudget : ArithmeticFunction.sigma 0 (168 * N - 1) ≤ 4 := by
      rw [hsigma] at hbudget
      omega
    exact ⟨hNres, hrbudget,
      hcard _ hr0 hrbudget⟩

end Erdos647
