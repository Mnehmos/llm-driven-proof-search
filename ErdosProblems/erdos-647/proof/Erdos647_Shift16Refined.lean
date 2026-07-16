import Erdos647_Shift14Refined
import Erdos647_ShiftFactorFramework

/-!
# Erdős #647 — family-sensitive shift-16 frontier

For a hypothetical candidate `n = 2520 N`, shift 16 has the factorization

`n - 16 = 8 * (315 N - 2)`.

The parity of `N`, already determined by the two Hughes prime-chain families,
therefore controls the first useful 2-adic layer.

* If `N` is odd (family B), `315 N - 2` is odd.  The shift budget at most 18
  and `sigma₀(8) = 4` force `sigma₀(315 N - 2) ≤ 4`.
* If `N = 2 M` (family A), then `n - 16 = 16 * (315 M - 1)`.  Successively
  peeling the exact powers of two gives three useful branches and one honest
  unresolved residue: `M` even, `M ≡ 1 (mod 4)`, `M ≡ 7 (mod 8)`, or
  `M ≡ 3 (mod 8)`.  In the first two branches the remaining odd cofactor has
  at most three divisors; in the third it is prime.

This is a refinement, not a contradiction.  The final residue records where
the 2-adic peeling must continue if shift 16 is pursued further.

The reusable part of the argument is already covered by generic APIs:
`ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime` removes an
exact coprime power of two, and
`primeFactors_card_le_of_sigma_zero_lt_two_pow` turns the resulting divisor
budget into a distinct-prime-factor bound.  The genuinely shift- and
family-specific input is precisely the congruence work that chooses the exact
power of two and the parity tags supplied by the two prime-chain families.

The strongest even-parameter arithmetic core (including all four branches,
the divisor bounds, and primality in the `M ≡ 7 (mod 8)` branch) was also
checked independently by the pinned proof-search verifier: job
`9d45701f-7e1e-45bc-8cd2-6c5b4be6906f`, outcome `kernel_pass`.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- The shift-16 budget and its basic factorization. -/
theorem candidate_shift16_base :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      ArithmeticFunction.sigma 0 (2520 * N - 16) ≤ 18 ∧
      2520 * N - 16 = 8 * (315 * N - 2) := by
  intro n N hn H hnN
  have hbudget := full_max_implies_shift_budgets n H 16 (by omega) (by omega)
  have hvalue : n - 16 = 2520 * N - 16 := by omega
  rw [hvalue] at hbudget
  exact ⟨hbudget, by omega⟩

/-- In the odd-parameter (family B) branch, the shift-16 cofactor has at most
four divisors and at most two distinct prime factors. -/
theorem candidate_shift16_odd_parameter :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → N % 2 = 1 →
      Odd (315 * N - 2) ∧
      ArithmeticFunction.sigma 0 (315 * N - 2) ≤ 4 ∧
      (315 * N - 2).primeFactors.card ≤ 2 := by
  intro n N hn H hnN hNodd
  have hN : 1 ≤ N := by omega
  have hNdecomp := Nat.mod_add_div N 2
  have hqodd : Odd (315 * N - 2) := by
    refine ⟨315 * (N / 2) + 156, ?_⟩
    omega
  have hnot2 : ¬ 2 ∣ 315 * N - 2 := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hqodd
    omega
  have hcop2 : Nat.Coprime 2 (315 * N - 2) :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2
  have hcop8 : Nat.Coprime 8 (315 * N - 2) := by
    simpa using hcop2.pow_left 3
  have hnfactor : n - 16 = 2 ^ 3 * (315 * N - 2) := by
    rw [hnN]
    norm_num
    omega
  have hqbudget : ArithmeticFunction.sigma 0 (315 * N - 2) ≤ 4 := by
    have h := candidate_shift_prime_power_peel n 16 2 3 (315 * N - 2)
      H (by omega) (by omega) Nat.prime_two hnfactor (by simpa using hcop8)
    norm_num at h ⊢
    exact h
  refine ⟨hqodd, hqbudget, ?_⟩
  exact candidate_shift_prime_power_omega_le n 16 2 3 (315 * N - 2) 2
    H (by omega) (by omega) Nat.prime_two hnfactor (by simpa using hcop8)
      (by omega) (by norm_num)

/-- In the even-parameter (family A) branch, write `N = 2 M` and expose the
first three exact 2-adic layers.  The final `M ≡ 3 (mod 8)` branch is the
honest higher-valuation remainder. -/
theorem candidate_shift16_even_parameter :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → N % 2 = 0 →
      ∃ M : ℕ, N = 2 * M ∧
        ((M % 2 = 0 ∧
            Odd (315 * M - 1) ∧
            ArithmeticFunction.sigma 0 (315 * M - 1) ≤ 3 ∧
            (315 * M - 1).primeFactors.card ≤ 1) ∨
          (M % 4 = 1 ∧
            ∃ t : ℕ, 315 * M - 1 = 2 * t ∧ Odd t ∧
              ArithmeticFunction.sigma 0 t ≤ 3 ∧
              t.primeFactors.card ≤ 1) ∨
          (M % 8 = 7 ∧
            ∃ u : ℕ, 315 * M - 1 = 4 * u ∧ Odd u ∧ Nat.Prime u) ∨
          M % 8 = 3) := by
  intro n N hn H hnN hNeven
  have hN : 1 ≤ N := by omega
  have hNdecomp := Nat.mod_add_div N 2
  let M := N / 2
  have hNM : N = 2 * M := by
    dsimp [M]
    omega
  have hM : 1 ≤ M := by omega
  refine ⟨M, hNM, ?_⟩
  have hnfull16 : n - 16 = 2 ^ 4 * (315 * M - 1) := by
    rw [hnN, hNM]
    norm_num
    omega
  by_cases hMeven : M % 2 = 0
  · left
    have hMdecomp := Nat.mod_add_div M 2
    have hrodd : Odd (315 * M - 1) := by
      refine ⟨315 * (M / 2) - 1, ?_⟩
      omega
    have hnot2 : ¬ 2 ∣ 315 * M - 1 := by
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := hrodd
      omega
    have hcop2 : Nat.Coprime 2 (315 * M - 1) :=
      (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2
    have hcop16 : Nat.Coprime 16 (315 * M - 1) := by
      simpa using hcop2.pow_left 4
    have hrbudget : ArithmeticFunction.sigma 0 (315 * M - 1) ≤ 3 := by
      have h := candidate_shift_prime_power_peel n 16 2 4 (315 * M - 1)
        H (by omega) (by omega) Nat.prime_two hnfull16 (by simpa using hcop16)
      norm_num at h ⊢
      exact h
    exact ⟨hMeven, hrodd, hrbudget,
      candidate_shift_prime_power_omega_le n 16 2 4 (315 * M - 1) 1
        H (by omega) (by omega) Nat.prime_two hnfull16
          (by simpa using hcop16) (by omega) (by norm_num)⟩
  · have hMmod2lt : M % 2 < 2 := Nat.mod_lt M (by norm_num)
    have hModd : M % 2 = 1 := by omega
    by_cases hM4 : M % 4 = 1
    · right
      left
      have hM4lt : M % 4 < 4 := Nat.mod_lt M (by norm_num)
      have hM4decomp := Nat.mod_add_div M 4
      let t := 630 * (M / 4) + 157
      have hrt : 315 * M - 1 = 2 * t := by
        dsimp [t]
        omega
      have htodd : Odd t := by
        refine ⟨315 * (M / 4) + 78, ?_⟩
        dsimp [t]
        omega
      have hnot2t : ¬ 2 ∣ t := by
        rintro ⟨a, ha⟩
        obtain ⟨b, hb⟩ := htodd
        omega
      have hcop2t : Nat.Coprime 2 t :=
        (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2t
      have hcop32t : Nat.Coprime 32 t := by
        simpa using hcop2t.pow_left 5
      have hnfull32 : n - 16 = 2 ^ 5 * t := by
        rw [hnfull16, hrt]
        norm_num
        ring
      have htbudget : ArithmeticFunction.sigma 0 t ≤ 3 := by
        have h := candidate_shift_prime_power_peel n 16 2 5 t H
          (by omega) (by omega) Nat.prime_two hnfull32 (by simpa using hcop32t)
        norm_num at h ⊢
        exact h
      exact ⟨hM4, t, hrt, htodd, htbudget,
        candidate_shift_prime_power_omega_le n 16 2 5 t 1 H
          (by omega) (by omega) Nat.prime_two hnfull32
            (by simpa using hcop32t) (by omega) (by norm_num)⟩
    · have hM4lt : M % 4 < 4 := Nat.mod_lt M (by norm_num)
      have hM4decomp := Nat.mod_add_div M 4
      have hM4eq : M % 4 = 3 := by omega
      by_cases hM8 : M % 8 = 7
      · right
        right
        left
        have hM8lt : M % 8 < 8 := Nat.mod_lt M (by norm_num)
        have hM8decomp := Nat.mod_add_div M 8
        let u := 630 * (M / 8) + 551
        have hru : 315 * M - 1 = 4 * u := by
          dsimp [u]
          omega
        have huodd : Odd u := by
          refine ⟨315 * (M / 8) + 275, ?_⟩
          dsimp [u]
          omega
        have hnot2u : ¬ 2 ∣ u := by
          rintro ⟨a, ha⟩
          obtain ⟨b, hb⟩ := huodd
          omega
        have hcop2u : Nat.Coprime 2 u :=
          (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2u
        have hcop64u : Nat.Coprime 64 u := by
          simpa using hcop2u.pow_left 6
        have hnfull64 : n - 16 = 2 ^ 6 * u := by
          rw [hnfull16, hru]
          norm_num
          ring
        have hubudget : ArithmeticFunction.sigma 0 u ≤ 2 := by
          have h := candidate_shift_prime_power_peel n 16 2 6 u H
            (by omega) (by omega) Nat.prime_two hnfull64 (by simpa using hcop64u)
          norm_num at h ⊢
          exact h
        exact ⟨hM8, u, hru, huodd,
          prime_of_two_le_of_sigma_zero_le_two u (by omega) hubudget⟩
      · right
        right
        right
        have hM8lt : M % 8 < 8 := Nat.mod_lt M (by norm_num)
        have hM8decomp := Nat.mod_add_div M 8
        omega

/-- The family-sensitive shift-16 frontier, stated directly in terms of the
parity tag already forced by the two prime-chain families. -/
theorem candidate_shift16_parameter_frontier :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      ((N % 2 = 1 ∧
          ArithmeticFunction.sigma 0 (315 * N - 2) ≤ 4 ∧
          (315 * N - 2).primeFactors.card ≤ 2) ∨
        (N % 2 = 0 ∧
          ∃ M : ℕ, N = 2 * M ∧
            ((M % 2 = 0 ∧
                ArithmeticFunction.sigma 0 (315 * M - 1) ≤ 3 ∧
                (315 * M - 1).primeFactors.card ≤ 1) ∨
              (M % 4 = 1 ∧
                ∃ t : ℕ, 315 * M - 1 = 2 * t ∧
                  ArithmeticFunction.sigma 0 t ≤ 3 ∧
                  t.primeFactors.card ≤ 1) ∨
              (M % 8 = 7 ∧
                ∃ u : ℕ, 315 * M - 1 = 4 * u ∧ Nat.Prime u) ∨
              M % 8 = 3))) := by
  intro n N hn H hnN
  have hmodlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
  by_cases hodd : N % 2 = 1
  · left
    have h := candidate_shift16_odd_parameter n N hn H hnN hodd
    exact ⟨hodd, h.2.1, h.2.2⟩
  · have heven : N % 2 = 0 := by omega
    right
    refine ⟨heven, ?_⟩
    obtain ⟨M, hNM, hfront⟩ :=
      candidate_shift16_even_parameter n N hn H hnN heven
    refine ⟨M, hNM, ?_⟩
    rcases hfront with h0 | h1 | h7 | h3
    · exact Or.inl ⟨h0.1, h0.2.2.1, h0.2.2.2⟩
    · exact Or.inr <| Or.inl ⟨h1.1, h1.2.choose, h1.2.choose_spec.1,
        h1.2.choose_spec.2.2.1, h1.2.choose_spec.2.2.2⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨h7.1, h7.2.choose,
        h7.2.choose_spec.1, h7.2.choose_spec.2.2⟩
    · exact Or.inr <| Or.inr <| Or.inr h3

/-- Family B supplies exactly the odd-parameter hypothesis used by the
shift-16 cofactor bound. -/
theorem candidate_shift16_familyB :
    ∀ n N s : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → n = 16 * s + 8 →
      N % 2 = 1 ∧
      ArithmeticFunction.sigma 0 (315 * N - 2) ≤ 4 ∧
      (315 * N - 2).primeFactors.card ≤ 2 := by
  intro n N s hn H hnN hfamily
  have hN : 1 ≤ N := by omega
  have hodd : N % 2 = 1 := by
    have hmodlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
    have hNdecomp := Nat.mod_add_div N 2
    omega
  have hfront := candidate_shift16_odd_parameter n N hn H hnN hodd
  exact ⟨hodd, hfront.2.1, hfront.2.2⟩

/-- Family A supplies exactly the even-parameter hypothesis used by the
shift-16 2-adic frontier.  Primality of its family parameter is needed only
to exclude the exceptional even prime when deriving this parity tag. -/
theorem candidate_shift16_familyA :
    ∀ n N s : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N → Nat.Prime s → n = 8 * s + 8 →
      N % 2 = 0 ∧
      ∃ M : ℕ, N = 2 * M ∧
        ((M % 2 = 0 ∧
            ArithmeticFunction.sigma 0 (315 * M - 1) ≤ 3 ∧
            (315 * M - 1).primeFactors.card ≤ 1) ∨
          (M % 4 = 1 ∧
            ∃ t : ℕ, 315 * M - 1 = 2 * t ∧
              ArithmeticFunction.sigma 0 t ≤ 3 ∧
              t.primeFactors.card ≤ 1) ∨
          (M % 8 = 7 ∧
            ∃ u : ℕ, 315 * M - 1 = 4 * u ∧ Nat.Prime u) ∨
          M % 8 = 3) := by
  intro n N s hn H hnN hs hfamily
  have hN : 1 ≤ N := by omega
  have heven : N % 2 = 0 := by
    by_cases h0 : N % 2 = 0
    · exact h0
    have hmodlt : N % 2 < 2 := Nat.mod_lt N (by norm_num)
    have hodd : N % 2 = 1 := by omega
    have hNdecomp := Nat.mod_add_div N 2
    rcases hs.eq_two_or_odd' with htwo | hsodd
    · rw [htwo] at hfamily
      omega
    · obtain ⟨r, hr⟩ := hsodd
      omega
  refine ⟨heven, ?_⟩
  obtain ⟨M, hNM, hfront⟩ :=
    candidate_shift16_even_parameter n N hn H hnN heven
  refine ⟨M, hNM, ?_⟩
  rcases hfront with h0 | h1 | h7 | h3
  · exact Or.inl ⟨h0.1, h0.2.2.1, h0.2.2.2⟩
  · exact Or.inr <| Or.inl ⟨h1.1, h1.2.choose, h1.2.choose_spec.1,
      h1.2.choose_spec.2.2.1, h1.2.choose_spec.2.2.2⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨h7.1, h7.2.choose,
      h7.2.choose_spec.1, h7.2.choose_spec.2.2⟩
  · exact Or.inr <| Or.inr <| Or.inr h3

end Erdos647
