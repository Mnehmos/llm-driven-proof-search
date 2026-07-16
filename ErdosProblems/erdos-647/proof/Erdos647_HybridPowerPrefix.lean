import Mathlib

set_option linter.unnecessarySeqFocus false

private theorem erdos647_hybrid_rough_cube_bound :
    ∀ m : ℕ, 1 ≤ m → (∀ p : ℕ, p.Prime → p ∣ m → 11 ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ 3 ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hrough
    by_cases h1 : m = 1
    · subst h1
      norm_num [ArithmeticFunction.sigma_zero_apply]
    · have hm2 : 2 ≤ m := by omega
      have hp : m.minFac.Prime := Nat.minFac_prime h1
      have hpd : m.minFac ∣ m := Nat.minFac_dvd m
      have hp11 : 11 ≤ m.minFac := hrough _ hp hpd
      set P := m.minFac with hPdef
      clear_value P
      obtain ⟨a, q, hqnd, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show m ≠ 0 by omega) P hp.ne_one
      have ha1 : 1 ≤ a := by
        by_contra h0
        push Not at h0
        have ha0 : a = 0 := by omega
        rw [ha0, pow_zero, one_mul] at heq
        rw [heq] at hpd
        exact hqnd hpd
      have hqpos : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at heq
          omega
        · exact h0
      have hpalt : 2 ≤ P ^ a := by
        have := Nat.le_self_pow (by omega : a ≠ 0) P
        omega
      have hqlt : q < m := by
        have h2 : 1 * q < P ^ a * q := by
          apply Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl q)
          omega
        calc q = 1 * q := (one_mul q).symm
          _ < P ^ a * q := h2
          _ = m := heq.symm
      have hqrough : ∀ p : ℕ, p.Prime → p ∣ q → 11 ≤ p := by
        intro p hpp hpq
        refine hrough p hpp ?_
        rw [heq]
        exact Dvd.dvd.mul_left hpq _
      have hIH := ih q hqlt hqpos hqrough
      have hT1 : ∀ b : ℕ, (b + 1) ^ 3 ≤ P ^ b := by
        intro b
        induction b with
        | zero => simp
        | succ k ihk =>
          have hstep : (k + 2) ^ 3 ≤ 8 * (k + 1) ^ 3 := by
            have h2 : k + 2 ≤ 2 * (k + 1) := by omega
            calc (k + 2) ^ 3 ≤ (2 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
              _ = 8 * (k + 1) ^ 3 := by ring
          calc (k + 1 + 1) ^ 3 = (k + 2) ^ 3 := by ring_nf
            _ ≤ 8 * (k + 1) ^ 3 := hstep
            _ ≤ 8 * P ^ k := Nat.mul_le_mul_left 8 ihk
            _ ≤ P * P ^ k := Nat.mul_le_mul_right _ (by omega)
            _ = P ^ (k + 1) := by rw [pow_succ]; ring
      have hcop : Nat.Coprime (P ^ a) q := Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hqnd)
      have hs : ArithmeticFunction.sigma 0 (P ^ a) = a + 1 := by
        rw [ArithmeticFunction.sigma_zero_apply, Nat.divisors_prime_pow hp,
          Finset.card_map, Finset.card_range]
      have hsig : ArithmeticFunction.sigma 0 m = (a + 1) * ArithmeticFunction.sigma 0 q := by
        rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs]
      calc (ArithmeticFunction.sigma 0 m) ^ 3
          = (a + 1) ^ 3 * (ArithmeticFunction.sigma 0 q) ^ 3 := by rw [hsig]; ring
        _ ≤ P ^ a * q := Nat.mul_le_mul (hT1 a) hIH
        _ = m := heq.symm

/-- The sharp global bound. The tracked episode's proof inlines
`erdos647_hybrid_rough_cube_bound` verbatim (cross-submission references are
unavailable to tracked replays); this snapshot states it against the
theorem above for readability of the repository artifact. -/
private theorem erdos647_hybrid_sharp_cube_divisor_bound :
    ∀ n : ℕ, 1 ≤ n → 35 * (ArithmeticFunction.sigma 0 n) ^ 3 ≤ 1536 * n := by
  intro n hn
  have L2 : ∀ a : ℕ, (a + 1) ^ 3 ≤ 8 * 2 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · push Not at hk
        have h2 : 4 * (k + 2) ≤ 5 * (k + 1) := by omega
        have h4 : 64 * (k + 2) ^ 3 ≤ 125 * (k + 1) ^ 3 := by
          calc 64 * (k + 2) ^ 3 = (4 * (k + 2)) ^ 3 := by ring
            _ ≤ (5 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 125 * (k + 1) ^ 3 := by ring
        have h5 : (k + 2) ^ 3 ≤ 2 * (k + 1) ^ 3 := by omega
        calc (k + 1 + 1) ^ 3 = (k + 2) ^ 3 := by ring_nf
          _ ≤ 2 * (k + 1) ^ 3 := h5
          _ ≤ 2 * (8 * 2 ^ k) := by omega
          _ = 8 * 2 ^ (k + 1) := by rw [pow_succ]; ring
  have L3 : ∀ b : ℕ, (b + 1) ^ 3 ≤ 3 * 3 ^ b := by
    intro b
    induction b with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 1
      · interval_cases k <;> norm_num
      · push Not at hk
        have h2 : 3 * (k + 2) ≤ 4 * (k + 1) := by omega
        have h4 : 27 * (k + 2) ^ 3 ≤ 64 * (k + 1) ^ 3 := by
          calc 27 * (k + 2) ^ 3 = (3 * (k + 2)) ^ 3 := by ring
            _ ≤ (4 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 64 * (k + 1) ^ 3 := by ring
        have h5 : (k + 2) ^ 3 ≤ 3 * (k + 1) ^ 3 := by omega
        calc (k + 1 + 1) ^ 3 = (k + 2) ^ 3 := by ring_nf
          _ ≤ 3 * (k + 1) ^ 3 := h5
          _ ≤ 3 * (3 * 3 ^ k) := by omega
          _ = 3 * 3 ^ (k + 1) := by rw [pow_succ]; ring
  have L5 : ∀ c : ℕ, 5 * (c + 1) ^ 3 ≤ 8 * 5 ^ c := by
    intro c
    induction c with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 0
      · interval_cases k
        all_goals norm_num
      · push Not at hk
        have h2 : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
        have h4 : 8 * (k + 2) ^ 3 ≤ 27 * (k + 1) ^ 3 := by
          calc 8 * (k + 2) ^ 3 = (2 * (k + 2)) ^ 3 := by ring
            _ ≤ (3 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 27 * (k + 1) ^ 3 := by ring
        have h6 : 5 * (k + 2) ^ 3 ≤ 8 * (5 * 5 ^ k) := by omega
        calc 5 * (k + 1 + 1) ^ 3 = 5 * (k + 2) ^ 3 := by ring_nf
          _ ≤ 8 * (5 * 5 ^ k) := h6
          _ = 8 * 5 ^ (k + 1) := by rw [pow_succ]; ring
  have L7 : ∀ d : ℕ, 7 * (d + 1) ^ 3 ≤ 8 * 7 ^ d := by
    intro d
    induction d with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 0
      · interval_cases k
        all_goals norm_num
      · push Not at hk
        have h2 : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
        have h4 : 8 * (k + 2) ^ 3 ≤ 27 * (k + 1) ^ 3 := by
          calc 8 * (k + 2) ^ 3 = (2 * (k + 2)) ^ 3 := by ring
            _ ≤ (3 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 27 * (k + 1) ^ 3 := by ring
        have h6 : 7 * (k + 2) ^ 3 ≤ 8 * (7 * 7 ^ k) := by omega
        calc 7 * (k + 1 + 1) ^ 3 = 7 * (k + 2) ^ 3 := by ring_nf
          _ ≤ 8 * (7 * 7 ^ k) := h6
          _ = 8 * 7 ^ (k + 1) := by rw [pow_succ]; ring
  obtain ⟨a, m1, h2m1, hd2⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show n ≠ 0 by omega) 2 (by norm_num)
  have hm1pos : 1 ≤ m1 := by
    rcases Nat.eq_zero_or_pos m1 with h0 | h0
    · rw [h0, mul_zero] at hd2
      omega
    · exact h0
  obtain ⟨b, m2, h3m2, hd3⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show m1 ≠ 0 by omega) 3 (by norm_num)
  have hm2pos : 1 ≤ m2 := by
    rcases Nat.eq_zero_or_pos m2 with h0 | h0
    · rw [h0, mul_zero] at hd3
      omega
    · exact h0
  obtain ⟨c, m3, h5m3, hd5⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show m2 ≠ 0 by omega) 5 (by norm_num)
  have hm3pos : 1 ≤ m3 := by
    rcases Nat.eq_zero_or_pos m3 with h0 | h0
    · rw [h0, mul_zero] at hd5
      omega
    · exact h0
  obtain ⟨d, m4, h7m4, hd7⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show m3 ≠ 0 by omega) 7 (by norm_num)
  have hm4pos : 1 ≤ m4 := by
    rcases Nat.eq_zero_or_pos m4 with h0 | h0
    · rw [h0, mul_zero] at hd7
      omega
    · exact h0
  have hm4d3 : m4 ∣ m3 := ⟨7 ^ d, by rw [hd7]; ring⟩
  have hm4d2 : m4 ∣ m2 := hm4d3.trans ⟨5 ^ c, by rw [hd5]; ring⟩
  have hm4d1 : m4 ∣ m1 := hm4d2.trans ⟨3 ^ b, by rw [hd3]; ring⟩
  have hrough4 : ∀ p : ℕ, p.Prime → p ∣ m4 → 11 ≤ p := by
    intro p hpp hpq
    have hp2 : p ≠ 2 := by
      intro h
      exact h2m1 (h ▸ hpq.trans hm4d1)
    have hp3 : p ≠ 3 := by
      intro h
      exact h3m2 (h ▸ hpq.trans hm4d2)
    have hp5 : p ≠ 5 := by
      intro h
      exact h5m3 (h ▸ hpq.trans hm4d3)
    have hp7 : p ≠ 7 := by
      intro h
      exact h7m4 (h ▸ hpq)
    have hge2 := hpp.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hpp (by norm_num)
    · exact hp5 rfl
    · exact absurd hpp (by norm_num)
    · exact hp7 rfl
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
  have hcore4 := erdos647_hybrid_rough_cube_bound m4 hm4pos hrough4
  have hs2 : ArithmeticFunction.sigma 0 (2 ^ a) = a + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 2), Finset.card_map, Finset.card_range]
  have hs3 : ArithmeticFunction.sigma 0 (3 ^ b) = b + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 3), Finset.card_map, Finset.card_range]
  have hs5 : ArithmeticFunction.sigma 0 (5 ^ c) = c + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 5), Finset.card_map, Finset.card_range]
  have hs7 : ArithmeticFunction.sigma 0 (7 ^ d) = d + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 7), Finset.card_map, Finset.card_range]
  have hc7 : Nat.Coprime (7 ^ d) m4 :=
    Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr h7m4)
  have hsig3 : ArithmeticFunction.sigma 0 m3 = (d + 1) * ArithmeticFunction.sigma 0 m4 := by
    rw [hd7, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc7, hs7]
  have hc5 : Nat.Coprime (5 ^ c) m3 :=
    Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr h5m3)
  have hsig2 : ArithmeticFunction.sigma 0 m2 = (c + 1) * ArithmeticFunction.sigma 0 m3 := by
    rw [hd5, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc5, hs5]
  have hc3 : Nat.Coprime (3 ^ b) m2 :=
    Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr h3m2)
  have hsig1 : ArithmeticFunction.sigma 0 m1 = (b + 1) * ArithmeticFunction.sigma 0 m2 := by
    rw [hd3, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc3, hs3]
  have hc2 : Nat.Coprime (2 ^ a) m1 :=
    Nat.Coprime.pow_left _ (((by norm_num : Nat.Prime 2).coprime_iff_not_dvd).mpr h2m1)
  have hsig0 : ArithmeticFunction.sigma 0 n = (a + 1) * ArithmeticFunction.sigma 0 m1 := by
    rw [hd2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc2, hs2]
  have hfull : ArithmeticFunction.sigma 0 n =
      (a + 1) * ((b + 1) * ((c + 1) * ((d + 1) * ArithmeticFunction.sigma 0 m4))) := by
    rw [hsig0, hsig1, hsig2, hsig3]
  calc 35 * (ArithmeticFunction.sigma 0 n) ^ 3
      = (a + 1) ^ 3 * (b + 1) ^ 3 * (5 * (c + 1) ^ 3) * (7 * (d + 1) ^ 3) *
          (ArithmeticFunction.sigma 0 m4) ^ 3 := by rw [hfull]; ring
    _ ≤ (8 * 2 ^ a) * (3 * 3 ^ b) * (8 * 5 ^ c) * (8 * 7 ^ d) * m4 :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (L2 a) (L3 b)) (L5 c)) (L7 d)) hcore4
    _ = 1536 * (2 ^ a * (3 ^ b * (5 ^ c * (7 ^ d * m4)))) := by ring
    _ = 1536 * n := by rw [← hd7, ← hd5, ← hd3, ← hd2]

private theorem erdos647_hybrid_fourth_power_bound :
    ∀ n : ℕ, 1 ≤ n →
      (ArithmeticFunction.sigma 0 n) ^ 4 ≤ 19680 * n := by
  intro n hn
  have hroughCore : ∀ m : ℕ, 1 ≤ m →
      (∀ p : ℕ, p.Prime → p ∣ m → 17 ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ 4 ≤ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hrough
      by_cases h1 : m = 1
      · subst h1
        simp
      · have hp : m.minFac.Prime := Nat.minFac_prime h1
        have hpd : m.minFac ∣ m := Nat.minFac_dvd m
        have hp17 : 17 ≤ m.minFac := hrough _ hp hpd
        set P := m.minFac with hPdef
        clear_value P
        obtain ⟨a, q, hqnd, heq⟩ :=
          Nat.exists_eq_pow_mul_and_not_dvd (show m ≠ 0 by omega) P hp.ne_one
        have ha1 : 1 ≤ a := by
          by_contra h0
          push Not at h0
          have ha0 : a = 0 := by omega
          rw [ha0, pow_zero, one_mul] at heq
          rw [heq] at hpd
          exact hqnd hpd
        have hqpos : 1 ≤ q := by
          rcases Nat.eq_zero_or_pos q with h0 | h0
          · rw [h0, mul_zero] at heq
            omega
          · exact h0
        have hpalt : 2 ≤ P ^ a := by
          exact hp.two_le.trans (Nat.le_self_pow (by omega : a ≠ 0) P)
        have hqlt : q < m := by
          have h2 : 1 * q < P ^ a * q := by
            apply Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl q)
            omega
          calc
            q = 1 * q := (one_mul q).symm
            _ < P ^ a * q := h2
            _ = m := heq.symm
        have hqrough : ∀ p : ℕ, p.Prime → p ∣ q → 17 ≤ p := by
          intro p hpp hpq
          refine hrough p hpp ?_
          rw [heq]
          exact Dvd.dvd.mul_left hpq _
        have hIH := ih q hqlt hqpos hqrough
        have hbinary : ∀ b : ℕ, b + 1 ≤ 2 ^ b := by
          intro b
          induction b with
          | zero => simp
          | succ k ihk =>
            calc
              k + 1 + 1 ≤ 2 * (k + 1) := by omega
              _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ihk
              _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
        have hT1 : ∀ b : ℕ, (b + 1) ^ 4 ≤ P ^ b := by
          intro b
          calc
            (b + 1) ^ 4 ≤ (2 ^ b) ^ 4 := Nat.pow_le_pow_left (hbinary b) 4
            _ = (2 ^ 4) ^ b := by
              rw [← pow_mul, ← pow_mul, Nat.mul_comm]
            _ ≤ P ^ b := Nat.pow_le_pow_left (by omega) b
        have hcop : Nat.Coprime (P ^ a) q :=
          Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hqnd)
        have hs : ArithmeticFunction.sigma 0 (P ^ a) = a + 1 := by
          rw [ArithmeticFunction.sigma_zero_apply, Nat.divisors_prime_pow hp,
            Finset.card_map, Finset.card_range]
        have hsig : ArithmeticFunction.sigma 0 m =
            (a + 1) * ArithmeticFunction.sigma 0 q := by
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs]
        calc
          (ArithmeticFunction.sigma 0 m) ^ 4 =
              (a + 1) ^ 4 * (ArithmeticFunction.sigma 0 q) ^ 4 := by
                rw [hsig, mul_pow]
          _ ≤ P ^ a * q := Nat.mul_le_mul (hT1 a) hIH
          _ = m := heq.symm
  have L2 : ∀ a : ℕ, (a + 1) ^ 4 ≤ 41 * 2 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 4
      · interval_cases k <;> norm_num
      · push Not at hk
        have hratio : (k + 2) ^ 4 ≤ 2 * (k + 1) ^ 4 := by
          have hlin : 6 * (k + 2) ≤ 7 * (k + 1) := by omega
          have hpow : 1296 * (k + 2) ^ 4 ≤ 2401 * (k + 1) ^ 4 := by
            calc
              1296 * (k + 2) ^ 4 = (6 * (k + 2)) ^ 4 := by ring
              _ ≤ (7 * (k + 1)) ^ 4 := Nat.pow_le_pow_left hlin 4
              _ = 2401 * (k + 1) ^ 4 := by ring
          omega
        calc
          (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring_nf
          _ ≤ 2 * (k + 1) ^ 4 := hratio
          _ ≤ 2 * (41 * 2 ^ k) := Nat.mul_le_mul_left 2 ihk
          _ = 41 * 2 ^ (k + 1) := by rw [pow_succ]; ring
  have L3 : ∀ a : ℕ, (a + 1) ^ 4 ≤ 10 * 3 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · push Not at hk
        have hratio : (k + 2) ^ 4 ≤ 3 * (k + 1) ^ 4 := by
          have hlin : 4 * (k + 2) ≤ 5 * (k + 1) := by omega
          have hpow : 256 * (k + 2) ^ 4 ≤ 625 * (k + 1) ^ 4 := by
            calc
              256 * (k + 2) ^ 4 = (4 * (k + 2)) ^ 4 := by ring
              _ ≤ (5 * (k + 1)) ^ 4 := Nat.pow_le_pow_left hlin 4
              _ = 625 * (k + 1) ^ 4 := by ring
          omega
        calc
          (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring_nf
          _ ≤ 3 * (k + 1) ^ 4 := hratio
          _ ≤ 3 * (10 * 3 ^ k) := Nat.mul_le_mul_left 3 ihk
          _ = 10 * 3 ^ (k + 1) := by rw [pow_succ]; ring
  have L5 : ∀ a : ℕ, (a + 1) ^ 4 ≤ 4 * 5 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 1
      · interval_cases k <;> norm_num
      · push Not at hk
        have hratio : (k + 2) ^ 4 ≤ 5 * (k + 1) ^ 4 := by
          have hlin : 3 * (k + 2) ≤ 4 * (k + 1) := by omega
          have hpow : 81 * (k + 2) ^ 4 ≤ 256 * (k + 1) ^ 4 := by
            calc
              81 * (k + 2) ^ 4 = (3 * (k + 2)) ^ 4 := by ring
              _ ≤ (4 * (k + 1)) ^ 4 := Nat.pow_le_pow_left hlin 4
              _ = 256 * (k + 1) ^ 4 := by ring
          omega
        calc
          (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring_nf
          _ ≤ 5 * (k + 1) ^ 4 := hratio
          _ ≤ 5 * (4 * 5 ^ k) := Nat.mul_le_mul_left 5 ihk
          _ = 4 * 5 ^ (k + 1) := by rw [pow_succ]; ring
  have L7 : ∀ a : ℕ, (a + 1) ^ 4 ≤ 3 * 7 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 0
      · interval_cases k; norm_num
      · push Not at hk
        have hratio : (k + 2) ^ 4 ≤ 7 * (k + 1) ^ 4 := by
          have hlin : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
          have hpow : 16 * (k + 2) ^ 4 ≤ 81 * (k + 1) ^ 4 := by
            calc
              16 * (k + 2) ^ 4 = (2 * (k + 2)) ^ 4 := by ring
              _ ≤ (3 * (k + 1)) ^ 4 := Nat.pow_le_pow_left hlin 4
              _ = 81 * (k + 1) ^ 4 := by ring
          omega
        calc
          (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring_nf
          _ ≤ 7 * (k + 1) ^ 4 := hratio
          _ ≤ 7 * (3 * 7 ^ k) := Nat.mul_le_mul_left 7 ihk
          _ = 3 * 7 ^ (k + 1) := by rw [pow_succ]; ring
  have L11 : ∀ a : ℕ, (a + 1) ^ 4 ≤ 2 * 11 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 0
      · interval_cases k; norm_num
      · push Not at hk
        have hratio : (k + 2) ^ 4 ≤ 11 * (k + 1) ^ 4 := by
          have hlin : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
          have hpow : 16 * (k + 2) ^ 4 ≤ 81 * (k + 1) ^ 4 := by
            calc
              16 * (k + 2) ^ 4 = (2 * (k + 2)) ^ 4 := by ring
              _ ≤ (3 * (k + 1)) ^ 4 := Nat.pow_le_pow_left hlin 4
              _ = 81 * (k + 1) ^ 4 := by ring
          omega
        calc
          (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring_nf
          _ ≤ 11 * (k + 1) ^ 4 := hratio
          _ ≤ 11 * (2 * 11 ^ k) := Nat.mul_le_mul_left 11 ihk
          _ = 2 * 11 ^ (k + 1) := by rw [pow_succ]; ring
  have L13 : ∀ a : ℕ, (a + 1) ^ 4 ≤ 2 * 13 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 0
      · interval_cases k; norm_num
      · push Not at hk
        have hratio : (k + 2) ^ 4 ≤ 13 * (k + 1) ^ 4 := by
          have hlin : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
          have hpow : 16 * (k + 2) ^ 4 ≤ 81 * (k + 1) ^ 4 := by
            calc
              16 * (k + 2) ^ 4 = (2 * (k + 2)) ^ 4 := by ring
              _ ≤ (3 * (k + 1)) ^ 4 := Nat.pow_le_pow_left hlin 4
              _ = 81 * (k + 1) ^ 4 := by ring
          omega
        calc
          (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring_nf
          _ ≤ 13 * (k + 1) ^ 4 := hratio
          _ ≤ 13 * (2 * 13 ^ k) := Nat.mul_le_mul_left 13 ihk
          _ = 2 * 13 ^ (k + 1) := by rw [pow_succ]; ring
  obtain ⟨a, m1, h2m1, hd2⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show n ≠ 0 by omega) 2 (by norm_num)
  have hm1pos : 1 ≤ m1 := by
    rcases Nat.eq_zero_or_pos m1 with h0 | h0
    · rw [h0, mul_zero] at hd2
      omega
    · exact h0
  obtain ⟨b, m2, h3m2, hd3⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show m1 ≠ 0 by omega) 3 (by norm_num)
  have hm2pos : 1 ≤ m2 := by
    rcases Nat.eq_zero_or_pos m2 with h0 | h0
    · rw [h0, mul_zero] at hd3
      omega
    · exact h0
  obtain ⟨c, m3, h5m3, hd5⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show m2 ≠ 0 by omega) 5 (by norm_num)
  have hm3pos : 1 ≤ m3 := by
    rcases Nat.eq_zero_or_pos m3 with h0 | h0
    · rw [h0, mul_zero] at hd5
      omega
    · exact h0
  obtain ⟨d, m4, h7m4, hd7⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show m3 ≠ 0 by omega) 7 (by norm_num)
  have hm4pos : 1 ≤ m4 := by
    rcases Nat.eq_zero_or_pos m4 with h0 | h0
    · rw [h0, mul_zero] at hd7
      omega
    · exact h0
  obtain ⟨e, m5, h11m5, hd11⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show m4 ≠ 0 by omega) 11 (by norm_num)
  have hm5pos : 1 ≤ m5 := by
    rcases Nat.eq_zero_or_pos m5 with h0 | h0
    · rw [h0, mul_zero] at hd11
      omega
    · exact h0
  obtain ⟨f, m6, h13m6, hd13⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show m5 ≠ 0 by omega) 13 (by norm_num)
  have hm6pos : 1 ≤ m6 := by
    rcases Nat.eq_zero_or_pos m6 with h0 | h0
    · rw [h0, mul_zero] at hd13
      omega
    · exact h0
  have hm2dm1 : m2 ∣ m1 := ⟨3 ^ b, by rw [hd3]; ring⟩
  have hm3dm2 : m3 ∣ m2 := ⟨5 ^ c, by rw [hd5]; ring⟩
  have hm4dm3 : m4 ∣ m3 := ⟨7 ^ d, by rw [hd7]; ring⟩
  have hm5dm4 : m5 ∣ m4 := ⟨11 ^ e, by rw [hd11]; ring⟩
  have hm6dm5 : m6 ∣ m5 := ⟨13 ^ f, by rw [hd13]; ring⟩
  have hrough6 : ∀ p : ℕ, p.Prime → p ∣ m6 → 17 ≤ p := by
    intro p hpp hp6
    have hp2 : p ≠ 2 := by
      intro h
      exact h2m1 (h ▸ hp6.trans (hm6dm5.trans (hm5dm4.trans
        (hm4dm3.trans (hm3dm2.trans hm2dm1)))))
    have hp3 : p ≠ 3 := by
      intro h
      exact h3m2 (h ▸ hp6.trans (hm6dm5.trans (hm5dm4.trans
        (hm4dm3.trans hm3dm2))))
    have hp5 : p ≠ 5 := by
      intro h
      exact h5m3 (h ▸ hp6.trans (hm6dm5.trans
        (hm5dm4.trans hm4dm3)))
    have hp7 : p ≠ 7 := by
      intro h
      exact h7m4 (h ▸ hp6.trans (hm6dm5.trans hm5dm4))
    have hp11 : p ≠ 11 := by
      intro h
      exact h11m5 (h ▸ hp6.trans hm6dm5)
    have hp13 : p ≠ 13 := by
      intro h
      exact h13m6 (h ▸ hp6)
    have hpge2 := hpp.two_le
    by_contra hlt
    push Not at hlt
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hpp (by norm_num)
    · exact hp5 rfl
    · exact absurd hpp (by norm_num)
    · exact hp7 rfl
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact hp11 rfl
    · exact absurd hpp (by norm_num)
    · exact hp13 rfl
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
    · exact absurd hpp (by norm_num)
  have hcore := hroughCore m6 hm6pos hrough6
  have hs2 : ArithmeticFunction.sigma 0 (2 ^ a) = a + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 2),
      Finset.card_map, Finset.card_range]
  have hs3 : ArithmeticFunction.sigma 0 (3 ^ b) = b + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 3),
      Finset.card_map, Finset.card_range]
  have hs5 : ArithmeticFunction.sigma 0 (5 ^ c) = c + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 5),
      Finset.card_map, Finset.card_range]
  have hs7 : ArithmeticFunction.sigma 0 (7 ^ d) = d + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 7),
      Finset.card_map, Finset.card_range]
  have hs11 : ArithmeticFunction.sigma 0 (11 ^ e) = e + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 11),
      Finset.card_map, Finset.card_range]
  have hs13 : ArithmeticFunction.sigma 0 (13 ^ f) = f + 1 := by
    rw [ArithmeticFunction.sigma_zero_apply,
      Nat.divisors_prime_pow (by norm_num : Nat.Prime 13),
      Finset.card_map, Finset.card_range]
  have hc13 : Nat.Coprime (13 ^ f) m6 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 13).coprime_iff_not_dvd).mpr h13m6)
  have hsig5 : ArithmeticFunction.sigma 0 m5 =
      (f + 1) * ArithmeticFunction.sigma 0 m6 := by
    rw [hd13, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc13, hs13]
  have hc11 : Nat.Coprime (11 ^ e) m5 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 11).coprime_iff_not_dvd).mpr h11m5)
  have hsig4 : ArithmeticFunction.sigma 0 m4 =
      (e + 1) * ArithmeticFunction.sigma 0 m5 := by
    rw [hd11, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc11, hs11]
  have hc7 : Nat.Coprime (7 ^ d) m4 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 7).coprime_iff_not_dvd).mpr h7m4)
  have hsig3 : ArithmeticFunction.sigma 0 m3 =
      (d + 1) * ArithmeticFunction.sigma 0 m4 := by
    rw [hd7, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc7, hs7]
  have hc5 : Nat.Coprime (5 ^ c) m3 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd).mpr h5m3)
  have hsig2 : ArithmeticFunction.sigma 0 m2 =
      (c + 1) * ArithmeticFunction.sigma 0 m3 := by
    rw [hd5, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc5, hs5]
  have hc3 : Nat.Coprime (3 ^ b) m2 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr h3m2)
  have hsig1 : ArithmeticFunction.sigma 0 m1 =
      (b + 1) * ArithmeticFunction.sigma 0 m2 := by
    rw [hd3, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc3, hs3]
  have hc2 : Nat.Coprime (2 ^ a) m1 :=
    Nat.Coprime.pow_left _
      (((by norm_num : Nat.Prime 2).coprime_iff_not_dvd).mpr h2m1)
  have hsig0 : ArithmeticFunction.sigma 0 n =
      (a + 1) * ArithmeticFunction.sigma 0 m1 := by
    rw [hd2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc2, hs2]
  have hfull : ArithmeticFunction.sigma 0 n =
      (a + 1) * ((b + 1) * ((c + 1) * ((d + 1) *
        ((e + 1) * ((f + 1) * ArithmeticFunction.sigma 0 m6))))) := by
    rw [hsig0, hsig1, hsig2, hsig3, hsig4, hsig5]
  calc
    (ArithmeticFunction.sigma 0 n) ^ 4 =
        (a + 1) ^ 4 * ((b + 1) ^ 4 * ((c + 1) ^ 4 *
          ((d + 1) ^ 4 * ((e + 1) ^ 4 * ((f + 1) ^ 4 *
            (ArithmeticFunction.sigma 0 m6) ^ 4))))) := by
              rw [hfull]
              simp only [mul_pow]
    _ ≤ (41 * 2 ^ a) * ((10 * 3 ^ b) * ((4 * 5 ^ c) *
          ((3 * 7 ^ d) * ((2 * 11 ^ e) * ((2 * 13 ^ f) * m6))))) :=
      Nat.mul_le_mul
        (L2 a) (Nat.mul_le_mul (L3 b) (Nat.mul_le_mul (L5 c)
          (Nat.mul_le_mul (L7 d) (Nat.mul_le_mul (L11 e)
            (Nat.mul_le_mul (L13 f) hcore)))))
    _ = (41 * 10 * 4 * 3 * 2 * 2) * (2 ^ a * (3 ^ b * (5 ^ c *
          (7 ^ d * (11 ^ e * (13 ^ f * m6)))))) := by ac_rfl
    _ = 19680 * (2 ^ a * (3 ^ b * (5 ^ c *
          (7 ^ d * (11 ^ e * (13 ^ f * m6)))))) := by norm_num
    _ = 19680 * n := by
      rw [← hd13, ← hd11, ← hd7, ← hd5, ← hd3, ← hd2]

private theorem erdos647_hybrid_fifth_power_bound :
    ∀ n : ℕ, 1 ≤ n →
      (ArithmeticFunction.sigma 0 n) ^ 5 ≤ 147700800 * n := by
  intro n hn
  have hgeneric :
      ∀ (r m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ),
        0 < r →
        1 ≤ m →
        (∀ p ∈ S, 1 ≤ c p) →
        (∀ p ∈ S, p.Prime → p ∣ m → ∀ a : ℕ, 1 ≤ a →
          (a + 1) ^ r ≤ c p * p ^ a) →
        (∀ p : ℕ, p.Prime → p ∣ m → p ∉ S → 2 ^ r ≤ p) →
        (ArithmeticFunction.sigma 0 m) ^ r ≤ (∏ p ∈ S, c p) * m := by
    intro r m S c hr hm hc hsmall hrough
    have hm0 : m ≠ 0 := by omega
    have hbinary : ∀ b : ℕ, b + 1 ≤ 2 ^ b := by
      intro b
      induction b with
      | zero => simp
      | succ k ih =>
        calc
          k + 1 + 1 ≤ 2 * (k + 1) := by omega
          _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
    have hlocal : ∀ p ∈ m.primeFactors,
        (m.factorization p + 1) ^ r ≤
          (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
      have hpa : 1 ≤ m.factorization p :=
        hpp.factorization_pos_of_dvd hm0 hpd
      by_cases hpS : p ∈ S
      · simp only [hpS, if_true]
        exact hsmall p hpS hpp hpd _ hpa
      · simp only [hpS, if_false, one_mul]
        calc
          (m.factorization p + 1) ^ r ≤ (2 ^ (m.factorization p)) ^ r :=
            Nat.pow_le_pow_left (hbinary _) r
          _ = (2 ^ r) ^ (m.factorization p) := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
          _ ≤ p ^ (m.factorization p) :=
            Nat.pow_le_pow_left (hrough p hpp hpd hpS) _
    have hsigma : ArithmeticFunction.sigma 0 m =
        ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
      rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
      simp
    have hmprod : (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) = m := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact Nat.prod_factorization_pow_eq_self hm0
    have hbase : (ArithmeticFunction.sigma 0 m) ^ r ≤
        (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by
      rw [hsigma, ← Finset.prod_pow]
      calc
        ∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ r
            ≤ ∏ p ∈ m.primeFactors,
                (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by
                  exact Finset.prod_le_prod' hlocal
        _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) *
              (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
                rw [Finset.prod_mul_distrib]
        _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by
              rw [hmprod]
    have hprod_eq :
        (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) =
          ∏ p ∈ m.primeFactors.filter (fun p => p ∈ S), c p := by
      rw [Finset.prod_filter]
    have hsub : m.primeFactors.filter (fun p => p ∈ S) ⊆ S := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hprod_le :
        (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) ≤
          ∏ p ∈ S, c p := by
      rw [hprod_eq]
      exact Finset.prod_le_prod_of_subset_of_one_le hsub
        (fun _ _ => Nat.zero_le _)
        (fun p hpS _ => hc p hpS)
    exact hbase.trans (Nat.mul_le_mul_right m hprod_le)
  have L2 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 263 * 2 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 5
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 7 * (k + 2) ≤ 8 * (k + 1) := by omega
        have hpow : 16807 * (k + 2) ^ 5 ≤ 32768 * (k + 1) ^ 5 := by
          calc
            16807 * (k + 2) ^ 5 = (7 * (k + 2)) ^ 5 := by ring
            _ ≤ (8 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 32768 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 2 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 2 * (k + 1) ^ 5 := hratio
          _ ≤ 2 * (263 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
          _ = 263 * 2 ^ (k + 1) := by rw [pow_succ]; ring
  have L3 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 39 * 3 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 3
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 5 * (k + 2) ≤ 6 * (k + 1) := by omega
        have hpow : 3125 * (k + 2) ^ 5 ≤ 7776 * (k + 1) ^ 5 := by
          calc
            3125 * (k + 2) ^ 5 = (5 * (k + 2)) ^ 5 := by ring
            _ ≤ (6 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 7776 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 3 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 3 * (k + 1) ^ 5 := hratio
          _ ≤ 3 * (39 * 3 ^ k) := Nat.mul_le_mul_left 3 ih
          _ = 39 * 3 ^ (k + 1) := by rw [pow_succ]; ring
  have L5 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 10 * 5 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 1
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 3 * (k + 2) ≤ 4 * (k + 1) := by omega
        have hpow : 243 * (k + 2) ^ 5 ≤ 1024 * (k + 1) ^ 5 := by
          calc
            243 * (k + 2) ^ 5 = (3 * (k + 2)) ^ 5 := by ring
            _ ≤ (4 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 1024 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 5 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 5 * (k + 1) ^ 5 := hratio
          _ ≤ 5 * (10 * 5 ^ k) := Nat.mul_le_mul_left 5 ih
          _ = 10 * 5 ^ (k + 1) := by rw [pow_succ]; ring
  have L7 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 5 * 7 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 1
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 3 * (k + 2) ≤ 4 * (k + 1) := by omega
        have hpow : 243 * (k + 2) ^ 5 ≤ 1024 * (k + 1) ^ 5 := by
          calc
            243 * (k + 2) ^ 5 = (3 * (k + 2)) ^ 5 := by ring
            _ ≤ (4 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 1024 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 7 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 7 * (k + 1) ^ 5 := hratio
          _ ≤ 7 * (5 * 7 ^ k) := Nat.mul_le_mul_left 7 ih
          _ = 5 * 7 ^ (k + 1) := by rw [pow_succ]; ring
  have Llarge : ∀ (p c : ℕ), 11 ≤ p → 32 ≤ c * p →
      ∀ a : ℕ, (a + 1) ^ 5 ≤ c * p ^ a := by
    intro p c hp hbase a
    have hc : 1 ≤ c := by
      by_contra hc0
      push Not at hc0
      have : c = 0 := by omega
      simp [this] at hbase
    induction a with
    | zero => simpa using hc
    | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simpa using hbase
      · have hk1 : 1 ≤ k := by omega
        have hlin : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
        have hpow : 32 * (k + 2) ^ 5 ≤ 243 * (k + 1) ^ 5 := by
          calc
            32 * (k + 2) ^ 5 = (2 * (k + 2)) ^ 5 := by ring
            _ ≤ (3 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 243 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ p * (k + 1) ^ 5 := by
          have hp32 : 243 ≤ 32 * p := by omega
          have hscaled : 32 * (k + 2) ^ 5 ≤
              32 * (p * (k + 1) ^ 5) := by
            calc
              32 * (k + 2) ^ 5 ≤ 243 * (k + 1) ^ 5 := hpow
              _ ≤ (32 * p) * (k + 1) ^ 5 :=
                Nat.mul_le_mul_right ((k + 1) ^ 5) hp32
              _ = 32 * (p * (k + 1) ^ 5) := by ring
          exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ p * (k + 1) ^ 5 := hratio
          _ ≤ p * (c * p ^ k) := Nat.mul_le_mul_left p ih
          _ = c * p ^ (k + 1) := by rw [pow_succ]; ring
  let S : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
  let c : ℕ → ℕ := fun p =>
    if p = 2 then 263 else if p = 3 then 39 else if p = 5 then 10 else
    if p = 7 then 5 else if p = 11 then 3 else if p = 13 then 3 else 2
  have hc : ∀ p ∈ S, 1 ≤ c p := by
    intro p hp
    simp [S] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [c]
  have hsmall : ∀ p ∈ S, p.Prime → p ∣ n → ∀ a : ℕ, 1 ≤ a →
      (a + 1) ^ 5 ≤ c p * p ^ a := by
    intro p hp hpp hpd a ha
    simp [S] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [c] using L2 a
    · simpa [c] using L3 a
    · simpa [c] using L5 a
    · simpa [c] using L7 a
    · simpa [c] using Llarge 11 3 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 13 3 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 17 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 19 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 23 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 29 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 31 2 (by norm_num) (by norm_num) a
  have hrough : ∀ p : ℕ, p.Prime → p ∣ n → p ∉ S → 2 ^ 5 ≤ p := by
    intro p hpp hpd hpS
    have hp32 : 32 ≤ p := by
      by_contra hp
      push Not at hp
      interval_cases p <;> norm_num at hpp
      all_goals norm_num [S] at hpS
    norm_num
    exact hp32
  have h := hgeneric 5 n S c (by norm_num) hn hc hsmall hrough
  norm_num [S, c] at h ⊢
  exact h

/-! The assembly layer, stated independently of the three bound proofs. This
form is small enough to replay as one tracked proof-search root; the
unconditional theorem below supplies its hypotheses from the private,
standalone bound proofs in this file. The cube, fourth-power, and fifth-power
components also have their own independently tracked roots.

Tracked proof-search provenance (2026-07-16):

* problem version: `8f106b39-3517-45b3-931d-963f361e7854`
* episode: `788ce5b5-fd30-4fc7-bd69-d73741195819`
* root statement hash:
  `2c8209c8fc0ecd9402fff3f4e6bae897f65a1e111c2735324a33d27a21bde981`
* outcome: `kernel_verified`

The unconditional theorem and all three supporting proofs replay together in
this source module. A single fully inlined proof-search declaration reaches the
server's fixed 200,000-heartbeat ceiling; that is a transport limit rather than
a mathematical gap, so the compact assembly theorem is the tracked root. -/
theorem erdos647_candidate_of_hybrid_power_prefix_from_bounds :
    ∀ n : ℕ,
      (∀ m : ℕ, 1 ≤ m →
        35 * (ArithmeticFunction.sigma 0 m) ^ 3 ≤ 1536 * m) →
      (∀ m : ℕ, 1 ≤ m →
        (ArithmeticFunction.sigma 0 m) ^ 4 ≤ 19680 * m) →
      (∀ m : ℕ, 1 ≤ m →
        (ArithmeticFunction.sigma 0 m) ^ 5 ≤ 147700800 * m) →
      0 < n →
      (∀ k : ℕ, 0 < k → k < n →
        35 * (k + 2) ^ 3 < 1536 * (n - k) →
        (k + 2) ^ 4 < 19680 * (n - k) →
        (k + 2) ^ 5 < 147700800 * (n - k) →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro n hcube hfourth hfifth hn hprefix
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbudget : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases h3 : 35 * (k + 2) ^ 3 < 1536 * (n - k)
    · by_cases h4 : (k + 2) ^ 4 < 19680 * (n - k)
      · by_cases h5 : (k + 2) ^ 5 < 147700800 * (n - k)
        · exact hprefix k hk0 hkn h3 h4 h5
        · push Not at h5
          have hmpos : 1 ≤ n - k := by omega
          have hbound := hfifth (n - k) hmpos
          have hpows :
              (ArithmeticFunction.sigma 0 (n - k)) ^ 5 ≤ (k + 2) ^ 5 :=
            hbound.trans h5
          exact (Nat.pow_le_pow_iff_left (by norm_num : 5 ≠ 0)).mp hpows
      · push Not at h4
        have hmpos : 1 ≤ n - k := by omega
        have hbound := hfourth (n - k) hmpos
        have hpows :
            (ArithmeticFunction.sigma 0 (n - k)) ^ 4 ≤ (k + 2) ^ 4 :=
          hbound.trans h4
        exact (Nat.pow_le_pow_iff_left (by norm_num : 4 ≠ 0)).mp hpows
    · push Not at h3
      have hmpos : 1 ≤ n - k := by omega
      have hbound := hcube (n - k) hmpos
      have hpows :
          35 * (ArithmeticFunction.sigma 0 (n - k)) ^ 3 ≤
            35 * (k + 2) ^ 3 :=
        hbound.trans h3
      have hcubes :
          (ArithmeticFunction.sigma 0 (n - k)) ^ 3 ≤ (k + 2) ^ 3 := by
        omega
      exact (Nat.pow_le_pow_iff_left (by norm_num : 3 ≠ 0)).mp hcubes
  apply ciSup_le
  intro m
  rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hmpos
  · rw [hm0]
    simp
  · have hmn : (m : ℕ) < n := m.isLt
    have hk0 : 0 < n - (m : ℕ) := by omega
    have hkn : n - (m : ℕ) < n := by omega
    have hb := hbudget (n - (m : ℕ)) hk0 hkn
    have hmk : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    rw [hmk] at hb
    omega

/-!
# Erdős #647 — exact hybrid power-prefix candidate certificate

The three verified global divisor-power bounds are used simultaneously. A
shift needs to be checked explicitly only when all three corresponding
unsafe inequalities hold. If any inequality fails, its global bound forces
the required divisor budget automatically.
-/

theorem erdos647_candidate_of_hybrid_power_prefix :
    ∀ n : ℕ,
      0 < n →
      (∀ k : ℕ, 0 < k → k < n →
        35 * (k + 2) ^ 3 < 1536 * (n - k) →
        (k + 2) ^ 4 < 19680 * (n - k) →
        (k + 2) ^ 5 < 147700800 * (n - k) →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro n hn hprefix
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbudget : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases h3 : 35 * (k + 2) ^ 3 < 1536 * (n - k)
    · by_cases h4 : (k + 2) ^ 4 < 19680 * (n - k)
      · by_cases h5 : (k + 2) ^ 5 < 147700800 * (n - k)
        · exact hprefix k hk0 hkn h3 h4 h5
        · push Not at h5
          have hmpos : 1 ≤ n - k := by omega
          have hbound := erdos647_hybrid_fifth_power_bound (n - k) hmpos
          have hpows :
              (ArithmeticFunction.sigma 0 (n - k)) ^ 5 ≤ (k + 2) ^ 5 :=
            hbound.trans h5
          exact (Nat.pow_le_pow_iff_left (by norm_num : 5 ≠ 0)).mp hpows
      · push Not at h4
        have hmpos : 1 ≤ n - k := by omega
        have hbound := erdos647_hybrid_fourth_power_bound (n - k) hmpos
        have hpows :
            (ArithmeticFunction.sigma 0 (n - k)) ^ 4 ≤ (k + 2) ^ 4 :=
          hbound.trans h4
        exact (Nat.pow_le_pow_iff_left (by norm_num : 4 ≠ 0)).mp hpows
    · push Not at h3
      have hmpos : 1 ≤ n - k := by omega
      have hbound := erdos647_hybrid_sharp_cube_divisor_bound (n - k) hmpos
      have hpows :
          35 * (ArithmeticFunction.sigma 0 (n - k)) ^ 3 ≤
            35 * (k + 2) ^ 3 :=
        hbound.trans h3
      have hcubes :
          (ArithmeticFunction.sigma 0 (n - k)) ^ 3 ≤ (k + 2) ^ 3 := by
        omega
      exact (Nat.pow_le_pow_iff_left (by norm_num : 3 ≠ 0)).mp hcubes
  apply ciSup_le
  intro m
  rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hmpos
  · rw [hm0]
    simp
  · have hmn : (m : ℕ) < n := m.isLt
    have hk0 : 0 < n - (m : ℕ) := by omega
    have hkn : n - (m : ℕ) < n := by omega
    have hb := hbudget (n - (m : ℕ)) hk0 hkn
    have hmk : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    rw [hmk] at hb
    omega
