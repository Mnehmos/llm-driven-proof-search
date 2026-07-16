import Mathlib

/-!
# Erdős #647 — exact small-prime class cube bound

The sharp global cube bound is refined according to exactly which of
`2,3,5,7` divide the input.  The coefficient is `35` on the 11-rough
class and `1536` when all four small primes occur, with every intermediate
class represented by the corresponding product of local constants.

Both declarations were kernel-verified on 2026-07-16:

* `erdos647_small_prime_class_cube_bound`: problem
  `ec3b4486-6f8d-49f5-961b-601f73ed0aec`, episode
  `05cc4956-b712-4c07-80df-3d9f9976f347`, statement hash
  `997bfc30d1734bb606c325bd22c85a3a7d91568ef0c2fdb06fc050261519962f`,
  preverification `01e62ffb-960e-4010-9c9c-81acc3b0e25a` (`kernel_pass`).
  The first tracked transport accidentally included the next declaration's
  doc comment and produced a parse error; the corrected proof boundary was
  accepted on revision 1 with outcome `kernel_verified`.
* `erdos647_gcd_class_cube_bound`: problem
  `06c149c9-648c-4f7a-a7ef-f7e02cddb9f1`, episode
  `49d6e0f2-48e5-4a20-a667-b292a0f3cc24`, statement hash
  `7666043b8b9dcdaa7186cd199a5ed47c54637ba370fd914ba93bbbdcfd1b398e`,
  preverification `32ef31ac-7a5d-47cd-9d66-1e797b51c3a2` (`kernel_pass`).
  The tracked proof inlined the full class theorem.
* `erdos647_gcd_class_excess_shift_in_cube_prefix`: problem
  `91a93bb5-9cce-4716-9439-c08c58cb1219`, episode
  `dd804d15-12b3-4b79-a51f-df444d46a368`, statement hash
  `b90c7a4b7c0818d190b13c102934bf35341108e3e17d82c71967cea6c34d7d0c`,
  preverification `056366e8-333a-42b2-ba71-8853d92ee801` (`kernel_pass`).
* `erdos647_candidate_of_gcd_class_cube_prefix`: problem
  `3d1991c6-042b-43d6-a8cd-5a3a62218165`, episode
  `a5be3ba2-ae6c-49b6-801b-07bf14d0b79b`, statement hash
  `fd29fc016b8a808ba9f1baee90c2e32c84723d72da3b50d4782981d67e8a438e`,
  preverification `918a5300-98e3-4da9-83ac-451878bd7d02` (`kernel_pass`).
  The two prefix proofs inline the shifted class theorem, which in turn
  inlines the complete small-prime class proof.
-/

theorem erdos647_small_prime_class_cube_bound :
    ∀ n : ℕ, 1 ≤ n →
      35 * (ArithmeticFunction.sigma 0 n) ^ 3 ≤
        (if 2 ∣ n then 8 else 1) *
        (if 3 ∣ n then 3 else 1) *
        (if 5 ∣ n then 8 else 5) *
        (if 7 ∣ n then 8 else 7) * n := by
  intro n hn
  have hroughCore : ∀ m : ℕ, 1 ≤ m →
      (∀ p : ℕ, p.Prime → p ∣ m → 11 ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ 3 ≤ m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hrough
      by_cases h1 : m = 1
      · subst h1
        native_decide
      · have hp : m.minFac.Prime := Nat.minFac_prime h1
        have hpd : m.minFac ∣ m := Nat.minFac_dvd m
        have hp11 : 11 ≤ m.minFac := hrough _ hp hpd
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
          have := Nat.le_self_pow (by omega : a ≠ 0) P
          omega
        have hqlt : q < m := by
          have h2 : 1 * q < P ^ a * q := by
            apply Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl q)
            omega
          calc
            q = 1 * q := (one_mul q).symm
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
              calc
                (k + 2) ^ 3 ≤ (2 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
                _ = 8 * (k + 1) ^ 3 := by ring
            calc
              (k + 1 + 1) ^ 3 = (k + 2) ^ 3 := by ring_nf
              _ ≤ 8 * (k + 1) ^ 3 := hstep
              _ ≤ 8 * P ^ k := Nat.mul_le_mul_left 8 ihk
              _ ≤ P * P ^ k := Nat.mul_le_mul_right _ (by omega)
              _ = P ^ (k + 1) := by rw [pow_succ]; ring
        have hcop : Nat.Coprime (P ^ a) q :=
          Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hqnd)
        have hs : ArithmeticFunction.sigma 0 (P ^ a) = a + 1 := by
          rw [ArithmeticFunction.sigma_zero_apply, Nat.divisors_prime_pow hp,
            Finset.card_map, Finset.card_range]
        have hsig : ArithmeticFunction.sigma 0 m =
            (a + 1) * ArithmeticFunction.sigma 0 q := by
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs]
        calc
          (ArithmeticFunction.sigma 0 m) ^ 3 =
              (a + 1) ^ 3 * (ArithmeticFunction.sigma 0 q) ^ 3 := by
                rw [hsig]
                ring
          _ ≤ P ^ a * q := Nat.mul_le_mul (hT1 a) hIH
          _ = m := heq.symm
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
          calc
            64 * (k + 2) ^ 3 = (4 * (k + 2)) ^ 3 := by ring
            _ ≤ (5 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 125 * (k + 1) ^ 3 := by ring
        have h5 : (k + 2) ^ 3 ≤ 2 * (k + 1) ^ 3 := by omega
        calc
          (k + 1 + 1) ^ 3 = (k + 2) ^ 3 := by ring_nf
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
          calc
            27 * (k + 2) ^ 3 = (3 * (k + 2)) ^ 3 := by ring
            _ ≤ (4 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 64 * (k + 1) ^ 3 := by ring
        have h5 : (k + 2) ^ 3 ≤ 3 * (k + 1) ^ 3 := by omega
        calc
          (k + 1 + 1) ^ 3 = (k + 2) ^ 3 := by ring_nf
          _ ≤ 3 * (k + 1) ^ 3 := h5
          _ ≤ 3 * (3 * 3 ^ k) := by omega
          _ = 3 * 3 ^ (k + 1) := by rw [pow_succ]; ring
  have L5 : ∀ c : ℕ, 5 * (c + 1) ^ 3 ≤ 8 * 5 ^ c := by
    intro c
    induction c with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 0
      · interval_cases k; norm_num
      · push Not at hk
        have h2 : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
        have h4 : 8 * (k + 2) ^ 3 ≤ 27 * (k + 1) ^ 3 := by
          calc
            8 * (k + 2) ^ 3 = (2 * (k + 2)) ^ 3 := by ring
            _ ≤ (3 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 27 * (k + 1) ^ 3 := by ring
        have h6 : 5 * (k + 2) ^ 3 ≤ 8 * (5 * 5 ^ k) := by omega
        calc
          5 * (k + 1 + 1) ^ 3 = 5 * (k + 2) ^ 3 := by ring_nf
          _ ≤ 8 * (5 * 5 ^ k) := h6
          _ = 8 * 5 ^ (k + 1) := by rw [pow_succ]; ring
  have L7 : ∀ d : ℕ, 7 * (d + 1) ^ 3 ≤ 8 * 7 ^ d := by
    intro d
    induction d with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 0
      · interval_cases k; norm_num
      · push Not at hk
        have h2 : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
        have h4 : 8 * (k + 2) ^ 3 ≤ 27 * (k + 1) ^ 3 := by
          calc
            8 * (k + 2) ^ 3 = (2 * (k + 2)) ^ 3 := by ring
            _ ≤ (3 * (k + 1)) ^ 3 := Nat.pow_le_pow_left h2 3
            _ = 27 * (k + 1) ^ 3 := by ring
        have h6 : 7 * (k + 2) ^ 3 ≤ 8 * (7 * 7 ^ k) := by omega
        calc
          7 * (k + 1 + 1) ^ 3 = 7 * (k + 2) ^ 3 := by ring_nf
          _ ≤ 8 * (7 * 7 ^ k) := h6
          _ = 8 * 7 ^ (k + 1) := by rw [pow_succ]; ring
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
  have hm1dn : m1 ∣ n := ⟨2 ^ a, by rw [hd2]; ring⟩
  have hm2dm1 : m2 ∣ m1 := ⟨3 ^ b, by rw [hd3]; ring⟩
  have hm2dn : m2 ∣ n := hm2dm1.trans hm1dn
  have hm3dm2 : m3 ∣ m2 := ⟨5 ^ c, by rw [hd5]; ring⟩
  have hm3dn : m3 ∣ n := hm3dm2.trans hm2dn
  have hm4dm3 : m4 ∣ m3 := ⟨7 ^ d, by rw [hd7]; ring⟩
  have hm4dn : m4 ∣ n := hm4dm3.trans hm3dn
  have ha0_of_not_dvd : ¬2 ∣ n → a = 0 := by
    intro hnot
    by_contra ha0
    apply hnot
    rw [hd2]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 ha0) m1
  have hb0_of_not_dvd : ¬3 ∣ n → b = 0 := by
    intro hnot
    by_contra hb0
    apply hnot
    have h3m1 : 3 ∣ m1 := by
      rw [hd3]
      exact Dvd.dvd.mul_right (dvd_pow_self 3 hb0) m2
    exact h3m1.trans hm1dn
  have hc0_of_not_dvd : ¬5 ∣ n → c = 0 := by
    intro hnot
    by_contra hc0
    apply hnot
    have h5m2 : 5 ∣ m2 := by
      rw [hd5]
      exact Dvd.dvd.mul_right (dvd_pow_self 5 hc0) m3
    exact h5m2.trans hm2dn
  have hd0_of_not_dvd : ¬7 ∣ n → d = 0 := by
    intro hnot
    by_contra hd0
    apply hnot
    have h7m3 : 7 ∣ m3 := by
      rw [hd7]
      exact Dvd.dvd.mul_right (dvd_pow_self 7 hd0) m4
    exact h7m3.trans hm3dn
  have C2 : (a + 1) ^ 3 ≤ (if 2 ∣ n then 8 else 1) * 2 ^ a := by
    by_cases h2n : 2 ∣ n
    · simp only [h2n, if_true]
      exact L2 a
    · have ha0 := ha0_of_not_dvd h2n
      subst a
      simp [h2n]
  have C3 : (b + 1) ^ 3 ≤ (if 3 ∣ n then 3 else 1) * 3 ^ b := by
    by_cases h3n : 3 ∣ n
    · simp only [h3n, if_true]
      exact L3 b
    · have hb0 := hb0_of_not_dvd h3n
      subst b
      simp [h3n]
  have C5 : 5 * (c + 1) ^ 3 ≤ (if 5 ∣ n then 8 else 5) * 5 ^ c := by
    by_cases h5n : 5 ∣ n
    · simp only [h5n, if_true]
      exact L5 c
    · have hc0 := hc0_of_not_dvd h5n
      subst c
      simp [h5n]
  have C7 : 7 * (d + 1) ^ 3 ≤ (if 7 ∣ n then 8 else 7) * 7 ^ d := by
    by_cases h7n : 7 ∣ n
    · simp only [h7n, if_true]
      exact L7 d
    · have hd0 := hd0_of_not_dvd h7n
      subst d
      simp [h7n]
  have hrough4 : ∀ p : ℕ, p.Prime → p ∣ m4 → 11 ≤ p := by
    intro p hpp hpq
    have hp2 : p ≠ 2 := by
      intro h
      exact h2m1 (h ▸ hpq.trans (hm4dm3.trans (hm3dm2.trans hm2dm1)))
    have hp3 : p ≠ 3 := by
      intro h
      exact h3m2 (h ▸ hpq.trans (hm4dm3.trans hm3dm2))
    have hp5 : p ≠ 5 := by
      intro h
      exact h5m3 (h ▸ hpq.trans hm4dm3)
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
  have hcore4 := hroughCore m4 hm4pos hrough4
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
      (a + 1) * ((b + 1) * ((c + 1) *
        ((d + 1) * ArithmeticFunction.sigma 0 m4))) := by
    rw [hsig0, hsig1, hsig2, hsig3]
  calc
    35 * (ArithmeticFunction.sigma 0 n) ^ 3 =
        (a + 1) ^ 3 * (b + 1) ^ 3 * (5 * (c + 1) ^ 3) *
          (7 * (d + 1) ^ 3) * (ArithmeticFunction.sigma 0 m4) ^ 3 := by
            rw [hfull]
            ring
    _ ≤ ((if 2 ∣ n then 8 else 1) * 2 ^ a) *
          ((if 3 ∣ n then 3 else 1) * 3 ^ b) *
          ((if 5 ∣ n then 8 else 5) * 5 ^ c) *
          ((if 7 ∣ n then 8 else 7) * 7 ^ d) * m4 :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul C2 C3) C5) C7) hcore4
    _ = (if 2 ∣ n then 8 else 1) *
          (if 3 ∣ n then 3 else 1) *
          (if 5 ∣ n then 8 else 5) *
          (if 7 ∣ n then 8 else 7) *
          (2 ^ a * (3 ^ b * (5 ^ c * (7 ^ d * m4)))) := by ring
    _ = (if 2 ∣ n then 8 else 1) *
          (if 3 ∣ n then 3 else 1) *
          (if 5 ∣ n then 8 else 5) *
          (if 7 ∣ n then 8 else 7) * n := by
      rw [← hd7, ← hd5, ← hd3, ← hd2]

/-- The class bound specialized to the shifted values `2520*N-k`.
The coefficient depends only on the small-prime divisibility class of `k`,
equivalently on `gcd(k,2520)`. -/
theorem erdos647_gcd_class_cube_bound :
    ∀ N k : ℕ, 1 ≤ N → 0 < k → k < 2520 * N →
      35 * (ArithmeticFunction.sigma 0 (2520 * N - k)) ^ 3 ≤
        (if 2 ∣ k then 8 else 1) *
        (if 3 ∣ k then 3 else 1) *
        (if 5 ∣ k then 8 else 5) *
        (if 7 ∣ k then 8 else 7) * (2520 * N - k) := by
  intro N k hN hk0 hkn
  have hmpos : 1 ≤ 2520 * N - k := by omega
  have hclass := erdos647_small_prime_class_cube_bound (2520 * N - k) hmpos
  have hiff : ∀ p : ℕ, p ∣ 2520 →
      (p ∣ 2520 * N - k ↔ p ∣ k) := by
    intro p hp
    have hbase : p ∣ 2520 * N := Dvd.dvd.mul_right hp N
    constructor
    · intro hshift
      have h := Nat.dvd_sub hbase hshift
      rwa [show 2520 * N - (2520 * N - k) = k by omega] at h
    · intro hpk
      exact Nat.dvd_sub hbase hpk
  simp only [hiff 2 (by norm_num), hiff 3 (by norm_num),
    hiff 5 (by norm_num), hiff 7 (by norm_num)] at hclass
  exact hclass

theorem erdos647_gcd_class_excess_shift_in_cube_prefix :
    ∀ N B k : ℕ, 1 ≤ N → 0 < k → k < 2520 * N →
      B + k < ArithmeticFunction.sigma 0 (2520 * N - k) →
      35 * (B + k) ^ 3 <
        (if 2 ∣ k then 8 else 1) *
        (if 3 ∣ k then 3 else 1) *
        (if 5 ∣ k then 8 else 5) *
        (if 7 ∣ k then 8 else 7) * (2520 * N - k) := by
  intro N B k hN hk0 hkn hfail
  have hclass := erdos647_gcd_class_cube_bound N k hN hk0 hkn
  by_contra hprefix
  push Not at hprefix
  have hmul :
      35 * (ArithmeticFunction.sigma 0 (2520 * N - k)) ^ 3 ≤
        35 * (B + k) ^ 3 := hclass.trans hprefix
  have hpows :
      (ArithmeticFunction.sigma 0 (2520 * N - k)) ^ 3 ≤ (B + k) ^ 3 :=
    le_of_mul_le_mul_left hmul (by norm_num)
  have hbudget : ArithmeticFunction.sigma 0 (2520 * N - k) ≤ B + k :=
    (Nat.pow_le_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hpows
  omega

theorem erdos647_candidate_of_gcd_class_cube_prefix :
    ∀ N : ℕ, 1 ≤ N →
      (∀ k : ℕ, 0 < k → k < 2520 * N →
        35 * (k + 2) ^ 3 <
          (if 2 ∣ k then 8 else 1) *
          (if 3 ∣ k then 3 else 1) *
          (if 5 ∣ k then 8 else 5) *
          (if 7 ∣ k then 8 else 7) * (2520 * N - k) →
        ArithmeticFunction.sigma 0 (2520 * N - k) ≤ k + 2) →
      (⨆ m : Fin (2520 * N),
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ 2520 * N + 2 := by
  intro N hN hprefix
  have hn : 0 < 2520 * N := by omega
  haveI : Nonempty (Fin (2520 * N)) := ⟨⟨0, hn⟩⟩
  have hbudget : ∀ k : ℕ, 0 < k → k < 2520 * N →
      ArithmeticFunction.sigma 0 (2520 * N - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases hk :
        35 * (k + 2) ^ 3 <
          (if 2 ∣ k then 8 else 1) *
          (if 3 ∣ k then 3 else 1) *
          (if 5 ∣ k then 8 else 5) *
          (if 7 ∣ k then 8 else 7) * (2520 * N - k)
    · exact hprefix k hk0 hkn hk
    · push Not at hk
      have hclass := erdos647_gcd_class_cube_bound N k hN hk0 hkn
      have hmul :
          35 * (ArithmeticFunction.sigma 0 (2520 * N - k)) ^ 3 ≤
            35 * (k + 2) ^ 3 := hclass.trans hk
      have hpows :
          (ArithmeticFunction.sigma 0 (2520 * N - k)) ^ 3 ≤ (k + 2) ^ 3 :=
        le_of_mul_le_mul_left hmul (by norm_num)
      exact (Nat.pow_le_pow_iff_left (by norm_num : (3 : ℕ) ≠ 0)).mp hpows
  apply ciSup_le
  intro m
  rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hmpos
  · rw [hm0]
    simp
  · have hmn : (m : ℕ) < 2520 * N := m.isLt
    have hk0 : 0 < 2520 * N - (m : ℕ) := by omega
    have hkn : 2520 * N - (m : ℕ) < 2520 * N := by omega
    have hb := hbudget (2520 * N - (m : ℕ)) hk0 hkn
    have hmk : 2520 * N - (2520 * N - (m : ℕ)) = (m : ℕ) := by omega
    rw [hmk] at hb
    omega
