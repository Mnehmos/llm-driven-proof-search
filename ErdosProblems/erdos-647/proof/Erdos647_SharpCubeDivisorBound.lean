import Mathlib

/-!
# Erdős #647 — the sharp cube divisor bound: 35·τ(n)³ ≤ 1536·n (priority 5)

Snapshots of two statements kernel-verified through the tracked
proof-search pipeline on 2026-07-16.

**Part 1 — the 11-rough core** (`τ(m)³ ≤ m` for 11-rough `m`):

  problem_version_id  a5d294e3-3e54-4cbd-b560-ad089596d057
  episode_id          18e64ee4-8ad6-449d-9692-601331e0ab04
  root_statement_hash 2095ed35da9d7f1324a66da07e672f4abc14a95e634ac90d984d22ab45c51d16
  outcome             kernel_verified (root_proved)
  preverification     ab82548d-ca69-423c-b1ed-70110cafe012 (kernel_pass;
                      one prior round 4887b4e6: nlinarith failed on the
                      cube expansion (n+2)³ ≤ 8(n+1)³ — replaced by the
                      monotone route n+2 ≤ 2(n+1) + Nat.pow_le_pow_left)

**Part 2 — the sharp global bound**:

  problem_version_id  12d9b211-e0ba-4905-a522-65aeb31f5857
  episode_id          77aa1b30-a41f-4dd2-8a08-8fb32228aadc
  root_statement_hash 69b30a0c751831fe92462911b1070229ef47a6396cc1dd36609ee26eb88217ab
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     a8853e24-bac9-463c-8e48-0d28c115ba92 (kernel_pass,
                      first try)

Content: for every `n ≥ 1`,

  `35 · τ(n)³ ≤ 1536 · n`,   i.e.   `τ(n) ≤ (1536/35)^{1/3} · n^{1/3} ≈ 3.53 · n^{1/3}`,

with equality at `n = 2520` (`35 · 48³ = 3 870 720 = 1536 · 2520`,
checked numerically). The proof design supports UNIQUENESS of the
extremal point (each local bound is strict off its extremal exponent,
and the rough core is strict for `m > 1`), but the characterization
`35·τ(n)³ = 1536·n ↔ n = 2520` is NOT yet exported as its own
kernel-verified theorem — until it is, only the inequality is a formal
claim.

Proof: peel the 2-, 3-, 5-, 7-parts and apply the sharp local bounds
`(a+1)³ ≤ 8·2^a` (extremal at a=3), `(b+1)³ ≤ 3·3^b` (b=2),
`5(c+1)³ ≤ 8·5^c` (c=1), `7(d+1)³ ≤ 8·7^d` (d=1) — the extremal
exponents (3,2,1,1) are exactly 2520's factorization — and the 11-rough
core `τ(m)³ ≤ m`, proved by strong induction peeling the minimal prime
`P ≥ 11` at full multiplicity with the per-prime bound `(a+1)³ ≤ P^a`.

**Consequences**:
- POSITIVE LANE: the candidate-certificate prefix shrinks from `2√n`
  to `≈ 3.53·n^{1/3}` — at frontier heights `n ≈ 6×10¹⁷`, a ~520×
  reduction of the finite `native_decide` obligation. The cube-root
  analogue of `erdos647_candidate_of_sqrt_prefix` is the next assembly.
- NEGATIVE LANE: any failed shift satisfies `35(k+2)³ < 1536·n`, so the
  entire obstruction window shrinks to `O(n^{1/3})` as well.
- Upgrades the pairing bound `τ(m) ≤ 2√m` everywhere it was used.

Lean notes: the strong-induction case label for
`Nat.strong_induction_on` is matched with `| _ m ih`; the recurring
self-referential-rewrite trap (`heq : m = m.minFac ^ a * q` rewrites
`m` inside `m.minFac`) is avoided by `set P := m.minFac with hPdef;
clear_value P` BEFORE obtaining the decomposition.
-/

theorem erdos647_rough_cube_bound :
    ∀ m : ℕ, 1 ≤ m → (∀ p : ℕ, p.Prime → p ∣ m → 11 ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ 3 ≤ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hrough
    by_cases h1 : m = 1
    · subst h1
      native_decide
    · have hm2 : 2 ≤ m := by omega
      have hp : m.minFac.Prime := Nat.minFac_prime h1
      have hpd : m.minFac ∣ m := Nat.minFac_dvd m
      have hp11 : 11 ≤ m.minFac := hrough _ hp hpd
      set P := m.minFac with hPdef
      clear_value P
      obtain ⟨a, q, hqnd, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show m ≠ 0 by omega) P hp.ne_one
      have ha1 : 1 ≤ a := by
        by_contra h0
        push_neg at h0
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
`erdos647_rough_cube_bound` verbatim (cross-submission references are
unavailable to tracked replays); this snapshot states it against the
theorem above for readability of the repository artifact. -/
theorem erdos647_sharp_cube_divisor_bound :
    ∀ n : ℕ, 1 ≤ n → 35 * (ArithmeticFunction.sigma 0 n) ^ 3 ≤ 1536 * n := by
  intro n hn
  have L2 : ∀ a : ℕ, (a + 1) ^ 3 ≤ 8 * 2 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ihk =>
      by_cases hk : k ≤ 2
      · interval_cases k <;> norm_num
      · push_neg at hk
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
      · push_neg at hk
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
      · interval_cases k <;> norm_num
      · push_neg at hk
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
      · interval_cases k <;> norm_num
      · push_neg at hk
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
    push_neg at hlt
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
  have hcore4 := erdos647_rough_cube_bound m4 hm4pos hrough4
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
