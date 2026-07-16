import Mathlib

/-!
# Erdős #647 — generic rough power divisor bound

Snapshot of the exact statement kernel-verified through the tracked
proof-search pipeline on 2026-07-16.

  problem_version_id  3485cd6c-1875-42e9-9125-20c656a39b49
  episode_id          44b3b927-ae01-4478-8f0b-43f57b871112
  root_statement_hash 33b98cfc81f9f1eac7353f952305af402acef74c8324c5b3510aa4fb390fa474
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     b345a587-0c16-4148-b6bb-92a930307c12 (kernel_pass)

For a positive integer `m`, if every prime divisor of `m` is at least
`2 ^ r`, then the `r`-th power of its divisor count is at most `m`.
This is the generic form of the previously verified 11-rough cube bound
and is the input to the arbitrary-power prefix certificate.

The first preverification job `db04bb84-71db-4967-b16b-09fe66480915`
failed before elaborating the mathematical proof because a PowerShell text
round-trip changed Lean's `·` bullets into invalid bytes.  The identical
locally compiling source was resubmitted through a byte-preserving transport
and passed; the tracked episode used that exact source.
-/

theorem erdos647_rough_power_bound :
    ∀ r m : ℕ,
      0 < r →
      1 ≤ m →
      (∀ p : ℕ, p.Prime → p ∣ m → 2 ^ r ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ r ≤ m := by
  intro r m hr
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hrough
    by_cases h1 : m = 1
    · subst h1
      simp
    · have hm2 : 2 ≤ m := by omega
      have hp : m.minFac.Prime := Nat.minFac_prime h1
      have hpd : m.minFac ∣ m := Nat.minFac_dvd m
      have hpbig : 2 ^ r ≤ m.minFac := hrough _ hp hpd
      set P := m.minFac with hPdef
      clear_value P
      have hP2 : 2 ≤ P := hp.two_le
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
        exact hP2.trans (Nat.le_self_pow (by omega : a ≠ 0) P)
      have hqlt : q < m := by
        have h2 : 1 * q < P ^ a * q := by
          apply Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl q)
          omega
        calc
          q = 1 * q := (one_mul q).symm
          _ < P ^ a * q := h2
          _ = m := heq.symm
      have hqrough : ∀ p : ℕ, p.Prime → p ∣ q → 2 ^ r ≤ p := by
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
      have hT1 : ∀ b : ℕ, (b + 1) ^ r ≤ P ^ b := by
        intro b
        calc
          (b + 1) ^ r ≤ (2 ^ b) ^ r := Nat.pow_le_pow_left (hbinary b) r
          _ = (2 ^ r) ^ b := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
          _ ≤ P ^ b := Nat.pow_le_pow_left hpbig b
      have hcop : Nat.Coprime (P ^ a) q :=
        Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hqnd)
      have hs : ArithmeticFunction.sigma 0 (P ^ a) = a + 1 := by
        rw [ArithmeticFunction.sigma_zero_apply, Nat.divisors_prime_pow hp,
          Finset.card_map, Finset.card_range]
      have hsig : ArithmeticFunction.sigma 0 m =
          (a + 1) * ArithmeticFunction.sigma 0 q := by
        rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hs]
      calc
        (ArithmeticFunction.sigma 0 m) ^ r
            = (a + 1) ^ r * (ArithmeticFunction.sigma 0 q) ^ r := by
                rw [hsig, mul_pow]
        _ ≤ P ^ a * q := Nat.mul_le_mul (hT1 a) hIH
        _ = m := heq.symm
