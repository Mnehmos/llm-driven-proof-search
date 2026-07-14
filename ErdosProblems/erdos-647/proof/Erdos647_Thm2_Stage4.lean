import Mathlib

/-!
# Erdős #647 — Theorem 2 (prime-chain reduction), stage k = 4

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-13.

  problem_version_id  52ff69c0-e7f5-443c-9cc1-14da17c92dd4
  episode_id          57bf2fb3-7a57-4644-b99a-f97ff2aa600c
  root_statement_hash f940625c1484f450d165e8f450a8f8c7eef5a39fc451e5f0f0a70f24f6c97afc
  outcome             kernel_verified (root_proved), pass@1
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: given the stage-1,2 output (`q` prime, `2q+1` prime, where
`n = 2q+2`), the shift-4 divisor budget (`σ₀(n-4) = σ₀(2q-2) ≤ 6`)
forces `q = 2p+1` for a prime `p`, via 2-adic decomposition of `q-1`.
The one budget-surviving exceptional case `q = 17` (i.e. `q-1 = 2⁴`)
is killed by the already-proven fact that `2q+1` is prime
(`2·17+1 = 35 = 5·7` is composite).
-/

theorem erdos647_primechain_stage4 :
    ∀ q : ℕ, 13 ≤ q → q.Prime → (2*q+1).Prime →
      ArithmeticFunction.sigma 0 (2*q - 2) ≤ 6 →
      ∃ p : ℕ, p.Prime ∧ q = 2*p+1 := by
  intro q hq13 hqp hq2p1 hbudget
  have hqodd : Odd q := by
    rcases hqp.eq_two_or_odd' with h2 | hodd
    · omega
    · exact hodd
  obtain ⟨t, ht⟩ := hqodd
  have hq1even : (2:ℕ) ∣ (q - 1) := ⟨t, by omega⟩
  obtain ⟨c, w, hwodd, hcw⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show q - 1 ≠ 0 by omega) 2 (by norm_num)
  have hnfull : 2 * q - 2 = 2 ^ (c + 1) * w := by
    rw [show 2 * q - 2 = 2 * (q - 1) by omega, hcw]; ring
  have hw_pos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · exfalso; rw [h0, mul_zero] at hnfull; omega
    · exact h0
  have hcop : Nat.Coprime (2 ^ (c + 1)) w := (Nat.prime_two.coprime_iff_not_dvd.mpr hwodd).pow_left (c + 1)
  have hsig2pow : ArithmeticFunction.sigma 0 (2 ^ (c + 1)) = c + 2 := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
  have hsigeq : ArithmeticFunction.sigma 0 (2 * q - 2) = (c + 2) * ArithmeticFunction.sigma 0 w := by
    rw [hnfull, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig2pow]
  have hsig_w_pos : 1 ≤ ArithmeticFunction.sigma 0 w := by
    rw [ArithmeticFunction.sigma_zero_apply]
    have h1mem : (1:ℕ) ∈ w.divisors := Nat.one_mem_divisors.mpr (by omega)
    exact Finset.card_pos.mpr ⟨1, h1mem⟩
  have hc_le : c ≤ 4 := by
    rw [hsigeq] at hbudget
    have hmul : (c + 2) * 1 ≤ (c + 2) * ArithmeticFunction.sigma 0 w := Nat.mul_le_mul_left (c + 2) hsig_w_pos
    omega
  interval_cases c
  · exfalso
    norm_num at hcw
    omega
  · rw [hsigeq] at hbudget
    have hsig_w2 : ArithmeticFunction.sigma 0 w ≤ 2 := by norm_num at hbudget; omega
    have hqw2 : q - 1 = 2 * w := by rw [hcw]; ring
    have hwne1 : w ≠ 1 := by
      intro hw1
      rw [hw1] at hqw2
      omega
    have hset : ({1, w} : Finset ℕ) ⊆ w.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, by omega⟩
      · exact ⟨dvd_refl _, by omega⟩
    have hcard2 : ({1, w} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have hdeq : w.divisors = ({1, w} : Finset ℕ) := by
      have hcardle : w.divisors.card ≤ ({1, w} : Finset ℕ).card := by
        rw [hcard2, ← ArithmeticFunction.sigma_zero_apply]
        exact hsig_w2
      exact (Finset.eq_of_subset_of_card_le hset hcardle).symm
    have hwprime : w.Prime := by
      rw [Nat.prime_def_lt]
      refine ⟨by omega, ?_⟩
      intro x hxlt hxdvd
      have hxmem : x ∈ w.divisors := Nat.mem_divisors.mpr ⟨hxdvd, by omega⟩
      rw [hdeq] at hxmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
      rcases hxmem with rfl | rfl
      · rfl
      · omega
    exact ⟨w, hwprime, by omega⟩
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_w1 : ArithmeticFunction.sigma 0 w ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : w.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_w1
    have h1mem : (1:ℕ) ∈ w.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hwmem : w ∈ w.divisors := Nat.mem_divisors.mpr ⟨dvd_refl w, by omega⟩
    have hw1 : w = 1 := (Finset.card_le_one.mp hcard1) w hwmem 1 h1mem
    have hqw : q - 1 = 4 := by rw [hcw, hw1]; ring
    omega
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_w1 : ArithmeticFunction.sigma 0 w ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : w.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_w1
    have h1mem : (1:ℕ) ∈ w.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hwmem : w ∈ w.divisors := Nat.mem_divisors.mpr ⟨dvd_refl w, by omega⟩
    have hw1 : w = 1 := (Finset.card_le_one.mp hcard1) w hwmem 1 h1mem
    have hqw : q - 1 = 8 := by rw [hcw, hw1]; ring
    omega
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_w1 : ArithmeticFunction.sigma 0 w ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : w.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_w1
    have h1mem : (1:ℕ) ∈ w.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hwmem : w ∈ w.divisors := Nat.mem_divisors.mpr ⟨dvd_refl w, by omega⟩
    have hw1 : w = 1 := (Finset.card_le_one.mp hcard1) w hwmem 1 h1mem
    have hqw : q - 1 = 16 := by rw [hcw, hw1]; ring
    have hq17 : q = 17 := by omega
    rw [hq17] at hq2p1
    norm_num at hq2p1
