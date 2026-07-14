import Mathlib

/-!
# Erdős #647 — Theorem 2 (prime-chain reduction), stage k = 8 (final split)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-13.

  problem_version_id  513c65fa-b031-479b-aa97-7d39091e7587
  episode_id          95fae0a4-f448-4236-9039-604e5cb902e7
  root_statement_hash 068b74ebba069c507eb598bade6aced904cb882e6b46745dedaeb1f97052382a
  outcome             kernel_verified (root_proved), pass@1
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: given the stage-1,2,4 output (`p` prime, `2p+1` prime, where
`n = 2q+2` and `q = 2p+1`), the shift-8 divisor budget
(`σ₀(n-8) = σ₀(4p-4) ≤ 10`) forces `p = 2s+1` or `p = 4s+1` for a
prime `s`, via 2-adic decomposition of `p-1`. Budget-surviving pure
powers of two (`p-1 ∈ {8,16,32,64,128}`, i.e. `p ∈ {9,17,33,65,129}`)
are each killed either by `p`'s own primality (9, 33, 65, 129
composite) or by the already-proven primality of `2p+1`
(`2·17+1 = 35` composite).

Chaining the three stages: `n = 2q+2`, `q = 2p+1`, `p = 2s+1` gives
family A `n = 8s+8` with `s, 2s+1, 4s+3, 8s+7` all prime; `p = 4s+1`
gives family B `n = 16s+8` with `s, 4s+1, 8s+3, 16s+7` all prime —
exactly the two admissible prime tuples of Hughes's Theorem 2 and the
Hughes–Kitamura Brun-sieve argument.
-/

theorem erdos647_primechain_stage8 :
    ∀ p : ℕ, 7 ≤ p → p.Prime → (2*p+1).Prime →
      ArithmeticFunction.sigma 0 (4*p - 4) ≤ 10 →
      ∃ s : ℕ, s.Prime ∧ (p = 2*s+1 ∨ p = 4*s+1) := by
  intro p hp7 hpp hq2p1 hbudget
  have hpodd : Odd p := by
    rcases hpp.eq_two_or_odd' with h2 | hodd
    · omega
    · exact hodd
  obtain ⟨t, ht⟩ := hpodd
  have hp1even : (2:ℕ) ∣ (p - 1) := ⟨t, by omega⟩
  obtain ⟨d, v, hvodd, hdv⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show p - 1 ≠ 0 by omega) 2 (by norm_num)
  have hnfull : 4 * p - 4 = 2 ^ (d + 2) * v := by
    rw [show 4 * p - 4 = 4 * (p - 1) by omega, hdv]; ring
  have hv_pos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · exfalso; rw [h0, mul_zero] at hnfull; omega
    · exact h0
  have hcop : Nat.Coprime (2 ^ (d + 2)) v := (Nat.prime_two.coprime_iff_not_dvd.mpr hvodd).pow_left (d + 2)
  have hsig2pow : ArithmeticFunction.sigma 0 (2 ^ (d + 2)) = d + 3 := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.divisors_prime_pow Nat.prime_two, Finset.card_map, Finset.card_range]
  have hsigeq : ArithmeticFunction.sigma 0 (4 * p - 4) = (d + 3) * ArithmeticFunction.sigma 0 v := by
    rw [hnfull, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsig2pow]
  have hsig_v_pos : 1 ≤ ArithmeticFunction.sigma 0 v := by
    rw [ArithmeticFunction.sigma_zero_apply]
    have h1mem : (1:ℕ) ∈ v.divisors := Nat.one_mem_divisors.mpr (by omega)
    exact Finset.card_pos.mpr ⟨1, h1mem⟩
  have hd_le : d ≤ 7 := by
    rw [hsigeq] at hbudget
    have hmul : (d + 3) * 1 ≤ (d + 3) * ArithmeticFunction.sigma 0 v := Nat.mul_le_mul_left (d + 3) hsig_v_pos
    omega
  have hvprime_of_sig2 : ArithmeticFunction.sigma 0 v ≤ 2 → v ≠ 1 → v.Prime := by
    intro hsig_v2 hvne1
    have hset : ({1, v} : Finset ℕ) ⊆ v.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl
      · exact ⟨one_dvd _, by omega⟩
      · exact ⟨dvd_refl _, by omega⟩
    have hcard2 : ({1, v} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have hdeq : v.divisors = ({1, v} : Finset ℕ) := by
      have hcardle : v.divisors.card ≤ ({1, v} : Finset ℕ).card := by
        rw [hcard2, ← ArithmeticFunction.sigma_zero_apply]
        exact hsig_v2
      exact (Finset.eq_of_subset_of_card_le hset hcardle).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro x hxlt hxdvd
    have hxmem : x ∈ v.divisors := Nat.mem_divisors.mpr ⟨hxdvd, by omega⟩
    rw [hdeq] at hxmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
    rcases hxmem with rfl | rfl
    · rfl
    · omega
  interval_cases d
  · exfalso
    norm_num at hdv
    omega
  · rw [hsigeq] at hbudget
    have hsig_v2 : ArithmeticFunction.sigma 0 v ≤ 2 := by norm_num at hbudget; omega
    have hpv2 : p - 1 = 2 * v := by rw [hdv]; ring
    have hvne1 : v ≠ 1 := by
      intro hv1
      rw [hv1] at hpv2
      omega
    have hvprime := hvprime_of_sig2 hsig_v2 hvne1
    exact ⟨v, hvprime, Or.inl (by omega)⟩
  · rw [hsigeq] at hbudget
    have hsig_v2 : ArithmeticFunction.sigma 0 v ≤ 2 := by norm_num at hbudget; omega
    have hpv4 : p - 1 = 4 * v := by rw [hdv]; ring
    have hvne1 : v ≠ 1 := by
      intro hv1
      rw [hv1] at hpv4
      omega
    have hvprime := hvprime_of_sig2 hsig_v2 hvne1
    exact ⟨v, hvprime, Or.inr (by omega)⟩
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_v1 : ArithmeticFunction.sigma 0 v ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : v.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_v1
    have h1mem : (1:ℕ) ∈ v.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hvmem : v ∈ v.divisors := Nat.mem_divisors.mpr ⟨dvd_refl v, by omega⟩
    have hv1 : v = 1 := (Finset.card_le_one.mp hcard1) v hvmem 1 h1mem
    have hpv : p - 1 = 8 := by rw [hdv, hv1]; ring
    have hp9 : p = 9 := by omega
    rw [hp9] at hpp
    norm_num at hpp
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_v1 : ArithmeticFunction.sigma 0 v ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : v.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_v1
    have h1mem : (1:ℕ) ∈ v.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hvmem : v ∈ v.divisors := Nat.mem_divisors.mpr ⟨dvd_refl v, by omega⟩
    have hv1 : v = 1 := (Finset.card_le_one.mp hcard1) v hvmem 1 h1mem
    have hpv : p - 1 = 16 := by rw [hdv, hv1]; ring
    have hp17 : p = 17 := by omega
    rw [hp17] at hq2p1
    norm_num at hq2p1
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_v1 : ArithmeticFunction.sigma 0 v ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : v.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_v1
    have h1mem : (1:ℕ) ∈ v.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hvmem : v ∈ v.divisors := Nat.mem_divisors.mpr ⟨dvd_refl v, by omega⟩
    have hv1 : v = 1 := (Finset.card_le_one.mp hcard1) v hvmem 1 h1mem
    have hpv : p - 1 = 32 := by rw [hdv, hv1]; ring
    have hp33 : p = 33 := by omega
    rw [hp33] at hpp
    norm_num at hpp
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_v1 : ArithmeticFunction.sigma 0 v ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : v.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_v1
    have h1mem : (1:ℕ) ∈ v.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hvmem : v ∈ v.divisors := Nat.mem_divisors.mpr ⟨dvd_refl v, by omega⟩
    have hv1 : v = 1 := (Finset.card_le_one.mp hcard1) v hvmem 1 h1mem
    have hpv : p - 1 = 64 := by rw [hdv, hv1]; ring
    have hp65 : p = 65 := by omega
    rw [hp65] at hpp
    norm_num at hpp
  · exfalso
    rw [hsigeq] at hbudget
    have hsig_v1 : ArithmeticFunction.sigma 0 v ≤ 1 := by norm_num at hbudget; omega
    have hcard1 : v.divisors.card ≤ 1 := by rw [← ArithmeticFunction.sigma_zero_apply]; exact hsig_v1
    have h1mem : (1:ℕ) ∈ v.divisors := Nat.one_mem_divisors.mpr (by omega)
    have hvmem : v ∈ v.divisors := Nat.mem_divisors.mpr ⟨dvd_refl v, by omega⟩
    have hv1 : v = 1 := (Finset.card_le_one.mp hcard1) v hvmem 1 h1mem
    have hpv : p - 1 = 128 := by rw [hdv, hv1]; ring
    have hp129 : p = 129 := by omega
    rw [hp129] at hpp
    norm_num at hpp
