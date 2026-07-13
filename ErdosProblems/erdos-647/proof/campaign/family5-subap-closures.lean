import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

/-!
# Erdős #647 — Family 5: novel sub-AP congruence closures

Self-contained Lean source (checks against Mathlib with `lake`; no project DB
needed), recovered via `proof_export{episode_id, format: "lean"}` against the
pinned environment (`environment_hash 9e26d28e…`).

Original-search sub-cell closures: each excludes `N ≡ r (mod 46189·p)` for one
extra prime `p ∈ {23,29,31,37,41,43}`, unconditionally for all N (Hughes's
"sub-AP" species, independently discovered against our own frontier). These
are sub-cell closures — they do not shrink the base-46189 41-class count
(only Family 4 does). Named `erdos647_subap_N<residue>`.
-/

theorem erdos647_subap_N5291 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 5291 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 13) ≤ 15 := by
    have hsub : n - 13 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 13, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 5291 := by omega
  have hn13lin : n = 5681 * 471240 * q + 5681 * 2347 + 13 := by rw [hnN, hNeq]; ring
  have hn13 : n - 13 = 5681 * (471240 * q + 2347) := by
    have h1 : n - 13 = 5681 * 471240 * q + 5681 * 2347 := by omega
    rw [h1]; ring
  set eval := 471240 * q + 2347 with heval_def
  have heval2 : 2 ≤ eval := by dsimp [eval]; omega
  have heval_ge : 2347 ≤ eval := by dsimp [eval]; omega
  have hn13ne : n - 13 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 13) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 13) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 13).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn13ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 15 < ArithmeticFunction.sigma 0 (5681 * D) → False := by
    intro D hDdvd hsig
    have hDm : 5681 * D ∣ (n - 13) := by rw [hn13]; exact Nat.mul_dvd_mul_left 5681 hDdvd
    have := hmono (5681 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow13 : ∀ s : ℕ, eval ≠ 13 ^ s := by
    intro s hs
    have heq2 : n - 13 = 13 ^ (s + 1) * 437 := by rw [hn13, hs]; ring
    have hcop : Nat.Coprime (13 ^ (s + 1)) 437 := by
      have h13_437 : Nat.Coprime 13 437 := by norm_num
      exact h13_437.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 437 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 13)]
    have hsig437 : ArithmeticFunction.sigma 0 437 = 4 := by native_decide
    rw [hsig437] at hsigeq
    have hsle : (s + 2) * 4 ≤ 15 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow19 : ∀ s : ℕ, eval ≠ 19 ^ s := by
    intro s hs
    have heq2 : n - 13 = 19 ^ (s + 1) * 299 := by rw [hn13, hs]; ring
    have hcop : Nat.Coprime (19 ^ (s + 1)) 299 := by
      have h19_299 : Nat.Coprime 19 299 := by norm_num
      exact h19_299.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 299 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 19)]
    have hsig299 : ArithmeticFunction.sigma 0 299 = 4 := by native_decide
    rw [hsig299] at hsigeq
    have hsle : (s + 2) * 4 ≤ 15 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow23 : ∀ s : ℕ, eval ≠ 23 ^ s := by
    intro s hs
    have heq2 : n - 13 = 23 ^ (s + 1) * 247 := by rw [hn13, hs]; ring
    have hcop : Nat.Coprime (23 ^ (s + 1)) 247 := by
      have h23_247 : Nat.Coprime 23 247 := by norm_num
      exact h23_247.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 247 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 23)]
    have hsig247 : ArithmeticFunction.sigma 0 247 = 4 := by native_decide
    rw [hsig247] at hsigeq
    have hsle : (s + 2) * 4 ≤ 15 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h13 : 13 ∣ eval
  · by_cases h19 : 19 ∣ eval
    · have h247 : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h19
      exact hclose 247 h247 (by native_decide)
    · by_cases h23 : 23 ∣ eval
      · have h299 : (299:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h23
        exact hclose 299 h299 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 13 (by norm_num) h13 hnopow13
        have hp13cop : Nat.Coprime 13 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h13p : (13 * p) ∣ eval := hp13cop.mul_dvd_of_dvd_of_dvd h13 hpdvd
        have hcop74153 : Nat.Coprime 73853 p := by
          have hfac : (73853:ℕ).primeFactors = {13, 19, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd73853
          have hpmem : p ∈ (73853:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd73853, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h19 hpdvd
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs73853 : ArithmeticFunction.sigma 0 73853 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (5681 * (13 * p)) := by
          have heq : 5681 * (13 * p) = 73853 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop74153, hs73853, hsigp]
          norm_num
        exact hclose (13 * p) h13p hfinal
  · by_cases h19 : 19 ∣ eval
    · by_cases h23 : 23 ∣ eval
      · have h437 : (437:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h19 h23
        exact hclose 437 h437 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 19 (by norm_num) h19 hnopow19
        have hp19cop : Nat.Coprime 19 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h19p : (19 * p) ∣ eval := hp19cop.mul_dvd_of_dvd_of_dvd h19 hpdvd
        have hcop107939 : Nat.Coprime 107939 p := by
          have hfac : (107939:ℕ).primeFactors = {13, 19, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd107939
          have hpmem : p ∈ (107939:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd107939, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact hpne rfl
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs107939 : ArithmeticFunction.sigma 0 107939 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (5681 * (19 * p)) := by
          have heq : 5681 * (19 * p) = 107939 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop107939, hs107939, hsigp]
          norm_num
        exact hclose (19 * p) h19p hfinal
    · by_cases h23 : 23 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 23 (by norm_num) h23 hnopow23
        have hp23cop : Nat.Coprime 23 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h23p : (23 * p) ∣ eval := hp23cop.mul_dvd_of_dvd_of_dvd h23 hpdvd
        have hcop130663 : Nat.Coprime 130663 p := by
          have hfac : (130663:ℕ).primeFactors = {13, 19, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd130663
          have hpmem : p ∈ (130663:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd130663, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact h19 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs130663 : ArithmeticFunction.sigma 0 130663 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (5681 * (23 * p)) := by
          have heq : 5681 * (23 * p) = 130663 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop130663, hs130663, hsigp]
          norm_num
        exact hclose (23 * p) h23p hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcop5681 : Nat.Coprime 5681 p := by
          have hfac : (5681:ℕ).primeFactors = {13, 19, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd5681
          have hpmem : p ∈ (5681:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd5681, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact h19 hpdvd
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs5681 : ArithmeticFunction.sigma 0 5681 = 8 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (5681 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop5681, hs5681, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N36608 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 36608 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 11) ≤ 13 := by
    have hsub : n - 11 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 11, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 36608 := by omega
  have hn11lin : n = 4301 * 622440 * q + 4301 * 21449 + 11 := by rw [hnN, hNeq]; ring
  have hn11 : n - 11 = 4301 * (622440 * q + 21449) := by
    have h1 : n - 11 = 4301 * 622440 * q + 4301 * 21449 := by omega
    rw [h1]; ring
  set eval := 622440 * q + 21449 with heval_def
  have heval2 : 2 ≤ eval := by dsimp [eval]; omega
  have heval_ge : 21449 ≤ eval := by dsimp [eval]; omega
  have hn11ne : n - 11 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 11) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 11) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 11).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn11ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 13 < ArithmeticFunction.sigma 0 (4301 * D) → False := by
    intro D hDdvd hsig
    have hDm : 4301 * D ∣ (n - 11) := by rw [hn11]; exact Nat.mul_dvd_mul_left 4301 hDdvd
    have := hmono (4301 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow11 : ∀ s : ℕ, eval ≠ 11 ^ s := by
    intro s hs
    have heq2 : n - 11 = 11 ^ (s + 1) * 391 := by rw [hn11, hs]; ring
    have hcop : Nat.Coprime (11 ^ (s + 1)) 391 := by
      have h11_391 : Nat.Coprime 11 391 := by norm_num
      exact h11_391.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 11) = (s + 2) * ArithmeticFunction.sigma 0 391 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 11)]
    have hsig391 : ArithmeticFunction.sigma 0 391 = 4 := by native_decide
    rw [hsig391] at hsigeq
    have hsle : (s + 2) * 4 ≤ 13 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow17 : ∀ s : ℕ, eval ≠ 17 ^ s := by
    intro s hs
    have heq2 : n - 11 = 17 ^ (s + 1) * 253 := by rw [hn11, hs]; ring
    have hcop : Nat.Coprime (17 ^ (s + 1)) 253 := by
      have h17_253 : Nat.Coprime 17 253 := by norm_num
      exact h17_253.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 11) = (s + 2) * ArithmeticFunction.sigma 0 253 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 17)]
    have hsig253 : ArithmeticFunction.sigma 0 253 = 4 := by native_decide
    rw [hsig253] at hsigeq
    have hsle : (s + 2) * 4 ≤ 13 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow23 : ∀ s : ℕ, eval ≠ 23 ^ s := by
    intro s hs
    have heq2 : n - 11 = 23 ^ (s + 1) * 187 := by rw [hn11, hs]; ring
    have hcop : Nat.Coprime (23 ^ (s + 1)) 187 := by
      have h23_187 : Nat.Coprime 23 187 := by norm_num
      exact h23_187.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 11) = (s + 2) * ArithmeticFunction.sigma 0 187 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 23)]
    have hsig187 : ArithmeticFunction.sigma 0 187 = 4 := by native_decide
    rw [hsig187] at hsigeq
    have hsle : (s + 2) * 4 ≤ 13 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h11 : 11 ∣ eval
  · by_cases h17 : 17 ∣ eval
    · have h187 : (187:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h11 h17
      exact hclose 187 h187 (by native_decide)
    · by_cases h23 : 23 ∣ eval
      · have h253 : (253:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h11 h23
        exact hclose 253 h253 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 11 (by norm_num) h11 hnopow11
        have hp11cop : Nat.Coprime 11 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h11p : (11 * p) ∣ eval := hp11cop.mul_dvd_of_dvd_of_dvd h11 hpdvd
        have hcop47311 : Nat.Coprime 47311 p := by
          have hfac : (47311:ℕ).primeFactors = {11, 17, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd47311
          have hpmem : p ∈ (47311:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd47311, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h17 hpdvd
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs47311 : ArithmeticFunction.sigma 0 47311 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (4301 * (11 * p)) := by
          have heq : 4301 * (11 * p) = 47311 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop47311, hs47311, hsigp]
          norm_num
        exact hclose (11 * p) h11p hfinal
  · by_cases h17 : 17 ∣ eval
    · by_cases h23 : 23 ∣ eval
      · have h391 : (391:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h17 h23
        exact hclose 391 h391 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 17 (by norm_num) h17 hnopow17
        have hp17cop : Nat.Coprime 17 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h17p : (17 * p) ∣ eval := hp17cop.mul_dvd_of_dvd_of_dvd h17 hpdvd
        have hcop73117 : Nat.Coprime 73117 p := by
          have hfac : (73117:ℕ).primeFactors = {11, 17, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd73117
          have hpmem : p ∈ (73117:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd73117, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact hpne rfl
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs73117 : ArithmeticFunction.sigma 0 73117 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (4301 * (17 * p)) := by
          have heq : 4301 * (17 * p) = 73117 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop73117, hs73117, hsigp]
          norm_num
        exact hclose (17 * p) h17p hfinal
    · by_cases h23 : 23 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 23 (by norm_num) h23 hnopow23
        have hp23cop : Nat.Coprime 23 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h23p : (23 * p) ∣ eval := hp23cop.mul_dvd_of_dvd_of_dvd h23 hpdvd
        have hcop98923 : Nat.Coprime 98923 p := by
          have hfac : (98923:ℕ).primeFactors = {11, 17, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd98923
          have hpmem : p ∈ (98923:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd98923, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact h17 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs98923 : ArithmeticFunction.sigma 0 98923 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (4301 * (23 * p)) := by
          have heq : 4301 * (23 * p) = 98923 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop98923, hs98923, hsigp]
          norm_num
        exact hclose (23 * p) h23p hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcop4301 : Nat.Coprime 4301 p := by
          have hfac : (4301:ℕ).primeFactors = {11, 17, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd4301
          have hpmem : p ∈ (4301:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd4301, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact h17 hpdvd
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs4301 : ArithmeticFunction.sigma 0 4301 = 8 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (4301 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop4301, hs4301, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N13442 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 13442 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 13) ≤ 15 := by
    have hsub : n - 13 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 13, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 13442 := by omega
  have hn13lin : n = 7163 * 471240 * q + 7163 * 4729 + 13 := by rw [hnN, hNeq]; ring
  have hn13 : n - 13 = 7163 * (471240 * q + 4729) := by
    have h1 : n - 13 = 7163 * 471240 * q + 7163 * 4729 := by omega
    rw [h1]; ring
  set eval := 471240 * q + 4729 with heval_def
  have heval2 : 2 ≤ eval := by dsimp [eval]; omega
  have heval_ge : 4729 ≤ eval := by dsimp [eval]; omega
  have hn13ne : n - 13 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 13) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 13) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 13).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn13ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 15 < ArithmeticFunction.sigma 0 (7163 * D) → False := by
    intro D hDdvd hsig
    have hDm : 7163 * D ∣ (n - 13) := by rw [hn13]; exact Nat.mul_dvd_mul_left 7163 hDdvd
    have := hmono (7163 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow13 : ∀ s : ℕ, eval ≠ 13 ^ s := by
    intro s hs
    have heq2 : n - 13 = 13 ^ (s + 1) * 551 := by rw [hn13, hs]; ring
    have hcop : Nat.Coprime (13 ^ (s + 1)) 551 := by
      have h13_551 : Nat.Coprime 13 551 := by norm_num
      exact h13_551.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 551 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 13)]
    have hsig551 : ArithmeticFunction.sigma 0 551 = 4 := by native_decide
    rw [hsig551] at hsigeq
    have hsle : (s + 2) * 4 ≤ 15 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow19 : ∀ s : ℕ, eval ≠ 19 ^ s := by
    intro s hs
    have heq2 : n - 13 = 19 ^ (s + 1) * 377 := by rw [hn13, hs]; ring
    have hcop : Nat.Coprime (19 ^ (s + 1)) 377 := by
      have h19_377 : Nat.Coprime 19 377 := by norm_num
      exact h19_377.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 377 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 19)]
    have hsig377 : ArithmeticFunction.sigma 0 377 = 4 := by native_decide
    rw [hsig377] at hsigeq
    have hsle : (s + 2) * 4 ≤ 15 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow29 : ∀ s : ℕ, eval ≠ 29 ^ s := by
    intro s hs
    have heq2 : n - 13 = 29 ^ (s + 1) * 247 := by rw [hn13, hs]; ring
    have hcop : Nat.Coprime (29 ^ (s + 1)) 247 := by
      have h29_247 : Nat.Coprime 29 247 := by norm_num
      exact h29_247.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 247 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 29)]
    have hsig247 : ArithmeticFunction.sigma 0 247 = 4 := by native_decide
    rw [hsig247] at hsigeq
    have hsle : (s + 2) * 4 ≤ 15 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h13 : 13 ∣ eval
  · by_cases h19 : 19 ∣ eval
    · have h247 : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h19
      exact hclose 247 h247 (by native_decide)
    · by_cases h29 : 29 ∣ eval
      · have h377 : (377:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h29
        exact hclose 377 h377 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 13 (by norm_num) h13 hnopow13
        have hp13cop : Nat.Coprime 13 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h13p : (13 * p) ∣ eval := hp13cop.mul_dvd_of_dvd_of_dvd h13 hpdvd
        have hcop93119 : Nat.Coprime 93119 p := by
          have hfac : (93119:ℕ).primeFactors = {13, 19, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd93119
          have hpmem : p ∈ (93119:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd93119, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h19 hpdvd
          · exact h29 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs93119 : ArithmeticFunction.sigma 0 93119 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (7163 * (13 * p)) := by
          have heq : 7163 * (13 * p) = 93119 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop93119, hs93119, hsigp]
          norm_num
        exact hclose (13 * p) h13p hfinal
  · by_cases h19 : 19 ∣ eval
    · by_cases h29 : 29 ∣ eval
      · have h551 : (551:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h19 h29
        exact hclose 551 h551 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 19 (by norm_num) h19 hnopow19
        have hp19cop : Nat.Coprime 19 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h19p : (19 * p) ∣ eval := hp19cop.mul_dvd_of_dvd_of_dvd h19 hpdvd
        have hcop136097 : Nat.Coprime 136097 p := by
          have hfac : (136097:ℕ).primeFactors = {13, 19, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd136097
          have hpmem : p ∈ (136097:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd136097, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact hpne rfl
          · exact h29 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs136097 : ArithmeticFunction.sigma 0 136097 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (7163 * (19 * p)) := by
          have heq : 7163 * (19 * p) = 136097 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop136097, hs136097, hsigp]
          norm_num
        exact hclose (19 * p) h19p hfinal
    · by_cases h29 : 29 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 29 (by norm_num) h29 hnopow29
        have hp29cop : Nat.Coprime 29 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h29p : (29 * p) ∣ eval := hp29cop.mul_dvd_of_dvd_of_dvd h29 hpdvd
        have hcop207727 : Nat.Coprime 207727 p := by
          have hfac : (207727:ℕ).primeFactors = {13, 19, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd207727
          have hpmem : p ∈ (207727:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd207727, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact h19 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs207727 : ArithmeticFunction.sigma 0 207727 = 12 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (7163 * (29 * p)) := by
          have heq : 7163 * (29 * p) = 207727 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop207727, hs207727, hsigp]
          norm_num
        exact hclose (29 * p) h29p hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcop7163 : Nat.Coprime 7163 p := by
          have hfac : (7163:ℕ).primeFactors = {13, 19, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd7163
          have hpmem : p ∈ (7163:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd7163, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h13 hpdvd
          · exact h19 hpdvd
          · exact h29 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs7163 : ArithmeticFunction.sigma 0 7163 = 8 := by native_decide
        have hfinal : 15 < ArithmeticFunction.sigma 0 (7163 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop7163, hs7163, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N24453 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 24453 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 11) ≤ 13 := by
    have hsub : n - 11 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 11, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 24453 := by omega
  have hn11lin : n = 5423 * 622440 * q + 5423 * 11363 + 11 := by rw [hnN, hNeq]; ring
  have hn11 : n - 11 = 5423 * (622440 * q + 11363) := by
    have h1 : n - 11 = 5423 * 622440 * q + 5423 * 11363 := by omega
    rw [h1]; ring
  set eval := 622440 * q + 11363 with heval_def
  have heval2 : 2 ≤ eval := by dsimp [eval]; omega
  have heval_ge : 11363 ≤ eval := by dsimp [eval]; omega
  have hn11ne : n - 11 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 11) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 11) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 11).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn11ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 13 < ArithmeticFunction.sigma 0 (5423 * D) → False := by
    intro D hDdvd hsig
    have hDm : 5423 * D ∣ (n - 11) := by rw [hn11]; exact Nat.mul_dvd_mul_left 5423 hDdvd
    have := hmono (5423 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow11 : ∀ s : ℕ, eval ≠ 11 ^ s := by
    intro s hs
    have heq2 : n - 11 = 11 ^ (s + 1) * 493 := by rw [hn11, hs]; ring
    have hcop : Nat.Coprime (11 ^ (s + 1)) 493 := by
      have h11_493 : Nat.Coprime 11 493 := by norm_num
      exact h11_493.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 11) = (s + 2) * ArithmeticFunction.sigma 0 493 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 11)]
    have hsig493 : ArithmeticFunction.sigma 0 493 = 4 := by native_decide
    rw [hsig493] at hsigeq
    have hsle : (s + 2) * 4 ≤ 13 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow17 : ∀ s : ℕ, eval ≠ 17 ^ s := by
    intro s hs
    have heq2 : n - 11 = 17 ^ (s + 1) * 319 := by rw [hn11, hs]; ring
    have hcop : Nat.Coprime (17 ^ (s + 1)) 319 := by
      have h17_319 : Nat.Coprime 17 319 := by norm_num
      exact h17_319.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 11) = (s + 2) * ArithmeticFunction.sigma 0 319 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 17)]
    have hsig319 : ArithmeticFunction.sigma 0 319 = 4 := by native_decide
    rw [hsig319] at hsigeq
    have hsle : (s + 2) * 4 ≤ 13 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow29 : ∀ s : ℕ, eval ≠ 29 ^ s := by
    intro s hs
    have heq2 : n - 11 = 29 ^ (s + 1) * 187 := by rw [hn11, hs]; ring
    have hcop : Nat.Coprime (29 ^ (s + 1)) 187 := by
      have h29_187 : Nat.Coprime 29 187 := by norm_num
      exact h29_187.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 11) = (s + 2) * ArithmeticFunction.sigma 0 187 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 29)]
    have hsig187 : ArithmeticFunction.sigma 0 187 = 4 := by native_decide
    rw [hsig187] at hsigeq
    have hsle : (s + 2) * 4 ≤ 13 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h11 : 11 ∣ eval
  · by_cases h17 : 17 ∣ eval
    · have h187 : (187:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h11 h17
      exact hclose 187 h187 (by native_decide)
    · by_cases h29 : 29 ∣ eval
      · have h319 : (319:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h11 h29
        exact hclose 319 h319 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 11 (by norm_num) h11 hnopow11
        have hp11cop : Nat.Coprime 11 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h11p : (11 * p) ∣ eval := hp11cop.mul_dvd_of_dvd_of_dvd h11 hpdvd
        have hcop59653 : Nat.Coprime 59653 p := by
          have hfac : (59653:ℕ).primeFactors = {11, 17, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd59653
          have hpmem : p ∈ (59653:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd59653, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h17 hpdvd
          · exact h29 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs59653 : ArithmeticFunction.sigma 0 59653 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (5423 * (11 * p)) := by
          have heq : 5423 * (11 * p) = 59653 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop59653, hs59653, hsigp]
          norm_num
        exact hclose (11 * p) h11p hfinal
  · by_cases h17 : 17 ∣ eval
    · by_cases h29 : 29 ∣ eval
      · have h493 : (493:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h17 h29
        exact hclose 493 h493 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 17 (by norm_num) h17 hnopow17
        have hp17cop : Nat.Coprime 17 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h17p : (17 * p) ∣ eval := hp17cop.mul_dvd_of_dvd_of_dvd h17 hpdvd
        have hcop92191 : Nat.Coprime 92191 p := by
          have hfac : (92191:ℕ).primeFactors = {11, 17, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd92191
          have hpmem : p ∈ (92191:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd92191, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact hpne rfl
          · exact h29 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs92191 : ArithmeticFunction.sigma 0 92191 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (5423 * (17 * p)) := by
          have heq : 5423 * (17 * p) = 92191 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop92191, hs92191, hsigp]
          norm_num
        exact hclose (17 * p) h17p hfinal
    · by_cases h29 : 29 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 29 (by norm_num) h29 hnopow29
        have hp29cop : Nat.Coprime 29 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne)
        have h29p : (29 * p) ∣ eval := hp29cop.mul_dvd_of_dvd_of_dvd h29 hpdvd
        have hcop157267 : Nat.Coprime 157267 p := by
          have hfac : (157267:ℕ).primeFactors = {11, 17, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd157267
          have hpmem : p ∈ (157267:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd157267, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact h17 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs157267 : ArithmeticFunction.sigma 0 157267 = 12 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (5423 * (29 * p)) := by
          have heq : 5423 * (29 * p) = 157267 * p := by ring
          rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop157267, hs157267, hsigp]
          norm_num
        exact hclose (29 * p) h29p hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcop5423 : Nat.Coprime 5423 p := by
          have hfac : (5423:ℕ).primeFactors = {11, 17, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd5423
          have hpmem : p ∈ (5423:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd5423, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h11 hpdvd
          · exact h17 hpdvd
          · exact h29 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs5423 : ArithmeticFunction.sigma 0 5423 = 8 := by native_decide
        have hfinal : 13 < ArithmeticFunction.sigma 0 (5423 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop5423, hs5423, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N9009 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1986127 = 9009 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 13) ≤ 15 := (by have hsub : n - 13 < n := (by omega); let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x; have hbdd : BddAbove (Set.range f) := (by refine ⟨2 * n, ?_⟩; rintro y ⟨x, rfl⟩; dsimp [f]; rw [ArithmeticFunction.sigma_zero_apply]; have hc := Nat.card_divisors_le_self (x : ℕ); have hx : (x : ℕ) < n := x.isLt; omega); let mm : Fin n := ⟨n - 13, hsub⟩; have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H; dsimp [f, mm] at hm; omega)
  set q := N / 1986127 with hq_def
  have hNeq : N = 1986127 * q + 9009 := (by omega)
  have hn13 : n - 13 = 9503 * (526680 * q + 2389) := (by have h1 : n - 13 = 9503 * 526680 * q + 9503 * 2389 := (by omega); rw [h1]; ring)
  set eval := 526680 * q + 2389 with heval_def
  have heval2 : 2 ≤ eval := (by dsimp [eval]; omega)
  have heval_ge : 2389 ≤ eval := (by dsimp [eval]; omega)
  have hn13ne : n - 13 ≠ 0 := (by omega)
  have hmono : ∀ a : ℕ, a ∣ (n - 13) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 13) := (by intro a hadvd; have hsub2 : a.divisors ⊆ (n - 13).divisors := (by intro d hd; rw [Nat.mem_divisors] at hd ⊢; exact ⟨hd.1.trans hadvd, hn13ne⟩); rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]; exact Finset.card_le_card hsub2)
  have hclose : ∀ D : ℕ, D ∣ eval → 15 < ArithmeticFunction.sigma 0 (9503 * D) → False := (by intro D hDdvd hsig; have hDm : 9503 * D ∣ (n - 13) := (by rw [hn13]; exact Nat.mul_dvd_mul_left 9503 hDdvd); have := hmono (9503 * D) hDm; omega)
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) → ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := (by intro p hp hpdvd hnotpow; by_contra hnone; push_neg at hnone; have heval0 : eval ≠ 0 := (by omega); have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd); exact hnotpow _ hpow)
  have hnopow13 : ∀ s : ℕ, eval ≠ 13 ^ s := (by intro s hs; have heq2 : n - 13 = 13 ^ (s + 1) * 731 := (by rw [hn13, hs]; ring); have hcop : Nat.Coprime (13 ^ (s + 1)) 731 := (by have h13_731 : Nat.Coprime 13 731 := (by norm_num); exact h13_731.pow_left (s + 1)); have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 731 := (by rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 13)]); have hsig731 : ArithmeticFunction.sigma 0 731 = 4 := (by native_decide); rw [hsig731] at hsigeq; have hsle : (s + 2) * 4 ≤ 15 := (by rw [← hsigeq]; exact shift); have hsbound : s ≤ 1 := (by omega); interval_cases s <;> (norm_num at hs; omega))
  have hnopow17 : ∀ s : ℕ, eval ≠ 17 ^ s := (by intro s hs; have heq2 : n - 13 = 17 ^ (s + 1) * 559 := (by rw [hn13, hs]; ring); have hcop : Nat.Coprime (17 ^ (s + 1)) 559 := (by have h17_559 : Nat.Coprime 17 559 := (by norm_num); exact h17_559.pow_left (s + 1)); have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 559 := (by rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 17)]); have hsig559 : ArithmeticFunction.sigma 0 559 = 4 := (by native_decide); rw [hsig559] at hsigeq; have hsle : (s + 2) * 4 ≤ 15 := (by rw [← hsigeq]; exact shift); have hsbound : s ≤ 1 := (by omega); interval_cases s <;> (norm_num at hs; omega))
  have hnopow43 : ∀ s : ℕ, eval ≠ 43 ^ s := (by intro s hs; have heq2 : n - 13 = 43 ^ (s + 1) * 221 := (by rw [hn13, hs]; ring); have hcop : Nat.Coprime (43 ^ (s + 1)) 221 := (by have h43_221 : Nat.Coprime 43 221 := (by norm_num); exact h43_221.pow_left (s + 1)); have hsigeq : ArithmeticFunction.sigma 0 (n - 13) = (s + 2) * ArithmeticFunction.sigma 0 221 := (by rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 43)]); have hsig221 : ArithmeticFunction.sigma 0 221 = 4 := (by native_decide); rw [hsig221] at hsigeq; have hsle : (s + 2) * 4 ≤ 15 := (by rw [← hsigeq]; exact shift); have hsbound : s ≤ 1 := (by omega); interval_cases s <;> (norm_num at hs; omega))
  exact (if h13 : 13 ∣ eval then (if h17 : 17 ∣ eval then (by have h221 : (221:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h17; exact hclose 221 h221 (by native_decide)) else (if h43 : 43 ∣ eval then (by have h559 : (559:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h13 h43; exact hclose 559 h559 (by native_decide)) else (by obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 13 (by norm_num) h13 hnopow13; have hp13cop : Nat.Coprime 13 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne); have h13p : (13 * p) ∣ eval := hp13cop.mul_dvd_of_dvd_of_dvd h13 hpdvd; have hcop123539 : Nat.Coprime 123539 p := (by have hfac : (123539:ℕ).primeFactors = {13, 17, 43} := (by native_decide); refine ((hp.coprime_iff_not_dvd).mpr ?_).symm; intro hpdvd123539; have hpmem : p ∈ (123539:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd123539, by norm_num⟩; rw [hfac] at hpmem; simp at hpmem; rcases hpmem with rfl | rfl | rfl <;> first | exact hpne rfl | exact h17 hpdvd | exact h43 hpdvd); have hsigp : ArithmeticFunction.sigma 0 p = 2 := (by rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]); have hs123539 : ArithmeticFunction.sigma 0 123539 = 12 := (by native_decide); have hfinal : 15 < ArithmeticFunction.sigma 0 (9503 * (13 * p)) := (by have heq : 9503 * (13 * p) = 123539 * p := (by ring); rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop123539, hs123539, hsigp]; norm_num); exact hclose (13 * p) h13p hfinal))) else (if h17 : 17 ∣ eval then (if h43 : 43 ∣ eval then (by have h731 : (731:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h17 h43; exact hclose 731 h731 (by native_decide)) else (by obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 17 (by norm_num) h17 hnopow17; have hp17cop : Nat.Coprime 17 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne); have h17p : (17 * p) ∣ eval := hp17cop.mul_dvd_of_dvd_of_dvd h17 hpdvd; have hcop161551 : Nat.Coprime 161551 p := (by have hfac : (161551:ℕ).primeFactors = {13, 17, 43} := (by native_decide); refine ((hp.coprime_iff_not_dvd).mpr ?_).symm; intro hpdvd161551; have hpmem : p ∈ (161551:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd161551, by norm_num⟩; rw [hfac] at hpmem; simp at hpmem; rcases hpmem with rfl | rfl | rfl <;> first | exact h13 hpdvd | exact hpne rfl | exact h43 hpdvd); have hsigp : ArithmeticFunction.sigma 0 p = 2 := (by rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]); have hs161551 : ArithmeticFunction.sigma 0 161551 = 12 := (by native_decide); have hfinal : 15 < ArithmeticFunction.sigma 0 (9503 * (17 * p)) := (by have heq : 9503 * (17 * p) = 161551 * p := (by ring); rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop161551, hs161551, hsigp]; norm_num); exact hclose (17 * p) h17p hfinal)) else (if h43 : 43 ∣ eval then (by obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 43 (by norm_num) h43 hnopow43; have hp43cop : Nat.Coprime 43 p := (Nat.coprime_primes (by norm_num) hp).mpr (Ne.symm hpne); have h43p : (43 * p) ∣ eval := hp43cop.mul_dvd_of_dvd_of_dvd h43 hpdvd; have hcop408629 : Nat.Coprime 408629 p := (by have hfac : (408629:ℕ).primeFactors = {13, 17, 43} := (by native_decide); refine ((hp.coprime_iff_not_dvd).mpr ?_).symm; intro hpdvd408629; have hpmem : p ∈ (408629:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd408629, by norm_num⟩; rw [hfac] at hpmem; simp at hpmem; rcases hpmem with rfl | rfl | rfl <;> first | exact h13 hpdvd | exact h17 hpdvd | exact hpne rfl); have hsigp : ArithmeticFunction.sigma 0 p = 2 := (by rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]); have hs408629 : ArithmeticFunction.sigma 0 408629 = 12 := (by native_decide); have hfinal : 15 < ArithmeticFunction.sigma 0 (9503 * (43 * p)) := (by have heq : 9503 * (43 * p) = 408629 * p := (by ring); rw [heq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop408629, hs408629, hsigp]; norm_num); exact hclose (43 * p) h43p hfinal) else (by obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega); have hcop9503 : Nat.Coprime 9503 p := (by have hfac : (9503:ℕ).primeFactors = {13, 17, 43} := (by native_decide); refine ((hp.coprime_iff_not_dvd).mpr ?_).symm; intro hpdvd9503; have hpmem : p ∈ (9503:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd9503, by norm_num⟩; rw [hfac] at hpmem; simp at hpmem; rcases hpmem with rfl | rfl | rfl <;> first | exact h13 hpdvd | exact h17 hpdvd | exact h43 hpdvd); have hsigp : ArithmeticFunction.sigma 0 p = 2 := (by rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]); have hs9503 : ArithmeticFunction.sigma 0 9503 = 8 := (by native_decide); have hfinal : 15 < ArithmeticFunction.sigma 0 (9503 * p) := (by rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop9503, hs9503, hsigp]; norm_num); exact hclose p hpdvd hfinal))))

theorem erdos647_subap_N18733 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1708993 = 18733 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 7) ≤ 9 := by
    have hsub : n - 7 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 7, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1708993 with hq_def
  have hNeq : N = 1708993 * q + 18733 := by omega
  have hn7lin : n = 4921 * 875160 * q + 4921 * 9593 + 7 := by rw [hnN, hNeq]; ring
  have hn7 : n - 7 = 4921 * (875160 * q + 9593) := by
    have h1 : n - 7 = 4921 * 875160 * q + 4921 * 9593 := by omega
    rw [h1]; ring
  set eval := 875160 * q + 9593 with heval_def
  have heval2 : 2 ≤ eval := by dsimp [eval]; omega
  have hn7ne : n - 7 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 7) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 7) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 7).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn7ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 9 < ArithmeticFunction.sigma 0 (4921 * D) → False := by
    intro D hDdvd hsig
    have hDm : 4921 * D ∣ (n - 7) := by rw [hn7]; exact Nat.mul_dvd_mul_left 4921 hDdvd
    have := hmono (4921 * D) hDm
    omega
  by_cases h7 : 7 ∣ eval
  · exact hclose 7 h7 (by native_decide)
  · by_cases h19 : 19 ∣ eval
    · exact hclose 19 h19 (by native_decide)
    · by_cases h37 : 37 ∣ eval
      · exact hclose 37 h37 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcop4921 : Nat.Coprime 4921 p := by
          have hfac : (4921:ℕ).primeFactors = {7, 19, 37} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvd4921
          have hpmem : p ∈ (4921:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd4921, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h7 hpdvd
          · exact h19 hpdvd
          · exact h37 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hs4921 : ArithmeticFunction.sigma 0 4921 = 8 := by native_decide
        have hfinal : 9 < ArithmeticFunction.sigma 0 (4921 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop4921, hs4921, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N4862 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 4862 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 4862 := by omega
  have hn2 : n - 2 = 46 * (58198140 * q + 266353) := by
    have h1 : n - 2 = 46 * 58198140 * q + 46 * 266353 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 266353 with heval_def
  have heval_ge : 266353 ≤ eval := by dsimp [eval]; omega
  have hn2ne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hn2ne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (46 * D) → False := by
    intro D hDdvd hsig
    have hDm : 46 * D ∣ (n - 2) := by rw [hn2]; exact Nat.mul_dvd_mul_left 46 hDdvd
    have := hmono (46 * D) hDm
    omega
  by_cases h2 : 2 ∣ eval
  · exact hclose 2 h2 (by native_decide)
  · by_cases h23 : 23 ∣ eval
    · exact hclose 23 h23 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcop46 : Nat.Coprime 46 p := by
        have hfac : (46:ℕ).primeFactors = {2, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvd46
        have hpmem : p ∈ (46:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd46, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact h2 hpdvd
        · exact h23 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hs46 : ArithmeticFunction.sigma 0 46 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (46 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop46, hs46, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N12155 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1708993 = 12155 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1708993 with hq_def
  have hNeq : N = 1708993 * q + 12155 := by omega
  have hnk : n - 2 = 74 * (58198140 * q + 413927) := by
    have h1 : n - 2 = 74 * 58198140 * q + 74 * 413927 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 413927 with heval_def
  have heval_ge : 413927 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (74 * D) → False := by
    intro D hDdvd hsig
    have hDm : 74 * D ∣ (n - 2) := by rw [hnk]; exact Nat.mul_dvd_mul_left 74 hDdvd
    have := hmono (74 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 37 ∣ eval
    · exact hclose 37 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 74 p := by
        have hfac : (74:ℕ).primeFactors = {2, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (74:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 74 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (74 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N858 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 858 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 858 := by omega
  have hnk : n - 3 = 93 * (38798760 * q + 23249) := by
    have h1 : n - 3 = 93 * 38798760 * q + 93 * 23249 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 23249 with heval_def
  have heval_ge : 23249 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (93 * D) → False := by
    intro D hDdvd hsig
    have hDm : 93 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 93 hDdvd
    have := hmono (93 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 31 ∣ eval
    · exact hclose 31 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 93 p := by
        have hfac : (93:ℕ).primeFactors = {3, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (93:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 93 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (93 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N10582_mod1062347 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 10582 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 10582 := by omega
  have hnk : n - 3 = 69 * (38798760 * q + 386473) := by
    have h1 : n - 3 = 69 * 38798760 * q + 69 * 386473 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 386473 with heval_def
  have heval_ge : 386473 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (69 * D) → False := by
    intro D hDdvd hsig
    have hDm : 69 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 69 hDdvd
    have := hmono (69 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 23 ∣ eval
    · exact hclose 23 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 69 p := by
        have hfac : (69:ℕ).primeFactors = {3, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (69:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 69 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (69 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N27170 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 27170 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 27170 := by omega
  have hnk : n - 2 = 62 * (58198140 * q + 1104329) := by
    have h1 : n - 2 = 62 * 58198140 * q + 62 * 1104329 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 1104329 with heval_def
  have heval_ge : 1104329 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (62 * D) → False := by
    intro D hDdvd hsig
    have hDm : 62 * D ∣ (n - 2) := by rw [hnk]; exact Nat.mul_dvd_mul_left 62 hDdvd
    have := hmono (62 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 31 ∣ eval
    · exact hclose 31 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 62 p := by
        have hfac : (62:ℕ).primeFactors = {2, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (62:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 62 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (62 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N35321 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 35321 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 35321 := by omega
  have hnk : n - 3 = 87 * (38798760 * q + 1023091) := by
    have h1 : n - 3 = 87 * 38798760 * q + 87 * 1023091 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 1023091 with heval_def
  have heval_ge : 1023091 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (87 * D) → False := by
    intro D hDdvd hsig
    have hDm : 87 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 87 hDdvd
    have := hmono (87 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 29 ∣ eval
    · exact hclose 29 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 87 p := by
        have hfac : (87:ℕ).primeFactors = {3, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (87:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 87 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (87 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N29601 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 29601 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 26) ≤ 28 := by
    have hsub : n - 26 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 26, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 29601 := by omega
  have hnk : n - 26 = 15314 * (235620 * q + 4871) := by
    have h1 : n - 26 = 15314 * 235620 * q + 15314 * 4871 := by omega
    rw [h1]; ring
  set eval := 235620 * q + 4871 with heval_def
  have heval_ge : 4871 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 26 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 26) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 26) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 26).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 28 < ArithmeticFunction.sigma 0 (15314 * D) → False := by
    intro D hDdvd hsig
    have hDm : 15314 * D ∣ (n - 26) := by rw [hnk]; exact Nat.mul_dvd_mul_left 15314 hDdvd
    have := hmono (15314 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 2 ^ s := by
    intro s hs
    have heq2 : n - 26 = 2 ^ (s + 1) * 7657 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (2 ^ (s + 1)) 7657 := by
      have hbase : Nat.Coprime 2 7657 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 7657 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 2)]
    have hsigX : ArithmeticFunction.sigma 0 7657 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 13 ^ s := by
    intro s hs
    have heq2 : n - 26 = 13 ^ (s + 1) * 1178 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (13 ^ (s + 1)) 1178 := by
      have hbase : Nat.Coprime 13 1178 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 1178 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 13)]
    have hsigX : ArithmeticFunction.sigma 0 1178 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowC : ∀ s : ℕ, eval ≠ 19 ^ s := by
    intro s hs
    have heq2 : n - 26 = 19 ^ (s + 1) * 806 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (19 ^ (s + 1)) 806 := by
      have hbase : Nat.Coprime 19 806 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 806 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 19)]
    have hsigX : ArithmeticFunction.sigma 0 806 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowD : ∀ s : ℕ, eval ≠ 31 ^ s := by
    intro s hs
    have heq2 : n - 26 = 31 ^ (s + 1) * 494 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (31 ^ (s + 1)) 494 := by
      have hbase : Nat.Coprime 31 494 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 494 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 31)]
    have hsigX : ArithmeticFunction.sigma 0 494 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h1 : 2 ∣ eval
  · by_cases h2 : 13 ∣ eval
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 31 ∣ eval
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
      · by_cases h4 : 31 ∣ eval
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 31 ∣ eval
        · have hpair : (38:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3
          exact hclose 38 hpair (by native_decide)
        · have hpair : (38:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3
          exact hclose 38 hpair (by native_decide)
      · by_cases h4 : 31 ∣ eval
        · have hpair : (62:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h4
          exact hclose 62 hpair (by native_decide)
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 2 (by norm_num) h1 hnopowA
          have hcopg : Nat.Coprime 15314 p := by
            have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact hpne rfl
            · exact h2 hpdvd
            · exact h3 hpdvd
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
  · by_cases h2 : 13 ∣ eval
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 31 ∣ eval
        · have hpair : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
          exact hclose 247 hpair (by native_decide)
        · have hpair : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
          exact hclose 247 hpair (by native_decide)
      · by_cases h4 : 31 ∣ eval
        · have hpair : (403:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h4
          exact hclose 403 hpair (by native_decide)
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 13 (by norm_num) h2 hnopowB
          have hcopg : Nat.Coprime 15314 p := by
            have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact hpne rfl
            · exact h3 hpdvd
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 31 ∣ eval
        · have hpair : (589:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4
          exact hclose 589 hpair (by native_decide)
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 19 (by norm_num) h3 hnopowC
          have hcopg : Nat.Coprime 15314 p := by
            have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact h2 hpdvd
            · exact hpne rfl
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
      · by_cases h4 : 31 ∣ eval
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 31 (by norm_num) h4 hnopowD
          have hcopg : Nat.Coprime 15314 p := by
            have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact h2 hpdvd
            · exact h3 hpdvd
            · exact hpne rfl
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
        · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
          have hcopg : Nat.Coprime 15314 p := by
            have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact h2 hpdvd
            · exact h3 hpdvd
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal

theorem erdos647_subap_N10582_mod1062347_alt :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 10582 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 26) ≤ 28 := by
    have hsub : n - 26 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 26, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 10582 := by omega
  have hnk : n - 26 = 11362 * (235620 * q + 2347) := by
    have h1 : n - 26 = 11362 * 235620 * q + 11362 * 2347 := by omega
    rw [h1]; ring
  set eval := 235620 * q + 2347 with heval_def
  have heval_ge : 2347 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 26 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 26) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 26) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 26).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 28 < ArithmeticFunction.sigma 0 (11362 * D) → False := by
    intro D hDdvd hsig
    have hDm : 11362 * D ∣ (n - 26) := by rw [hnk]; exact Nat.mul_dvd_mul_left 11362 hDdvd
    have := hmono (11362 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 2 ^ s := by
    intro s hs
    have heq2 : n - 26 = 2 ^ (s + 1) * 5681 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (2 ^ (s + 1)) 5681 := by
      have hbase : Nat.Coprime 2 5681 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 5681 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 2)]
    have hsigX : ArithmeticFunction.sigma 0 5681 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 13 ^ s := by
    intro s hs
    have heq2 : n - 26 = 13 ^ (s + 1) * 874 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (13 ^ (s + 1)) 874 := by
      have hbase : Nat.Coprime 13 874 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 874 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 13)]
    have hsigX : ArithmeticFunction.sigma 0 874 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowC : ∀ s : ℕ, eval ≠ 19 ^ s := by
    intro s hs
    have heq2 : n - 26 = 19 ^ (s + 1) * 598 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (19 ^ (s + 1)) 598 := by
      have hbase : Nat.Coprime 19 598 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 598 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 19)]
    have hsigX : ArithmeticFunction.sigma 0 598 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowD : ∀ s : ℕ, eval ≠ 23 ^ s := by
    intro s hs
    have heq2 : n - 26 = 23 ^ (s + 1) * 494 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (23 ^ (s + 1)) 494 := by
      have hbase : Nat.Coprime 23 494 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 494 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 23)]
    have hsigX : ArithmeticFunction.sigma 0 494 = 8 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h1 : 2 ∣ eval
  · by_cases h2 : 13 ∣ eval
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 23 ∣ eval
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
      · by_cases h4 : 23 ∣ eval
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
        · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
          exact hclose 26 hpair (by native_decide)
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 23 ∣ eval
        · have hpair : (38:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3
          exact hclose 38 hpair (by native_decide)
        · have hpair : (38:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3
          exact hclose 38 hpair (by native_decide)
      · by_cases h4 : 23 ∣ eval
        · have hpair : (46:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h4
          exact hclose 46 hpair (by native_decide)
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 2 (by norm_num) h1 hnopowA
          have hcopg : Nat.Coprime 11362 p := by
            have hfac : (11362:ℕ).primeFactors = {2, 13, 19, 23} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (11362:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact hpne rfl
            · exact h2 hpdvd
            · exact h3 hpdvd
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 11362 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (11362 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
  · by_cases h2 : 13 ∣ eval
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 23 ∣ eval
        · have hpair : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
          exact hclose 247 hpair (by native_decide)
        · have hpair : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
          exact hclose 247 hpair (by native_decide)
      · by_cases h4 : 23 ∣ eval
        · have hpair : (299:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h4
          exact hclose 299 hpair (by native_decide)
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 13 (by norm_num) h2 hnopowB
          have hcopg : Nat.Coprime 11362 p := by
            have hfac : (11362:ℕ).primeFactors = {2, 13, 19, 23} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (11362:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact hpne rfl
            · exact h3 hpdvd
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 11362 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (11362 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
    · by_cases h3 : 19 ∣ eval
      · by_cases h4 : 23 ∣ eval
        · have hpair : (437:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4
          exact hclose 437 hpair (by native_decide)
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 19 (by norm_num) h3 hnopowC
          have hcopg : Nat.Coprime 11362 p := by
            have hfac : (11362:ℕ).primeFactors = {2, 13, 19, 23} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (11362:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact h2 hpdvd
            · exact hpne rfl
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 11362 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (11362 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
      · by_cases h4 : 23 ∣ eval
        · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 23 (by norm_num) h4 hnopowD
          have hcopg : Nat.Coprime 11362 p := by
            have hfac : (11362:ℕ).primeFactors = {2, 13, 19, 23} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (11362:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact h2 hpdvd
            · exact h3 hpdvd
            · exact hpne rfl
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 11362 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (11362 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal
        · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
          have hcopg : Nat.Coprime 11362 p := by
            have hfac : (11362:ℕ).primeFactors = {2, 13, 19, 23} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (11362:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact h1 hpdvd
            · exact h2 hpdvd
            · exact h3 hpdvd
            · exact h4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 11362 = 16 := by native_decide
          have hfinal : 28 < ArithmeticFunction.sigma 0 (11362 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal

theorem erdos647_subap_N32032 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 32032 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by
    have hsub : n - 10 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 10, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 32032 := by omega
  have hnk : n - 10 = 290 * (11639628 * q + 278347) := by
    have h1 : n - 10 = 290 * 11639628 * q + 290 * 278347 := by omega
    rw [h1]; ring
  set eval := 11639628 * q + 278347 with heval_def
  have heval_ge : 278347 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 10 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 10) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 10) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 10).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 12 < ArithmeticFunction.sigma 0 (290 * D) → False := by
    intro D hDdvd hsig
    have hDm : 290 * D ∣ (n - 10) := by rw [hnk]; exact Nat.mul_dvd_mul_left 290 hDdvd
    have := hmono (290 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 2 ^ s := by
    intro s hs
    have heq2 : n - 10 = 2 ^ (s + 1) * 145 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (2 ^ (s + 1)) 145 := by
      have hbase : Nat.Coprime 2 145 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 145 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 2)]
    have hsigX : ArithmeticFunction.sigma 0 145 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 10 = 5 ^ (s + 1) * 58 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 58 := by
      have hbase : Nat.Coprime 5 58 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 58 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigX : ArithmeticFunction.sigma 0 58 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowC : ∀ s : ℕ, eval ≠ 29 ^ s := by
    intro s hs
    have heq2 : n - 10 = 29 ^ (s + 1) * 10 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (29 ^ (s + 1)) 10 := by
      have hbase : Nat.Coprime 29 10 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 10 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 29)]
    have hsigX : ArithmeticFunction.sigma 0 10 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h1 : 2 ∣ eval
  · by_cases h2 : 5 ∣ eval
    · have hp12 : (10:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
      exact hclose 10 hp12 (by native_decide)
    · by_cases h3 : 29 ∣ eval
      · have hp13 : (58:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3
        exact hclose 58 hp13 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 2 (by norm_num) h1 hnopowA
        have hcopg : Nat.Coprime 290 p := by
          have hfac : (290:ℕ).primeFactors = {2, 5, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (290:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h2 hpdvd
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 290 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (290 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
  · by_cases h2 : 5 ∣ eval
    · by_cases h3 : 29 ∣ eval
      · have hp23 : (145:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
        exact hclose 145 hp23 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) h2 hnopowB
        have hcopg : Nat.Coprime 290 p := by
          have hfac : (290:ℕ).primeFactors = {2, 5, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (290:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact hpne rfl
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 290 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (290 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
    · by_cases h3 : 29 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 29 (by norm_num) h3 hnopowC
        have hcopg : Nat.Coprime 290 p := by
          have hfac : (290:ℕ).primeFactors = {2, 5, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (290:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact h2 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 290 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (290 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 290 p := by
          have hfac : (290:ℕ).primeFactors = {2, 5, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (290:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact h2 hpdvd
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 290 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (290 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N24310 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 24310 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by
    have hsub : n - 10 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 10, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 24310 := by omega
  have hnk : n - 10 = 230 * (11639628 * q + 266353) := by
    have h1 : n - 10 = 230 * 11639628 * q + 230 * 266353 := by omega
    rw [h1]; ring
  set eval := 11639628 * q + 266353 with heval_def
  have heval_ge : 266353 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 10 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 10) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 10) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 10).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 12 < ArithmeticFunction.sigma 0 (230 * D) → False := by
    intro D hDdvd hsig
    have hDm : 230 * D ∣ (n - 10) := by rw [hnk]; exact Nat.mul_dvd_mul_left 230 hDdvd
    have := hmono (230 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 2 ^ s := by
    intro s hs
    have heq2 : n - 10 = 2 ^ (s + 1) * 115 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (2 ^ (s + 1)) 115 := by
      have hbase : Nat.Coprime 2 115 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 115 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 2)]
    have hsigX : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 10 = 5 ^ (s + 1) * 46 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 46 := by
      have hbase : Nat.Coprime 5 46 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 46 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigX : ArithmeticFunction.sigma 0 46 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowC : ∀ s : ℕ, eval ≠ 23 ^ s := by
    intro s hs
    have heq2 : n - 10 = 23 ^ (s + 1) * 10 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (23 ^ (s + 1)) 10 := by
      have hbase : Nat.Coprime 23 10 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 10 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 23)]
    have hsigX : ArithmeticFunction.sigma 0 10 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h1 : 2 ∣ eval
  · by_cases h2 : 5 ∣ eval
    · have hp12 : (10:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
      exact hclose 10 hp12 (by native_decide)
    · by_cases h3 : 23 ∣ eval
      · have hp13 : (46:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3
        exact hclose 46 hp13 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 2 (by norm_num) h1 hnopowA
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h2 hpdvd
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
  · by_cases h2 : 5 ∣ eval
    · by_cases h3 : 23 ∣ eval
      · have hp23 : (115:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
        exact hclose 115 hp23 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) h2 hnopowB
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact hpne rfl
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
    · by_cases h3 : 23 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 23 (by norm_num) h3 hnopowC
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact h2 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact h2 hpdvd
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N18733_mod1062347 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 18733 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 18733 := by omega
  have hnk : n - 5 = 115 * (23279256 * q + 410497) := by
    have h1 : n - 5 = 115 * 23279256 * q + 115 * 410497 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 410497 with heval_def
  have heval_ge : 410497 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (115 * D) → False := by
    intro D hDdvd hsig
    have hDm : 115 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 115 hDdvd
    have := hmono (115 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 23 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 23 := by
      have hbase : Nat.Coprime 5 23 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 23 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 23 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 23 ^ s := by
    intro s hs
    have heq2 : n - 5 = 23 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (23 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 23 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 23)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 23 ∣ eval
    · have hboth : (115:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 115 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 115 p := by
        have hfac : (115:ℕ).primeFactors = {5, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (115:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (115 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 23 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 23 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 115 p := by
        have hfac : (115:ℕ).primeFactors = {5, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (115:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (115 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 115 p := by
        have hfac : (115:ℕ).primeFactors = {5, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (115:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (115 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N17160 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1708993 = 17160 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1708993 with hq_def
  have hNeq : N = 1708993 * q + 17160 := by omega
  have hnk : n - 5 = 185 * (23279256 * q + 233747) := by
    have h1 : n - 5 = 185 * 23279256 * q + 185 * 233747 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 233747 with heval_def
  have heval_ge : 233747 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (185 * D) → False := by
    intro D hDdvd hsig
    have hDm : 185 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 185 hDdvd
    have := hmono (185 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 37 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 37 := by
      have hbase : Nat.Coprime 5 37 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 37 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 37 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 37 ^ s := by
    intro s hs
    have heq2 : n - 5 = 37 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (37 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 37 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 37)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 37 ∣ eval
    · have hboth : (185:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 185 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 185 p := by
        have hfac : (185:ℕ).primeFactors = {5, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (185:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 185 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (185 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 37 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 37 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 185 p := by
        have hfac : (185:ℕ).primeFactors = {5, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (185:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 185 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (185 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 185 p := by
        have hfac : (185:ℕ).primeFactors = {5, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (185:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 185 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (185 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N12155_mod1062347 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 12155 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 12155 := by omega
  have hnk : n - 5 = 115 * (23279256 * q + 266353) := by
    have h1 : n - 5 = 115 * 23279256 * q + 115 * 266353 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 266353 with heval_def
  have heval_ge : 266353 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (115 * D) → False := by
    intro D hDdvd hsig
    have hDm : 115 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 115 hDdvd
    have := hmono (115 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 23 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 23 := by
      have hbase : Nat.Coprime 5 23 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 23 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 23 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 23 ^ s := by
    intro s hs
    have heq2 : n - 5 = 23 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (23 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 23 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 23)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 23 ∣ eval
    · have hboth : (115:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 115 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 115 p := by
        have hfac : (115:ℕ).primeFactors = {5, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (115:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (115 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 23 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 23 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 115 p := by
        have hfac : (115:ℕ).primeFactors = {5, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (115:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (115 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 115 p := by
        have hfac : (115:ℕ).primeFactors = {5, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (115:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (115 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N4862_mod1893749 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1893749 = 4862 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1893749 with hq_def
  have hNeq : N = 1893749 * q + 4862 := by omega
  have hnk : n - 5 = 205 * (23279256 * q + 59767) := by
    have h1 : n - 5 = 205 * 23279256 * q + 205 * 59767 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 59767 with heval_def
  have heval_ge : 59767 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (205 * D) → False := by
    intro D hDdvd hsig
    have hDm : 205 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 205 hDdvd
    have := hmono (205 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 41 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 41 := by
      have hbase : Nat.Coprime 5 41 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 41 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 41 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 41 ^ s := by
    intro s hs
    have heq2 : n - 5 = 41 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (41 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 41 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 41)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 41 ∣ eval
    · have hboth : (205:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 205 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 205 p := by
        have hfac : (205:ℕ).primeFactors = {5, 41} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (205:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 205 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (205 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 41 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 41 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 205 p := by
        have hfac : (205:ℕ).primeFactors = {5, 41} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (205:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 205 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (205 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 205 p := by
        have hfac : (205:ℕ).primeFactors = {5, 41} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (205:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 205 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (205 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N1287 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1708993 = 1287 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1708993 with hq_def
  have hNeq : N = 1708993 * q + 1287 := by omega
  have hnk : n - 5 = 185 * (23279256 * q + 17531) := by
    have h1 : n - 5 = 185 * 23279256 * q + 185 * 17531 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 17531 with heval_def
  have heval_ge : 17531 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (185 * D) → False := by
    intro D hDdvd hsig
    have hDm : 185 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 185 hDdvd
    have := hmono (185 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow5 : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 37 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 37 := by
      have h5_37 : Nat.Coprime 5 37 := by norm_num
      exact h5_37.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 37 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsig37 : ArithmeticFunction.sigma 0 37 = 2 := by native_decide
    rw [hsig37] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow37 : ∀ s : ℕ, eval ≠ 37 ^ s := by
    intro s hs
    have heq2 : n - 5 = 37 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (37 ^ (s + 1)) 5 := by
      have h37_5 : Nat.Coprime 37 5 := by norm_num
      exact h37_5.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 37)]
    have hsig5 : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsig5] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 37 ∣ eval
    · have hboth : (185:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 185 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopow5
      have hcopg : Nat.Coprime 185 p := by
        have hfac : (185:ℕ).primeFactors = {5, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (185:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 185 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (185 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 37 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 37 (by norm_num) hq2 hnopow37
      have hcopg : Nat.Coprime 185 p := by
        have hfac : (185:ℕ).primeFactors = {5, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (185:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 185 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (185 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 185 p := by
        have hfac : (185:ℕ).primeFactors = {5, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (185:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 185 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (185 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N17017 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 17017 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 30) ≤ 32 := by
    have hsub : n - 30 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 30, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 17017 := by omega
  have hnk : n - 30 = 13110 * (204204 * q + 3271) := by
    have h1 : n - 30 = 13110 * 204204 * q + 13110 * 3271 := by omega
    rw [h1]; ring
  set eval := 204204 * q + 3271 with heval_def
  have heval_ge : 3271 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 30 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 30) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 30) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 30).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 32 < ArithmeticFunction.sigma 0 (13110 * D) → False := by
    intro D hDdvd hsig
    have hDm : 13110 * D ∣ (n - 30) := by rw [hnk]; exact Nat.mul_dvd_mul_left 13110 hDdvd
    have := hmono (13110 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 5 ∣ eval
      · exact hclose 5 hq3 (by native_decide)
      · by_cases hq4 : 19 ∣ eval
        · exact hclose 19 hq4 (by native_decide)
        · by_cases hq5 : 23 ∣ eval
          · exact hclose 23 hq5 (by native_decide)
          · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
            have hcopg : Nat.Coprime 13110 p := by
              have hfac : (13110:ℕ).primeFactors = {2, 3, 5, 19, 23} := by native_decide
              refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
              intro hpdvdg
              have hpmem : p ∈ (13110:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
              rw [hfac] at hpmem
              simp at hpmem
              rcases hpmem with rfl | rfl | rfl | rfl | rfl
              · exact hq1 hpdvd
              · exact hq2 hpdvd
              · exact hq3 hpdvd
              · exact hq4 hpdvd
              · exact hq5 hpdvd
            have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
              rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
            have hsg : ArithmeticFunction.sigma 0 13110 = 32 := by native_decide
            have hfinal : 32 < ArithmeticFunction.sigma 0 (13110 * p) := by
              rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
              norm_num
            exact hclose p hpdvd hfinal

theorem erdos647_subap_N9009_mod1339481 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 9009 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 30) ≤ 32 := by
    have hsub : n - 30 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 30, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 9009 := by omega
  have hnk : n - 30 = 14790 * (228228 * q + 1535) := by
    have h1 : n - 30 = 14790 * 228228 * q + 14790 * 1535 := by omega
    rw [h1]; ring
  set eval := 228228 * q + 1535 with heval_def
  have heval_ge : 1535 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 30 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 30) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 30) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 30).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 32 < ArithmeticFunction.sigma 0 (14790 * D) → False := by
    intro D hDdvd hsig
    have hDm : 14790 * D ∣ (n - 30) := by rw [hnk]; exact Nat.mul_dvd_mul_left 14790 hDdvd
    have := hmono (14790 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 5 ∣ eval
      · exact hclose 5 hq3 (by native_decide)
      · by_cases hq4 : 17 ∣ eval
        · exact hclose 17 hq4 (by native_decide)
        · by_cases hq5 : 29 ∣ eval
          · exact hclose 29 hq5 (by native_decide)
          · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
            have hcopg : Nat.Coprime 14790 p := by
              have hfac : (14790:ℕ).primeFactors = {2, 3, 5, 17, 29} := by native_decide
              refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
              intro hpdvdg
              have hpmem : p ∈ (14790:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
              rw [hfac] at hpmem
              simp at hpmem
              rcases hpmem with rfl | rfl | rfl | rfl | rfl
              · exact hq1 hpdvd
              · exact hq2 hpdvd
              · exact hq3 hpdvd
              · exact hq4 hpdvd
              · exact hq5 hpdvd
            have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
              rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
            have hsg : ArithmeticFunction.sigma 0 14790 = 32 := by native_decide
            have hfinal : 32 < ArithmeticFunction.sigma 0 (14790 * p) := by
              rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
              norm_num
            exact hclose p hpdvd hfinal

theorem erdos647_subap_N13013 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1986127 = 13013 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 14) ≤ 16 := by
    have hsub : n - 14 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 14, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1986127 with hq_def
  have hNeq : N = 1986127 * q + 13013 := by omega
  have hnk : n - 14 = 11438 * (437580 * q + 2867) := by
    have h1 : n - 14 = 11438 * 437580 * q + 11438 * 2867 := by omega
    rw [h1]; ring
  set eval := 437580 * q + 2867 with heval_def
  have heval_ge : 2867 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 14 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 14) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 14) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 14).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 16 < ArithmeticFunction.sigma 0 (11438 * D) → False := by
    intro D hDdvd hsig
    have hDm : 11438 * D ∣ (n - 14) := by rw [hnk]; exact Nat.mul_dvd_mul_left 11438 hDdvd
    have := hmono (11438 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 7 ∣ eval
    · exact hclose 7 hq2 (by native_decide)
    · by_cases hq3 : 19 ∣ eval
      · exact hclose 19 hq3 (by native_decide)
      · by_cases hq4 : 43 ∣ eval
        · exact hclose 43 hq4 (by native_decide)
        · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
          have hcopg : Nat.Coprime 11438 p := by
            have hfac : (11438:ℕ).primeFactors = {2, 7, 19, 43} := by native_decide
            refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
            intro hpdvdg
            have hpmem : p ∈ (11438:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
            rw [hfac] at hpmem
            simp at hpmem
            rcases hpmem with rfl | rfl | rfl | rfl
            · exact hq1 hpdvd
            · exact hq2 hpdvd
            · exact hq3 hpdvd
            · exact hq4 hpdvd
          have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
            rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
          have hsg : ArithmeticFunction.sigma 0 11438 = 16 := by native_decide
          have hfinal : 16 < ArithmeticFunction.sigma 0 (11438 * p) := by
            rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
            norm_num
          exact hclose p hpdvd hfinal

theorem erdos647_subap_N2574 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1708993 = 2574 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by
    have hsub : n - 10 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 10, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1708993 with hq_def
  have hNeq : N = 1708993 * q + 2574 := by omega
  have hnk : n - 10 = 370 * (11639628 * q + 17531) := by
    have h1 : n - 10 = 370 * 11639628 * q + 370 * 17531 := by omega
    rw [h1]; ring
  set eval := 11639628 * q + 17531 with heval_def
  have heval_ge : 17531 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 10 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 10) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 10) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 10).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 12 < ArithmeticFunction.sigma 0 (370 * D) → False := by
    intro D hDdvd hsig
    have hDm : 370 * D ∣ (n - 10) := by rw [hnk]; exact Nat.mul_dvd_mul_left 370 hDdvd
    have := hmono (370 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 2 ^ s := by
    intro s hs
    have heq2 : n - 10 = 2 ^ (s + 1) * 185 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (2 ^ (s + 1)) 185 := by
      have hbase : Nat.Coprime 2 185 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 185 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 2)]
    have hsigX : ArithmeticFunction.sigma 0 185 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 10 = 5 ^ (s + 1) * 74 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 74 := by
      have hbase : Nat.Coprime 5 74 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 74 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigX : ArithmeticFunction.sigma 0 74 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowC : ∀ s : ℕ, eval ≠ 37 ^ s := by
    intro s hs
    have heq2 : n - 10 = 37 ^ (s + 1) * 10 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (37 ^ (s + 1)) 10 := by
      have hbase : Nat.Coprime 37 10 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 10 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 37)]
    have hsigX : ArithmeticFunction.sigma 0 10 = 4 := by native_decide
    rw [hsigX] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h1 : 2 ∣ eval
  · by_cases h2 : 5 ∣ eval
    · have hp12 : (10:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
      exact hclose 10 hp12 (by native_decide)
    · by_cases h3 : 37 ∣ eval
      · have hp13 : (74:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3
        exact hclose 74 hp13 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 2 (by norm_num) h1 hnopowA
        have hcopg : Nat.Coprime 370 p := by
          have hfac : (370:ℕ).primeFactors = {2, 5, 37} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (370:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h2 hpdvd
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 370 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (370 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
  · by_cases h2 : 5 ∣ eval
    · by_cases h3 : 37 ∣ eval
      · have hp23 : (185:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
        exact hclose 185 hp23 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) h2 hnopowB
        have hcopg : Nat.Coprime 370 p := by
          have hfac : (370:ℕ).primeFactors = {2, 5, 37} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (370:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact hpne rfl
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 370 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (370 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
    · by_cases h3 : 37 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 37 (by norm_num) h3 hnopowC
        have hcopg : Nat.Coprime 370 p := by
          have hfac : (370:ℕ).primeFactors = {2, 5, 37} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (370:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact h2 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 370 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (370 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 370 p := by
          have hfac : (370:ℕ).primeFactors = {2, 5, 37} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (370:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h1 hpdvd
          · exact h2 hpdvd
          · exact h3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 370 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (370 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N1287_mod1062347 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 1287 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by
    have hsub : n - 10 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 10, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 1287 := by omega
  have hnk : n - 10 = 230 * (11639628 * q + 14101) := by
    have h1 : n - 10 = 230 * 11639628 * q + 230 * 14101 := by omega
    rw [h1]; ring
  set eval := 11639628 * q + 14101 with heval_def
  have heval_ge : 14101 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 10 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 10) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 10) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 10).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 12 < ArithmeticFunction.sigma 0 (230 * D) → False := by
    intro D hDdvd hsig
    have hDm : 230 * D ∣ (n - 10) := by rw [hnk]; exact Nat.mul_dvd_mul_left 230 hDdvd
    have := hmono (230 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopow2 : ∀ s : ℕ, eval ≠ 2 ^ s := by
    intro s hs
    have heq2 : n - 10 = 2 ^ (s + 1) * 115 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (2 ^ (s + 1)) 115 := by
      have hbase : Nat.Coprime 2 115 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 115 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 2)]
    have hsig115 : ArithmeticFunction.sigma 0 115 = 4 := by native_decide
    rw [hsig115] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow5 : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 10 = 5 ^ (s + 1) * 46 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 46 := by
      have hbase : Nat.Coprime 5 46 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 46 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsig46 : ArithmeticFunction.sigma 0 46 = 4 := by native_decide
    rw [hsig46] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopow23 : ∀ s : ℕ, eval ≠ 23 ^ s := by
    intro s hs
    have heq2 : n - 10 = 23 ^ (s + 1) * 10 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (23 ^ (s + 1)) 10 := by
      have hbase : Nat.Coprime 23 10 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 10) = (s + 2) * ArithmeticFunction.sigma 0 10 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 23)]
    have hsig10 : ArithmeticFunction.sigma 0 10 = 4 := by native_decide
    rw [hsig10] at hsigeq
    have hsle : (s + 2) * 4 ≤ 12 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases h2 : 2 ∣ eval
  · by_cases h5 : 5 ∣ eval
    · have hp12 : (10:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h5
      exact hclose 10 hp12 (by native_decide)
    · by_cases h23 : 23 ∣ eval
      · have hp13 : (46:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h23
        exact hclose 46 hp13 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 2 (by norm_num) h2 hnopow2
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hpne rfl
          · exact h5 hpdvd
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
  · by_cases h5 : 5 ∣ eval
    · by_cases h23 : 23 ∣ eval
      · have hp23 : (115:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h23
        exact hclose 115 hp23 (by native_decide)
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) h5 hnopow5
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h2 hpdvd
          · exact hpne rfl
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
    · by_cases h23 : 23 ∣ eval
      · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 23 (by norm_num) h23 hnopow23
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h2 hpdvd
          · exact h5 hpdvd
          · exact hpne rfl
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 230 p := by
          have hfac : (230:ℕ).primeFactors = {2, 5, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (230:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact h2 hpdvd
          · exact h5 hpdvd
          · exact h23 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 230 = 8 := by native_decide
        have hfinal : 12 < ArithmeticFunction.sigma 0 (230 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N32461 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 32461 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 32461 := by omega
  have hnk : n - 5 = 155 * (23279256 * q + 527753) := by
    have h1 : n - 5 = 155 * 23279256 * q + 155 * 527753 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 527753 with heval_def
  have heval_ge : 527753 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (155 * D) → False := by
    intro D hDdvd hsig
    have hDm : 155 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 155 hDdvd
    have := hmono (155 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 31 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 31 := by
      have hbase : Nat.Coprime 5 31 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 31 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 31 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 31 ^ s := by
    intro s hs
    have heq2 : n - 5 = 31 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (31 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 31 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 31)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 31 ∣ eval
    · have hboth : (155:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 155 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 155 p := by
        have hfac : (155:ℕ).primeFactors = {5, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (155:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 155 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (155 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 31 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 31 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 155 p := by
        have hfac : (155:ℕ).primeFactors = {5, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (155:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 155 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (155 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 155 p := by
        have hfac : (155:ℕ).primeFactors = {5, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (155:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 155 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (155 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N28457 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 28457 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 28457 := by omega
  have hnk : n - 5 = 145 * (23279256 * q + 494563) := by
    have h1 : n - 5 = 145 * 23279256 * q + 145 * 494563 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 494563 with heval_def
  have heval_ge : 494563 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (145 * D) → False := by
    intro D hDdvd hsig
    have hDm : 145 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 145 hDdvd
    have := hmono (145 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 29 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 29 := by
      have hbase : Nat.Coprime 5 29 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 29 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 29 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 29 ^ s := by
    intro s hs
    have heq2 : n - 5 = 29 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (29 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 29 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 29)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 29 ∣ eval
    · have hboth : (145:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 145 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 145 p := by
        have hfac : (145:ℕ).primeFactors = {5, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (145:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 145 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (145 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 29 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 29 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 145 p := by
        have hfac : (145:ℕ).primeFactors = {5, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (145:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 145 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (145 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 145 p := by
        have hfac : (145:ℕ).primeFactors = {5, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (145:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 145 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (145 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N28028 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 28028 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 28028 := by omega
  have hnk : n - 5 = 155 * (23279256 * q + 455681) := by
    have h1 : n - 5 = 155 * 23279256 * q + 155 * 455681 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 455681 with heval_def
  have heval_ge : 455681 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (155 * D) → False := by
    intro D hDdvd hsig
    have hDm : 155 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 155 hDdvd
    have := hmono (155 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 31 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 31 := by
      have hbase : Nat.Coprime 5 31 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 31 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 31 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 31 ^ s := by
    intro s hs
    have heq2 : n - 5 = 31 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (31 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 31 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 31)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 31 ∣ eval
    · have hboth : (155:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 155 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 155 p := by
        have hfac : (155:ℕ).primeFactors = {5, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (155:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 155 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (155 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 31 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 31 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 155 p := by
        have hfac : (155:ℕ).primeFactors = {5, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (155:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 155 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (155 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 155 p := by
        have hfac : (155:ℕ).primeFactors = {5, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (155:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 155 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (155 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N24310_mod1339481 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 24310 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 5) ≤ 7 := by
    have hsub : n - 5 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 5, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 24310 := by omega
  have hnk : n - 5 = 145 * (23279256 * q + 422491) := by
    have h1 : n - 5 = 145 * 23279256 * q + 145 * 422491 := by omega
    rw [h1]; ring
  set eval := 23279256 * q + 422491 with heval_def
  have heval_ge : 422491 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 5 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 5) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 5) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 5).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 7 < ArithmeticFunction.sigma 0 (145 * D) → False := by
    intro D hDdvd hsig
    have hDm : 145 * D ∣ (n - 5) := by rw [hnk]; exact Nat.mul_dvd_mul_left 145 hDdvd
    have := hmono (145 * D) hDm
    omega
  have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) →
      ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by
    intro p hp hpdvd hnotpow
    by_contra hnone
    push_neg at hnone
    have heval0 : eval ≠ 0 := by omega
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd)
    exact hnotpow _ hpow
  have hnopowA : ∀ s : ℕ, eval ≠ 5 ^ s := by
    intro s hs
    have heq2 : n - 5 = 5 ^ (s + 1) * 29 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (5 ^ (s + 1)) 29 := by
      have hbase : Nat.Coprime 5 29 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 29 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)]
    have hsigB : ArithmeticFunction.sigma 0 29 = 2 := by native_decide
    rw [hsigB] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  have hnopowB : ∀ s : ℕ, eval ≠ 29 ^ s := by
    intro s hs
    have heq2 : n - 5 = 29 ^ (s + 1) * 5 := by rw [hnk, hs]; ring
    have hcop : Nat.Coprime (29 ^ (s + 1)) 5 := by
      have hbase : Nat.Coprime 29 5 := by norm_num
      exact hbase.pow_left (s + 1)
    have hsigeq : ArithmeticFunction.sigma 0 (n - 5) = (s + 2) * ArithmeticFunction.sigma 0 5 := by
      rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 29)]
    have hsigA : ArithmeticFunction.sigma 0 5 = 2 := by native_decide
    rw [hsigA] at hsigeq
    have hsle : (s + 2) * 2 ≤ 7 := by rw [← hsigeq]; exact shift
    have hsbound : s ≤ 1 := by omega
    interval_cases s
    · norm_num at hs; omega
    · norm_num at hs; omega
  by_cases hq1 : 5 ∣ eval
  · by_cases hq2 : 29 ∣ eval
    · have hboth : (145:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hq1 hq2
      exact hclose 145 hboth (by native_decide)
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 5 (by norm_num) hq1 hnopowA
      have hcopg : Nat.Coprime 145 p := by
        have hfac : (145:ℕ).primeFactors = {5, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (145:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hpne rfl
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 145 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (145 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
  · by_cases hq2 : 29 ∣ eval
    · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 29 (by norm_num) hq2 hnopowB
      have hcopg : Nat.Coprime 145 p := by
        have hfac : (145:ℕ).primeFactors = {5, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (145:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hpne rfl
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 145 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (145 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 145 p := by
        have hfac : (145:ℕ).primeFactors = {5, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (145:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 145 = 4 := by native_decide
      have hfinal : 7 < ArithmeticFunction.sigma 0 (145 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N44187 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 44187 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 44187 := by omega
  have hnk : n - 6 = 138 * (19399380 * q + 806893) := by
    have h1 : n - 6 = 138 * 19399380 * q + 138 * 806893 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 806893 with heval_def
  have heval_ge : 806893 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (138 * D) → False := by
    intro D hDdvd hsig
    have hDm : 138 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 138 hDdvd
    have := hmono (138 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 23 ∣ eval
      · exact hclose 23 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 138 p := by
          have hfac : (138:ℕ).primeFactors = {2, 3, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (138:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 138 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (138 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N24453_mod1062347 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 24453 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 24453 := by omega
  have hnk : n - 6 = 138 * (19399380 * q + 446533) := by
    have h1 : n - 6 = 138 * 19399380 * q + 138 * 446533 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 446533 with heval_def
  have heval_ge : 446533 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (138 * D) → False := by
    intro D hDdvd hsig
    have hDm : 138 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 138 hDdvd
    have := hmono (138 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 23 ∣ eval
      · exact hclose 23 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 138 p := by
          have hfac : (138:ℕ).primeFactors = {2, 3, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (138:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 138 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (138 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N21164 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 21164 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 21164 := by omega
  have hnk : n - 6 = 138 * (19399380 * q + 386473) := by
    have h1 : n - 6 = 138 * 19399380 * q + 138 * 386473 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 386473 with heval_def
  have heval_ge : 386473 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (138 * D) → False := by
    intro D hDdvd hsig
    have hDm : 138 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 138 hDdvd
    have := hmono (138 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 23 ∣ eval
      · exact hclose 23 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 138 p := by
          have hfac : (138:ℕ).primeFactors = {2, 3, 23} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (138:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 138 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (138 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N18733_mod1893749 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1893749 = 18733 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1893749 with hq_def
  have hNeq : N = 1893749 * q + 18733 := by omega
  have hnk : n - 6 = 246 * (19399380 * q + 191899) := by
    have h1 : n - 6 = 246 * 19399380 * q + 246 * 191899 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 191899 with heval_def
  have heval_ge : 191899 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (246 * D) → False := by
    intro D hDdvd hsig
    have hDm : 246 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 246 hDdvd
    have := hmono (246 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 41 ∣ eval
      · exact hclose 41 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 246 p := by
          have hfac : (246:ℕ).primeFactors = {2, 3, 41} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (246:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 246 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (246 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N12584 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 12584 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 12584 := by omega
  have hnk : n - 6 = 174 * (19399380 * q + 182251) := by
    have h1 : n - 6 = 174 * 19399380 * q + 174 * 182251 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 182251 with heval_def
  have heval_ge : 182251 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (174 * D) → False := by
    intro D hDdvd hsig
    have hDm : 174 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 174 hDdvd
    have := hmono (174 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 29 ∣ eval
      · exact hclose 29 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 174 p := by
          have hfac : (174:ℕ).primeFactors = {2, 3, 29} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (174:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 174 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (174 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N10582_mod1431859 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 10582 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 10582 := by omega
  have hnk : n - 6 = 186 * (19399380 * q + 143369) := by
    have h1 : n - 6 = 186 * 19399380 * q + 186 * 143369 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 143369 with heval_def
  have heval_ge : 143369 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (186 * D) → False := by
    intro D hDdvd hsig
    have hDm : 186 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 186 hDdvd
    have := hmono (186 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 31 ∣ eval
      · exact hclose 31 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 186 p := by
          have hfac : (186:ℕ).primeFactors = {2, 3, 31} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (186:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 186 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (186 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N6149 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 6149 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 6149 := by omega
  have hnk : n - 6 = 186 * (19399380 * q + 83309) := by
    have h1 : n - 6 = 186 * 19399380 * q + 186 * 83309 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 83309 with heval_def
  have heval_ge : 83309 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (186 * D) → False := by
    intro D hDdvd hsig
    have hDm : 186 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 186 hDdvd
    have := hmono (186 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 31 ∣ eval
      · exact hclose 31 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 186 p := by
          have hfac : (186:ℕ).primeFactors = {2, 3, 31} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (186:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 186 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (186 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N1716 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 1716 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 6) ≤ 8 := by
    have hsub : n - 6 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 6, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 1716 := by omega
  have hnk : n - 6 = 186 * (19399380 * q + 23249) := by
    have h1 : n - 6 = 186 * 19399380 * q + 186 * 23249 := by omega
    rw [h1]; ring
  set eval := 19399380 * q + 23249 with heval_def
  have heval_ge : 23249 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 6 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 6) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 6) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 6).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 8 < ArithmeticFunction.sigma 0 (186 * D) → False := by
    intro D hDdvd hsig
    have hDm : 186 * D ∣ (n - 6) := by rw [hnk]; exact Nat.mul_dvd_mul_left 186 hDdvd
    have := hmono (186 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 3 ∣ eval
    · exact hclose 3 hq2 (by native_decide)
    · by_cases hq3 : 31 ∣ eval
      · exact hclose 31 hq3 (by native_decide)
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
        have hcopg : Nat.Coprime 186 p := by
          have hfac : (186:ℕ).primeFactors = {2, 3, 31} := by native_decide
          refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
          intro hpdvdg
          have hpmem : p ∈ (186:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
          rw [hfac] at hpmem
          simp at hpmem
          rcases hpmem with rfl | rfl | rfl
          · exact hq1 hpdvd
          · exact hq2 hpdvd
          · exact hq3 hpdvd
        have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
          rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
        have hsg : ArithmeticFunction.sigma 0 186 = 8 := by native_decide
        have hfinal : 8 < ArithmeticFunction.sigma 0 (186 * p) := by
          rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
          norm_num
        exact hclose p hpdvd hfinal

theorem erdos647_subap_N36608_mod1986127 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1986127 = 36608 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1986127 with hq_def
  have hNeq : N = 1986127 * q + 36608 := by omega
  have hnk : n - 3 = 129 * (38798760 * q + 715133) := by
    have h1 : n - 3 = 129 * 38798760 * q + 129 * 715133 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 715133 with heval_def
  have heval_ge : 715133 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (129 * D) → False := by
    intro D hDdvd hsig
    have hDm : 129 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 129 hDdvd
    have := hmono (129 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 43 ∣ eval
    · exact hclose 43 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 129 p := by
        have hfac : (129:ℕ).primeFactors = {3, 43} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (129:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 129 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (129 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N24310_mod1986127 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1986127 = 24310 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1986127 with hq_def
  have hNeq : N = 1986127 * q + 24310 := by omega
  have hnk : n - 3 = 129 * (38798760 * q + 474893) := by
    have h1 : n - 3 = 129 * 38798760 * q + 129 * 474893 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 474893 with heval_def
  have heval_ge : 474893 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (129 * D) → False := by
    intro D hDdvd hsig
    have hDm : 129 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 129 hDdvd
    have := hmono (129 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 43 ∣ eval
    · exact hclose 43 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 129 p := by
        have hfac : (129:ℕ).primeFactors = {3, 43} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (129:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 129 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (129 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N18733_mod1339481 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1339481 = 18733 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1339481 with hq_def
  have hNeq : N = 1339481 * q + 18733 := by omega
  have hnk : n - 3 = 87 * (38798760 * q + 542611) := by
    have h1 : n - 3 = 87 * 38798760 * q + 87 * 542611 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 542611 with heval_def
  have heval_ge : 542611 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (87 * D) → False := by
    intro D hDdvd hsig
    have hDm : 87 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 87 hDdvd
    have := hmono (87 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 29 ∣ eval
    · exact hclose 29 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 87 p := by
        have hfac : (87:ℕ).primeFactors = {3, 29} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (87:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 87 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (87 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N17160_mod1062347 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 17160 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 17160 := by omega
  have hnk : n - 3 = 69 * (38798760 * q + 626713) := by
    have h1 : n - 3 = 69 * 38798760 * q + 69 * 626713 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 626713 with heval_def
  have heval_ge : 626713 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (69 * D) → False := by
    intro D hDdvd hsig
    have hDm : 69 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 69 hDdvd
    have := hmono (69 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 23 ∣ eval
    · exact hclose 23 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 69 p := by
        have hfac : (69:ℕ).primeFactors = {3, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (69:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 69 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (69 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N5291_mod1431859 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 5291 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 3) ≤ 5 := by
    have hsub : n - 3 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 3, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 5291 := by omega
  have hnk : n - 3 = 93 * (38798760 * q + 143369) := by
    have h1 : n - 3 = 93 * 38798760 * q + 93 * 143369 := by omega
    rw [h1]; ring
  set eval := 38798760 * q + 143369 with heval_def
  have heval_ge : 143369 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 3 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 3) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 3) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 3).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 5 < ArithmeticFunction.sigma 0 (93 * D) → False := by
    intro D hDdvd hsig
    have hDm : 93 * D ∣ (n - 3) := by rw [hnk]; exact Nat.mul_dvd_mul_left 93 hDdvd
    have := hmono (93 * D) hDm
    omega
  by_cases hq1 : 3 ∣ eval
  · exact hclose 3 hq1 (by native_decide)
  · by_cases hq2 : 31 ∣ eval
    · exact hclose 31 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 93 p := by
        have hfac : (93:ℕ).primeFactors = {3, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (93:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 93 = 4 := by native_decide
      have hfinal : 5 < ArithmeticFunction.sigma 0 (93 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N37752 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 37752 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 37752 := by omega
  have hnk : n - 2 = 46 * (58198140 * q + 2068153) := by
    have h1 : n - 2 = 46 * 58198140 * q + 46 * 2068153 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 2068153 with heval_def
  have heval_ge : 2068153 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (46 * D) → False := by
    intro D hDdvd hsig
    have hDm : 46 * D ∣ (n - 2) := by rw [hnk]; exact Nat.mul_dvd_mul_left 46 hDdvd
    have := hmono (46 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 23 ∣ eval
    · exact hclose 23 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 46 p := by
        have hfac : (46:ℕ).primeFactors = {2, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (46:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 46 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (46 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N31603 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 31603 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1431859 with hq_def
  have hNeq : N = 1431859 * q + 31603 := by omega
  have hnk : n - 2 = 62 * (58198140 * q + 1284509) := by
    have h1 : n - 2 = 62 * 58198140 * q + 62 * 1284509 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 1284509 with heval_def
  have heval_ge : 1284509 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (62 * D) → False := by
    intro D hDdvd hsig
    have hDm : 62 * D ∣ (n - 2) := by rw [hnk]; exact Nat.mul_dvd_mul_left 62 hDdvd
    have := hmono (62 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 31 ∣ eval
    · exact hclose 31 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 62 p := by
        have hfac : (62:ℕ).primeFactors = {2, 31} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (62:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 62 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (62 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N28028_mod1708993 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1708993 = 28028 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1708993 with hq_def
  have hNeq : N = 1708993 * q + 28028 := by omega
  have hnk : n - 2 = 74 * (58198140 * q + 954467) := by
    have h1 : n - 2 = 74 * 58198140 * q + 74 * 954467 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 954467 with heval_def
  have heval_ge : 954467 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (74 * D) → False := by
    intro D hDdvd hsig
    have hDm : 74 * D ∣ (n - 2) := by rw [hnk]; exact Nat.mul_dvd_mul_left 74 hDdvd
    have := hmono (74 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 37 ∣ eval
    · exact hclose 37 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 74 p := by
        have hfac : (74:ℕ).primeFactors = {2, 37} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (74:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 74 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (74 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N20306 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1986127 = 20306 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1986127 with hq_def
  have hNeq : N = 1986127 * q + 20306 := by omega
  have hnk : n - 2 = 86 * (58198140 * q + 595013) := by
    have h1 : n - 2 = 86 * 58198140 * q + 86 * 595013 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 595013 with heval_def
  have heval_ge : 595013 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (86 * D) → False := by
    intro D hDdvd hsig
    have hDm : 86 * D ∣ (n - 2) := by rw [hnk]; exact Nat.mul_dvd_mul_left 86 hDdvd
    have := hmono (86 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 43 ∣ eval
    · exact hclose 43 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 86 p := by
        have hfac : (86:ℕ).primeFactors = {2, 43} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (86:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 86 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (86 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal

theorem erdos647_subap_N8151 :
    ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1062347 = 8151 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 2) ≤ 4 := by
    have hsub : n - 2 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 2, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 1062347 with hq_def
  have hNeq : N = 1062347 * q + 8151 := by omega
  have hnk : n - 2 = 46 * (58198140 * q + 446533) := by
    have h1 : n - 2 = 46 * 58198140 * q + 46 * 446533 := by omega
    rw [h1]; ring
  set eval := 58198140 * q + 446533 with heval_def
  have heval_ge : 446533 ≤ eval := by dsimp [eval]; omega
  have hnkne : n - 2 ≠ 0 := by omega
  have hmono : ∀ a : ℕ, a ∣ (n - 2) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 2) := by
    intro a hadvd
    have hsub2 : a.divisors ⊆ (n - 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans hadvd, hnkne⟩
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub2
  have hclose : ∀ D : ℕ, D ∣ eval → 4 < ArithmeticFunction.sigma 0 (46 * D) → False := by
    intro D hDdvd hsig
    have hDm : 46 * D ∣ (n - 2) := by rw [hnk]; exact Nat.mul_dvd_mul_left 46 hDdvd
    have := hmono (46 * D) hDm
    omega
  by_cases hq1 : 2 ∣ eval
  · exact hclose 2 hq1 (by native_decide)
  · by_cases hq2 : 23 ∣ eval
    · exact hclose 23 hq2 (by native_decide)
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega)
      have hcopg : Nat.Coprime 46 p := by
        have hfac : (46:ℕ).primeFactors = {2, 23} := by native_decide
        refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
        intro hpdvdg
        have hpmem : p ∈ (46:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩
        rw [hfac] at hpmem
        simp at hpmem
        rcases hpmem with rfl | rfl
        · exact hq1 hpdvd
        · exact hq2 hpdvd
      have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
        rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
      have hsg : ArithmeticFunction.sigma 0 46 = 4 := by native_decide
      have hfinal : 4 < ArithmeticFunction.sigma 0 (46 * p) := by
        rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp]
        norm_num
      exact hclose p hpdvd hfinal
