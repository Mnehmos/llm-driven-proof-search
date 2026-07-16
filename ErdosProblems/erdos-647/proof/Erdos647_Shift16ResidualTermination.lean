import Mathlib

/-!
# Erdős #647 — shift-16 residual termination

This snapshot closes the formerly open `M % 8 = 3` branch of the shift-16
classification. A pure power-of-two cofactor is impossible by incompatible
mod-3 and mod-5 exponent conditions. Consequently the shift budget rules out
`32 ∣ 315 * M - 1`, leaving exactly two prime-producing leaves:

* `M = 16Q + 11` and `630Q + 433` is prime;
* `M = 32R + 3` and `630R + 59` is prime.

Proof-search records (2026-07-16):

* no-high-2-adic preverification: `85156cea-bb8c-4d84-a0f7-14356f95b2f6`
* no-high-2-adic problem: `dccdc909-b5f0-469c-a08e-399bb7bd1df1`
* no-high-2-adic episode: `d1ba6805-c532-480b-9bd5-d18bb893b752`
* no-high-2-adic root hash: `cdb4a94a9bac222bb03cbbf7c85d8005df99af26f592bf5897cc4435e9df8571`
* residual-split preverification: `dee7cb16-6f84-47dd-ac83-a5e2e63c7226`
* residual-split problem: `118dfd13-405e-429a-9e7b-64594451c510`
* residual-split episode: `2fd992ae-c20a-46b1-b95e-25575963cad3`
* residual-split root hash: `dbaf4a7e6c48a150d34e0722f72b60719aef0eab5dd5f6da6c9de6e454f1a378`

Both tracked episodes ended `kernel_verified` / `root_proved`.
-/
open ArithmeticFunction

theorem erdos647_affine315_not_two_pow :
    ∀ M e : ℕ, 1 ≤ M → 315 * M - 1 ≠ 2 ^ e := by
  intro M e hM heq
  have hadd : 315 * M = 2 ^ e + 1 := by omega
  have hz3 : (2 : ZMod 3) ^ e = 2 := by
    have h := congrArg (fun x : ℕ => (x : ZMod 3)) hadd
    push_cast at h
    have h315 : (315 : ZMod 3) = 0 := by native_decide
    rw [h315, zero_mul] at h
    calc
      (2 : ZMod 3) ^ e = -1 := by linear_combination -h
      _ = 2 := by native_decide
  have hz5 : (2 : ZMod 5) ^ e = 4 := by
    have h := congrArg (fun x : ℕ => (x : ZMod 5)) hadd
    push_cast at h
    have h315 : (315 : ZMod 5) = 0 := by native_decide
    rw [h315, zero_mul] at h
    calc
      (2 : ZMod 5) ^ e = -1 := by linear_combination -h
      _ = 4 := by native_decide
  have he2 : e % 2 = 1 := by
    have hedecomp : e = 2 * (e / 2) + e % 2 := by omega
    rw [hedecomp, pow_add, pow_mul] at hz3
    have hsq : (2 : ZMod 3) ^ 2 = 1 := by native_decide
    rw [hsq, one_pow, one_mul] at hz3
    have hlt : e % 2 < 2 := Nat.mod_lt e (by norm_num)
    interval_cases h : e % 2
    · exfalso
      exact (by native_decide : (1 : ZMod 3) ≠ 2) hz3
    · rfl
  have he4 : e % 4 = 2 := by
    have hedecomp : e = 4 * (e / 4) + e % 4 := by omega
    rw [hedecomp, pow_add, pow_mul] at hz5
    have hfour : (2 : ZMod 5) ^ 4 = 1 := by native_decide
    rw [hfour, one_pow, one_mul] at hz5
    have hlt : e % 4 < 4 := Nat.mod_lt e (by norm_num)
    interval_cases h : e % 4
    · exfalso
      exact (by native_decide : (1 : ZMod 5) ≠ 4) hz5
    · exfalso
      exact (by native_decide : (2 : ZMod 5) ≠ 4) hz5
    · rfl
    · exfalso
      exact (by native_decide : (8 : ZMod 5) ≠ 4) hz5
  have h2decomp := Nat.mod_add_div e 2
  have h4decomp := Nat.mod_add_div e 4
  omega

theorem erdos647_shift16_not_thirtytwo_dvd :
    ∀ M : ℕ, 1 ≤ M →
      ArithmeticFunction.sigma 0 (16 * (315 * M - 1)) ≤ 18 →
      ¬ 32 ∣ 315 * M - 1 := by
  intro M hM hbudget h32
  set T := 315 * M - 1 with hT
  have hbudgetT : ArithmeticFunction.sigma 0 (16 * T) ≤ 18 := by
    simpa [T] using hbudget
  have hT2 : 2 ≤ T := by dsimp [T]; omega
  have hT0 : T ≠ 0 := by omega
  have hnopow : ∀ e : ℕ, T ≠ 2 ^ e := by
    intro e
    dsimp [T]
    exact erdos647_affine315_not_two_pow M e hM
  have h2T : 2 ∣ T := dvd_trans (by norm_num) h32
  have hother : ∃ p : ℕ, Nat.Prime p ∧ p ∣ T ∧ p ≠ 2 := by
    by_contra hnone
    push Not at hnone
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hT0
      (fun {p} hp hpd => hnone p hp hpd)
    exact hnopow _ hpow
  obtain ⟨p, hp, hpT, hpne⟩ := hother
  have hpnot32 : ¬ p ∣ 32 := by
    intro hp32
    have h32eq : (32 : ℕ) = 2 ^ 5 := by norm_num
    rw [h32eq] at hp32
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hp32
    exact hpne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)
  have hcop32p : Nat.Coprime 32 p :=
    ((hp.coprime_iff_not_dvd).mpr hpnot32).symm
  have h32pT : 32 * p ∣ T :=
    hcop32p.mul_dvd_of_dvd_of_dvd h32 hpT
  have h512p : 512 * p ∣ 16 * T := by
    have h := Nat.mul_dvd_mul_left 16 h32pT
    convert h using 1
    · ring
  have hcop2p : Nat.Coprime 2 p :=
    (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hpne)
  have hcop512p : Nat.Coprime (2 ^ 9) p := hcop2p.pow_left 9
  have hs512p : ArithmeticFunction.sigma 0 (512 * p) = 20 := by
    rw [show 512 * p = 2 ^ 9 * p by norm_num,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop512p,
      ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two,
      show p = p ^ 1 by simp,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    norm_num
  have hfull0 : 16 * T ≠ 0 := by omega
  have hsub : (512 * p).divisors ⊆ (16 * T).divisors := by
    intro d hd
    rw [Nat.mem_divisors] at hd ⊢
    exact ⟨hd.1.trans h512p, hfull0⟩
  have hmono : ArithmeticFunction.sigma 0 (512 * p) ≤
      ArithmeticFunction.sigma 0 (16 * T) := by
    rw [ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card hsub
  rw [hs512p] at hmono
  omega

theorem erdos647_prime_of_sigma_zero_le_two :
    ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 →
      Nat.Prime x := by
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

theorem erdos647_shift16_residual_split :
    ∀ M : ℕ, 1 ≤ M →
      ArithmeticFunction.sigma 0 (16 * (315 * M - 1)) ≤ 18 →
      M % 8 = 3 →
      (∃ Q : ℕ, M = 16 * Q + 11 ∧ Nat.Prime (630 * Q + 433)) ∨
      (∃ R : ℕ, M = 32 * R + 3 ∧ Nat.Prime (630 * R + 59)) := by
  intro M hM hbudget hM8
  have hM16lt : M % 16 < 16 := Nat.mod_lt M (by norm_num)
  have hM8decomp := Nat.mod_add_div M 8
  have hM16decomp := Nat.mod_add_div M 16
  by_cases hM16 : M % 16 = 11
  · left
    let Q := M / 16
    have hMQ : M = 16 * Q + 11 := by
      dsimp [Q]
      omega
    refine ⟨Q, hMQ, ?_⟩
    set u := 630 * Q + 433 with hu
    have hfactor : 16 * (315 * M - 1) = 2 ^ 7 * u := by
      rw [hMQ, hu]
      omega
    have hu2 : 2 ≤ u := by dsimp [u]; omega
    have huodd : Odd u := by
      refine ⟨315 * Q + 216, ?_⟩
      rw [hu]
      ring
    have hnot2u : ¬ 2 ∣ u := by
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := huodd
      omega
    have hcop2u : Nat.Coprime 2 u :=
      (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2u
    have hcop128u : Nat.Coprime (2 ^ 7) u := hcop2u.pow_left 7
    have hsigma : ArithmeticFunction.sigma 0 (16 * (315 * M - 1)) =
        8 * ArithmeticFunction.sigma 0 u := by
      rw [hfactor,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop128u,
        ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two]
    have hubudget : ArithmeticFunction.sigma 0 u ≤ 2 := by
      rw [hsigma] at hbudget
      omega
    exact erdos647_prime_of_sigma_zero_le_two u hu2 hubudget
  · have hM16eq : M % 16 = 3 := by omega
    have hM32lt : M % 32 < 32 := Nat.mod_lt M (by norm_num)
    have hM32decomp := Nat.mod_add_div M 32
    by_cases hM32 : M % 32 = 3
    · right
      let R := M / 32
      have hMR : M = 32 * R + 3 := by
        dsimp [R]
        omega
      refine ⟨R, hMR, ?_⟩
      set v := 630 * R + 59 with hv
      have hfactor : 16 * (315 * M - 1) = 2 ^ 8 * v := by
        rw [hMR, hv]
        omega
      have hv2 : 2 ≤ v := by dsimp [v]; omega
      have hvodd : Odd v := by
        refine ⟨315 * R + 29, ?_⟩
        rw [hv]
        ring
      have hnot2v : ¬ 2 ∣ v := by
        rintro ⟨a, ha⟩
        obtain ⟨b, hb⟩ := hvodd
        omega
      have hcop2v : Nat.Coprime 2 v :=
        (Nat.prime_two.coprime_iff_not_dvd).mpr hnot2v
      have hcop256v : Nat.Coprime (2 ^ 8) v := hcop2v.pow_left 8
      have hsigma : ArithmeticFunction.sigma 0 (16 * (315 * M - 1)) =
          9 * ArithmeticFunction.sigma 0 v := by
        rw [hfactor,
          ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop256v,
          ArithmeticFunction.sigma_zero_apply_prime_pow Nat.prime_two]
      have hvbudget : ArithmeticFunction.sigma 0 v ≤ 2 := by
        rw [hsigma] at hbudget
        omega
      exact erdos647_prime_of_sigma_zero_le_two v hv2 hvbudget
    · have hM32eq : M % 32 = 19 := by omega
      have h32 : 32 ∣ 315 * M - 1 := by
        refine ⟨315 * (M / 32) + 187, ?_⟩
        omega
      exact (erdos647_shift16_not_thirtytwo_dvd M hM hbudget h32).elim
