# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdős 647 shift-10 classification (near-prime, adic case-split, the "252-row family"): any candidate n > 84 with the divisor-sum bound and 2520 | n has (n-10)/10 prime, a prime square, or 5 times a prime. Proof: r = (n-10)/10 = 252q-1, always odd (252 even); write r = 5^c * s with 5 ∤ s (Nat.exists_eq_pow_mul_and_not_dvd); s is automatically odd too (divides the odd r); n-10 = 2*5^(c+1)*s, coprime factors, σ₀(n-10) = 2*(c+2)*σ₀(s) ≤ 12. c=0 → σ₀(s)≤3 → r prime or p^2; c=1 → σ₀(s)≤2 → r=5*prime; c≥2 forces (using the correct bound 2*(c+2)≥8) σ₀(s)≤1 → s=1 → r=5^c with c≤4 (from budget), and interval_cases on c∈{2,3,4} shows 252q-1=5^c has no natural solution q for any of these 3 values. Completes the near-prime classification family alongside shifts 8 and 9. Novel in Lean (dossier 83bf3744).

> This proof establishes:
>
> `∀ n : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 2520 ∣ n → Nat.Prime ((n - 10) / 10) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = 5 * p)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ n : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 2520 ∣ n → Nat.Prime ((n - 10) / 10) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = 5 * p)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `a9c7ea71-3b55-4a02-bdfa-bca0b0ba979c` | terminated (root_proved) | 1 | — | 2026-07-13T08:37:00 | 2026-07-13T08:38:15 |

## Proof tree

- ✅ **root_theorem** : `∀ n : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 2520 ∣ n → Nat.Prime ((n - 10) / 10) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = 5 * p)`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ n : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → 2520 ∣ n → Nat.Prime ((n - 10) / 10) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = p ^ 2) ∨ (∃ p : ℕ, Nat.Prime p ∧ (n - 10) / 10 = 5 * p) := by
  intro n hn H hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hq1 : 1 ≤ q := (by omega)
  have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by
    intro x hx hs
    rw [ArithmeticFunction.sigma_zero_apply] at hs
    have hx0 : x ≠ 0 := (by omega)
    have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Nat.mem_divisors]
      rcases hy with rfl | rfl
      · exact ⟨one_dvd _, hx0⟩
      · exact ⟨dvd_rfl, hx0⟩
    have hc2 : ({1, x} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro mm hmlt hmdvd
    have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h1
    · exact h1
    · omega
  have hchar : ∀ r : ℕ, 2 ≤ r → ArithmeticFunction.sigma 0 r ≤ 3 → Nat.Prime r ∨ ∃ p : ℕ, Nat.Prime p ∧ r = p ^ 2 := by
    intro r hr hcard
    rw [ArithmeticFunction.sigma_zero_apply] at hcard
    have hr0 : r ≠ 0 := (by omega)
    have hr1 : r ≠ 1 := (by omega)
    have hp : (r.minFac).Prime := Nat.minFac_prime hr1
    by_cases hpr : r.minFac = r
    · exact Or.inl (hpr ▸ hp)
    · right
      refine ⟨r.minFac, hp, ?_⟩
      have hpd : r.minFac ∣ r := Nat.minFac_dvd r
      have hp2 : 2 ≤ r.minFac := hp.two_le
      have hplt : r.minFac < r := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr
      have hsub2 : ({1, r.minFac, r} : Finset ℕ) ⊆ r.divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd r, hr0⟩
        · exact ⟨hpd, hr0⟩
        · exact ⟨dvd_rfl, hr0⟩
      have hcard3 : ({1, r.minFac, r} : Finset ℕ).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
      have heq : r.divisors = {1, r.minFac, r} :=
        (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm
      have hmul : r.minFac * (r / r.minFac) = r := Nat.mul_div_cancel' hpd
      have hqd : r / r.minFac ∣ r := ⟨r.minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩
      have hqmem : r / r.minFac ∈ r.divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩
      rw [heq] at hqmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
      rcases hqmem with h1 | h2 | h3
      · rw [h1, mul_one] at hmul
        exact absurd hmul (Nat.ne_of_lt hplt)
      · rw [h2] at hmul
        rw [pow_two]
        exact hmul.symm
      · rw [h3] at hmul
        exfalso
        nlinarith [hp2, hr, hmul]
  have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by
    have hsub : n - 10 < n := (by omega)
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
  have hval : (n - 10) / 10 = 252 * q - 1 := (by omega)
  have hn10 : n - 10 = 10 * (252 * q - 1) := (by omega)
  rw [hval]
  have hrodd : ¬ (2 ∣ 252 * q - 1) := (by omega)
  obtain ⟨c, s, hnd, hrs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show 252 * q - 1 ≠ 0 by omega) 5 (by norm_num)
  have hs0 : s ≠ 0 := (by rintro rfl; exact hnd (dvd_zero 5))
  have hsodd : ¬ (2 ∣ s) := by
    intro hcon
    apply hrodd
    rw [hrs]
    exact Dvd.dvd.mul_left hcon (5 ^ c)
  have hcop25 : Nat.Coprime (2 * 5 ^ (c + 1)) s := by
    have h2s : Nat.Coprime 2 s := (Nat.prime_two.coprime_iff_not_dvd).mpr hsodd
    have h5s : Nat.Coprime 5 s := (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnd
    exact h2s.mul (h5s.pow_left (c + 1))
  have hn10s : n - 10 = (2 * 5 ^ (c + 1)) * s := by rw [hn10, hrs] <;> ring
  have hsig10 : ArithmeticFunction.sigma 0 (n - 10) = (2 * (c + 2)) * ArithmeticFunction.sigma 0 s := by
    rw [hn10s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25]
    have h2v : ArithmeticFunction.sigma 0 (2 * 5 ^ (c + 1)) = 2 * (c + 2) := by
      have hcop2_5 : Nat.Coprime 2 (5 ^ (c + 1)) := (Nat.prime_two.coprime_iff_not_dvd).mpr (by
        intro hcon; have := (Nat.prime_two.dvd_of_dvd_pow hcon); omega)
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2_5]
      have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide
      rw [hs2, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)] <;> ring
    rw [h2v]
  have hbudget : (2 * (c + 2)) * ArithmeticFunction.sigma 0 s ≤ 12 := (by rw [← hsig10]; exact shift)
  have hcases : c = 0 ∨ c = 1 ∨ 2 ≤ c := (by omega)
  rcases hcases with rfl | rfl | hc
  · have hrs0 : (252 * q - 1) = s := by rw [hrs] <;> ring
    have hsle : ArithmeticFunction.sigma 0 (252 * q - 1) ≤ 3 := by rw [hrs0]; omega
    have hs2 : 2 ≤ 252 * q - 1 := (by omega)
    rcases hchar (252 * q - 1) hs2 hsle with hp | ⟨p, hp, heqp⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl ⟨p, hp, heqp⟩)
  · have hrs1 : (252 * q - 1) = 5 * s := by rw [hrs] <;> ring
    have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega)
    exact Or.inr (Or.inr ⟨s, hprime2 s (by omega) hsle, hrs1⟩)
  · exfalso
    have h8 : 8 * ArithmeticFunction.sigma 0 s ≤ 12 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (8:ℕ) ≤ 2 * (c + 2))) hbudget
    have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega)
    have hs_eq1 : s = 1 := by
      by_contra hne
      rw [ArithmeticFunction.sigma_zero_apply] at hsle1
      have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr hs0, s, Nat.mem_divisors_self s hs0, by omega⟩
      omega
    have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide)
    have hcle4 : c ≤ 4 := by rw [hsig1, Nat.mul_one] at hbudget; omega
    rw [hs_eq1, Nat.mul_one] at hrs
    interval_cases c <;> norm_num at hrs <;> omega

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro n hn H hdvd ;   obtain ⟨q, hq⟩ := hdvd ;   have hq1 : 1 ≤ q := (by omega) ;   have hprime2 : ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 2 → Nat.Prime x := by ;     intro x hx hs ;     rw [ArithmeticFunction.sigma_zero_apply] at hs ;     have hx0 : x ≠ 0 := (by omega) ;     have hsub : ({1, x} : Finset ℕ) ⊆ x.divisors := by ;       intro y hy ;       simp only [Finset.mem_insert, Finset.mem_singleton] at hy ;       rw [Nat.mem_divisors] ;       rcases hy with rfl \| rfl ;       · exact ⟨one_dvd _, hx0⟩ ;       · exact ⟨dvd_rfl, hx0⟩ ;     have hc2 : ({1, x} : Finset ℕ).card = 2 := by ;       rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] ;     have heq : x.divisors = {1, x} := (Finset.eq_of_subset_of_card_le hsub (by rw [hc2]; exact hs)).symm ;     rw [Nat.prime_def_lt] ;     refine ⟨by omega, ?_⟩ ;     intro mm hmlt hmdvd ;     have hmem : mm ∈ x.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hx0⟩ ;     rw [heq] at hmem ;     simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ;     rcases hmem with h1 \| h1 ;     · exact h1 ;     · omega ;   have hchar : ∀ r : ℕ, 2 ≤ r → ArithmeticFunction.sigma 0 r ≤ 3 → Nat.Prime r ∨ ∃ p : ℕ, Nat.Prime p ∧ r = p ^ 2 := by ;     intro r hr hcard ;     rw [ArithmeticFunction.sigma_zero_apply] at hcard ;     have hr0 : r ≠ 0 := (by omega) ;     have hr1 : r ≠ 1 := (by omega) ;     have hp : (r.minFac).Prime := Nat.minFac_prime hr1 ;     by_cases hpr : r.minFac = r ;     · exact Or.inl (hpr ▸ hp) ;     · right ;       refine ⟨r.minFac, hp, ?_⟩ ;       have hpd : r.minFac ∣ r := Nat.minFac_dvd r ;       have hp2 : 2 ≤ r.minFac := hp.two_le ;       have hplt : r.minFac < r := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hpd) hpr ;       have hsub2 : ({1, r.minFac, r} : Finset ℕ) ⊆ r.divisors := by ;         intro x hx ;         simp only [Finset.mem_insert, Finset.mem_singleton] at hx ;         rw [Nat.mem_divisors] ;         rcases hx with rfl \| rfl \| rfl ;         · exact ⟨one_dvd r, hr0⟩ ;         · exact ⟨hpd, hr0⟩ ;         · exact ⟨dvd_rfl, hr0⟩ ;       have hcard3 : ({1, r.minFac, r} : Finset ℕ).card = 3 := by ;         rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] ;       have heq : r.divisors = {1, r.minFac, r} := ;         (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard3]; exact hcard)).symm ;       have hmul : r.minFac * (r / r.minFac) = r := Nat.mul_div_cancel' hpd ;       have hqd : r / r.minFac ∣ r := ⟨r.minFac, by rw [Nat.mul_comm]; exact hmul.symm⟩ ;       have hqmem : r / r.minFac ∈ r.divisors := Nat.mem_divisors.mpr ⟨hqd, hr0⟩ ;       rw [heq] at hqmem ;       simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem ;       rcases hqmem with h1 \| h2 \| h3 ;       · rw [h1, mul_one] at hmul ;         exact absurd hmul (Nat.ne_of_lt hplt) ;       · rw [h2] at hmul ;         rw [pow_two] ;         exact hmul.symm ;       · rw [h3] at hmul ;         exfalso ;         nlinarith [hp2, hr, hmul] ;   have shift : ArithmeticFunction.sigma 0 (n - 10) ≤ 12 := by ;     have hsub : n - 10 < n := (by omega) ;     let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x ;     have hbdd : BddAbove (Set.range f) := by ;       refine ⟨2 * n, ?_⟩ ;       rintro y ⟨x, rfl⟩ ;       dsimp [f] ;       rw [ArithmeticFunction.sigma_zero_apply] ;       have hc := Nat.card_divisors_le_self (x : ℕ) ;       have hx : (x : ℕ) < n := x.isLt ;       omega ;     let mm : Fin n := ⟨n - 10, hsub⟩ ;     have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H ;     dsimp [f, mm] at hm ;     omega ;   have hval : (n - 10) / 10 = 252 * q - 1 := (by omega) ;   have hn10 : n - 10 = 10 * (252 * q - 1) := (by omega) ;   rw [hval] ;   have hrodd : ¬ (2 ∣ 252 * q - 1) := (by omega) ;   obtain ⟨c, s, hnd, hrs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show 252 * q - 1 ≠ 0 by omega) 5 (by norm_num) ;   have hs0 : s ≠ 0 := (by rintro rfl; exact hnd (dvd_zero 5)) ;   have hsodd : ¬ (2 ∣ s) := by ;     intro hcon ;     apply hrodd ;     rw [hrs] ;     exact Dvd.dvd.mul_left hcon (5 ^ c) ;   have hcop25 : Nat.Coprime (2 * 5 ^ (c + 1)) s := by ;     have h2s : Nat.Coprime 2 s := (Nat.prime_two.coprime_iff_not_dvd).mpr hsodd ;     have h5s : Nat.Coprime 5 s := (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnd ;     exact h2s.mul (h5s.pow_left (c + 1)) ;   have hn10s : n - 10 = (2 * 5 ^ (c + 1)) * s := by rw [hn10, hrs] <;> ring ;   have hsig10 : ArithmeticFunction.sigma 0 (n - 10) = (2 * (c + 2)) * ArithmeticFunction.sigma 0 s := by ;     rw [hn10s, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop25] ;     have h2v : ArithmeticFunction.sigma 0 (2 * 5 ^ (c + 1)) = 2 * (c + 2) := by ;       have hcop2_5 : Nat.Coprime 2 (5 ^ (c + 1)) := (Nat.prime_two.coprime_iff_not_dvd).mpr (by ;         intro hcon; have := (Nat.prime_two.dvd_of_dvd_pow hcon); omega) ;       rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2_5] ;       have hs2 : ArithmeticFunction.sigma 0 2 = 2 := by native_decide ;       rw [hs2, ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 5)] <;> ring ;     rw [h2v] ;   have hbudget : (2 * (c + 2)) * ArithmeticFunction.sigma 0 s ≤ 12 := (by rw [← hsig10]; exact shift) ;   have hcases : c = 0 ∨ c = 1 ∨ 2 ≤ c := (by omega) ;   rcases hcases with rfl \| rfl \| hc ;   · have hrs0 : (252 * q - 1) = s := by rw [hrs] <;> ring ;     have hsle : ArithmeticFunction.sigma 0 (252 * q - 1) ≤ 3 := by rw [hrs0]; omega ;     have hs2 : 2 ≤ 252 * q - 1 := (by omega) ;     rcases hchar (252 * q - 1) hs2 hsle with hp \| ⟨p, hp, heqp⟩ ;     · exact Or.inl hp ;     · exact Or.inr (Or.inl ⟨p, hp, heqp⟩) ;   · have hrs1 : (252 * q - 1) = 5 * s := by rw [hrs] <;> ring ;     have hsle : ArithmeticFunction.sigma 0 s ≤ 2 := (by omega) ;     exact Or.inr (Or.inr ⟨s, hprime2 s (by omega) hsle, hrs1⟩) ;   · exfalso ;     have h8 : 8 * ArithmeticFunction.sigma 0 s ≤ 12 := le_trans (Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 s) (by omega : (8:ℕ) ≤ 2 * (c + 2))) hbudget ;     have hsle1 : ArithmeticFunction.sigma 0 s ≤ 1 := (by omega) ;     have hs_eq1 : s = 1 := by ;       by_contra hne ;       rw [ArithmeticFunction.sigma_zero_apply] at hsle1 ;       have hcard : 1 < s.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr hs0, s, Nat.mem_divisors_self s hs0, by omega⟩ ;       omega ;     have hsig1 : ArithmeticFunction.sigma 0 s = 1 := (by rw [hs_eq1]; native_decide) ;     have hcle4 : c ≤ 4 := by rw [hsig1, Nat.mul_one] at hbudget; omega ;     rw [hs_eq1, Nat.mul_one] at hrs ;     interval_cases c <;> norm_num at hrs <;> omega` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `89d2f7db4bcf…` → `3abb349d6f50…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
