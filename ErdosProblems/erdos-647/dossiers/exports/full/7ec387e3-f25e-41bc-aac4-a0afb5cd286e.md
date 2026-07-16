# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdos Problem #647 sub-AP congruence closure (novel, environment-original, non-trivial pattern, 4-prime g requiring a 16-leaf case tree with full hexists_other/pow-exclusion machinery). N ≡ 29601 (mod 1431859 = 46189 × 31), combined with N ≡ 29601 (mod 31). Shift-26 evaluation n-26 = 15314 * eval (15314 = 2*13*19*31) with eval ≥ 4871 forces sigma_0(n-26) > 28. Cites Hughes (github.com/scottdhughes/erdos647-proof-chain) for the base 46189 modular reduction; this sub-AP instance is original to this environment.

> This proof establishes:
>
> `∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 29601 → False`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 29601 → False`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `7ec387e3-f25e-41bc-aac4-a0afb5cd286e` | terminated (root_proved) | 1 | — | 2026-07-13T14:35:48 | 2026-07-13T14:37:10 |

## Proof tree

- ✅ **root_theorem** : `∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 29601 → False`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 1431859 = 29601 → False := by
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

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro n N hn H hnN hres ;   have shift : ArithmeticFunction.sigma 0 (n - 26) ≤ 28 := by ;     have hsub : n - 26 < n := by omega ;     let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x ;     have hbdd : BddAbove (Set.range f) := by ;       refine ⟨2 * n, ?_⟩ ;       rintro y ⟨x, rfl⟩ ;       dsimp [f] ;       rw [ArithmeticFunction.sigma_zero_apply] ;       have hc := Nat.card_divisors_le_self (x : ℕ) ;       have hx : (x : ℕ) < n := x.isLt ;       omega ;     let mm : Fin n := ⟨n - 26, hsub⟩ ;     have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H ;     dsimp [f, mm] at hm ;     omega ;   set q := N / 1431859 with hq_def ;   have hNeq : N = 1431859 * q + 29601 := by omega ;   have hnk : n - 26 = 15314 * (235620 * q + 4871) := by ;     have h1 : n - 26 = 15314 * 235620 * q + 15314 * 4871 := by omega ;     rw [h1]; ring ;   set eval := 235620 * q + 4871 with heval_def ;   have heval_ge : 4871 ≤ eval := by dsimp [eval]; omega ;   have hnkne : n - 26 ≠ 0 := by omega ;   have hmono : ∀ a : ℕ, a ∣ (n - 26) → ArithmeticFunction.sigma 0 a ≤ ArithmeticFunction.sigma 0 (n - 26) := by ;     intro a hadvd ;     have hsub2 : a.divisors ⊆ (n - 26).divisors := by ;       intro d hd ;       rw [Nat.mem_divisors] at hd ⊢ ;       exact ⟨hd.1.trans hadvd, hnkne⟩ ;     rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply] ;     exact Finset.card_le_card hsub2 ;   have hclose : ∀ D : ℕ, D ∣ eval → 28 < ArithmeticFunction.sigma 0 (15314 * D) → False := by ;     intro D hDdvd hsig ;     have hDm : 15314 * D ∣ (n - 26) := by rw [hnk]; exact Nat.mul_dvd_mul_left 15314 hDdvd ;     have := hmono (15314 * D) hDm ;     omega ;   have hexists_other : ∀ p : ℕ, Nat.Prime p → p ∣ eval → (∀ s, eval ≠ p ^ s) → ;       ∃ p' : ℕ, Nat.Prime p' ∧ p' ∣ eval ∧ p' ≠ p := by ;     intro p hp hpdvd hnotpow ;     by_contra hnone ;     push_neg at hnone ;     have heval0 : eval ≠ 0 := by omega ;     have hpow := Nat.eq_prime_pow_of_unique_prime_dvd heval0 (fun {r} hq hqd => hnone r hq hqd) ;     exact hnotpow _ hpow ;   have hnopowA : ∀ s : ℕ, eval ≠ 2 ^ s := by ;     intro s hs ;     have heq2 : n - 26 = 2 ^ (s + 1) * 7657 := by rw [hnk, hs]; ring ;     have hcop : Nat.Coprime (2 ^ (s + 1)) 7657 := by ;       have hbase : Nat.Coprime 2 7657 := by norm_num ;       exact hbase.pow_left (s + 1) ;     have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 7657 := by ;       rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ;         ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 2)] ;     have hsigX : ArithmeticFunction.sigma 0 7657 = 8 := by native_decide ;     rw [hsigX] at hsigeq ;     have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift ;     have hsbound : s ≤ 1 := by omega ;     interval_cases s ;     · norm_num at hs; omega ;     · norm_num at hs; omega ;   have hnopowB : ∀ s : ℕ, eval ≠ 13 ^ s := by ;     intro s hs ;     have heq2 : n - 26 = 13 ^ (s + 1) * 1178 := by rw [hnk, hs]; ring ;     have hcop : Nat.Coprime (13 ^ (s + 1)) 1178 := by ;       have hbase : Nat.Coprime 13 1178 := by norm_num ;       exact hbase.pow_left (s + 1) ;     have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 1178 := by ;       rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ;         ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 13)] ;     have hsigX : ArithmeticFunction.sigma 0 1178 = 8 := by native_decide ;     rw [hsigX] at hsigeq ;     have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift ;     have hsbound : s ≤ 1 := by omega ;     interval_cases s ;     · norm_num at hs; omega ;     · norm_num at hs; omega ;   have hnopowC : ∀ s : ℕ, eval ≠ 19 ^ s := by ;     intro s hs ;     have heq2 : n - 26 = 19 ^ (s + 1) * 806 := by rw [hnk, hs]; ring ;     have hcop : Nat.Coprime (19 ^ (s + 1)) 806 := by ;       have hbase : Nat.Coprime 19 806 := by norm_num ;       exact hbase.pow_left (s + 1) ;     have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 806 := by ;       rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ;         ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 19)] ;     have hsigX : ArithmeticFunction.sigma 0 806 = 8 := by native_decide ;     rw [hsigX] at hsigeq ;     have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift ;     have hsbound : s ≤ 1 := by omega ;     interval_cases s ;     · norm_num at hs; omega ;     · norm_num at hs; omega ;   have hnopowD : ∀ s : ℕ, eval ≠ 31 ^ s := by ;     intro s hs ;     have heq2 : n - 26 = 31 ^ (s + 1) * 494 := by rw [hnk, hs]; ring ;     have hcop : Nat.Coprime (31 ^ (s + 1)) 494 := by ;       have hbase : Nat.Coprime 31 494 := by norm_num ;       exact hbase.pow_left (s + 1) ;     have hsigeq : ArithmeticFunction.sigma 0 (n - 26) = (s + 2) * ArithmeticFunction.sigma 0 494 := by ;       rw [heq2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, ;         ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num : Nat.Prime 31)] ;     have hsigX : ArithmeticFunction.sigma 0 494 = 8 := by native_decide ;     rw [hsigX] at hsigeq ;     have hsle : (s + 2) * 8 ≤ 28 := by rw [← hsigeq]; exact shift ;     have hsbound : s ≤ 1 := by omega ;     interval_cases s ;     · norm_num at hs; omega ;     · norm_num at hs; omega ;   by_cases h1 : 2 ∣ eval ;   · by_cases h2 : 13 ∣ eval ;     · by_cases h3 : 19 ∣ eval ;       · by_cases h4 : 31 ∣ eval ;         · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2 ;           exact hclose 26 hpair (by native_decide) ;         · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2 ;           exact hclose 26 hpair (by native_decide) ;       · by_cases h4 : 31 ∣ eval ;         · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2 ;           exact hclose 26 hpair (by native_decide) ;         · have hpair : (26:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2 ;           exact hclose 26 hpair (by native_decide) ;     · by_cases h3 : 19 ∣ eval ;       · by_cases h4 : 31 ∣ eval ;         · have hpair : (38:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3 ;           exact hclose 38 hpair (by native_decide) ;         · have hpair : (38:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h3 ;           exact hclose 38 hpair (by native_decide) ;       · by_cases h4 : 31 ∣ eval ;         · have hpair : (62:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h4 ;           exact hclose 62 hpair (by native_decide) ;         · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 2 (by norm_num) h1 hnopowA ;           have hcopg : Nat.Coprime 15314 p := by ;             have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide ;             refine ((hp.coprime_iff_not_dvd).mpr ?_).symm ;             intro hpdvdg ;             have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩ ;             rw [hfac] at hpmem ;             simp at hpmem ;             rcases hpmem with rfl \| rfl \| rfl \| rfl ;             · exact hpne rfl ;             · exact h2 hpdvd ;             · exact h3 hpdvd ;             · exact h4 hpdvd ;           have hsigp : ArithmeticFunction.sigma 0 p = 2 := by ;             rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp] ;           have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide ;           have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by ;             rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp] ;             norm_num ;           exact hclose p hpdvd hfinal ;   · by_cases h2 : 13 ∣ eval ;     · by_cases h3 : 19 ∣ eval ;       · by_cases h4 : 31 ∣ eval ;         · have hpair : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3 ;           exact hclose 247 hpair (by native_decide) ;         · have hpair : (247:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3 ;           exact hclose 247 hpair (by native_decide) ;       · by_cases h4 : 31 ∣ eval ;         · have hpair : (403:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h4 ;           exact hclose 403 hpair (by native_decide) ;         · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 13 (by norm_num) h2 hnopowB ;           have hcopg : Nat.Coprime 15314 p := by ;             have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide ;             refine ((hp.coprime_iff_not_dvd).mpr ?_).symm ;             intro hpdvdg ;             have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩ ;             rw [hfac] at hpmem ;             simp at hpmem ;             rcases hpmem with rfl \| rfl \| rfl \| rfl ;             · exact h1 hpdvd ;             · exact hpne rfl ;             · exact h3 hpdvd ;             · exact h4 hpdvd ;           have hsigp : ArithmeticFunction.sigma 0 p = 2 := by ;             rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp] ;           have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide ;           have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by ;             rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp] ;             norm_num ;           exact hclose p hpdvd hfinal ;     · by_cases h3 : 19 ∣ eval ;       · by_cases h4 : 31 ∣ eval ;         · have hpair : (589:ℕ) ∣ eval := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4 ;           exact hclose 589 hpair (by native_decide) ;         · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 19 (by norm_num) h3 hnopowC ;           have hcopg : Nat.Coprime 15314 p := by ;             have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide ;             refine ((hp.coprime_iff_not_dvd).mpr ?_).symm ;             intro hpdvdg ;             have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩ ;             rw [hfac] at hpmem ;             simp at hpmem ;             rcases hpmem with rfl \| rfl \| rfl \| rfl ;             · exact h1 hpdvd ;             · exact h2 hpdvd ;             · exact hpne rfl ;             · exact h4 hpdvd ;           have hsigp : ArithmeticFunction.sigma 0 p = 2 := by ;             rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp] ;           have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide ;           have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by ;             rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp] ;             norm_num ;           exact hclose p hpdvd hfinal ;       · by_cases h4 : 31 ∣ eval ;         · obtain ⟨p, hp, hpdvd, hpne⟩ := hexists_other 31 (by norm_num) h4 hnopowD ;           have hcopg : Nat.Coprime 15314 p := by ;             have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide ;             refine ((hp.coprime_iff_not_dvd).mpr ?_).symm ;             intro hpdvdg ;             have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩ ;             rw [hfac] at hpmem ;             simp at hpmem ;             rcases hpmem with rfl \| rfl \| rfl \| rfl ;             · exact h1 hpdvd ;             · exact h2 hpdvd ;             · exact h3 hpdvd ;             · exact hpne rfl ;           have hsigp : ArithmeticFunction.sigma 0 p = 2 := by ;             rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp] ;           have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide ;           have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by ;             rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp] ;             norm_num ;           exact hclose p hpdvd hfinal ;         · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show eval ≠ 1 by omega) ;           have hcopg : Nat.Coprime 15314 p := by ;             have hfac : (15314:ℕ).primeFactors = {2, 13, 19, 31} := by native_decide ;             refine ((hp.coprime_iff_not_dvd).mpr ?_).symm ;             intro hpdvdg ;             have hpmem : p ∈ (15314:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvdg, by norm_num⟩ ;             rw [hfac] at hpmem ;             simp at hpmem ;             rcases hpmem with rfl \| rfl \| rfl \| rfl ;             · exact h1 hpdvd ;             · exact h2 hpdvd ;             · exact h3 hpdvd ;             · exact h4 hpdvd ;           have hsigp : ArithmeticFunction.sigma 0 p = 2 := by ;             rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hp] ;           have hsg : ArithmeticFunction.sigma 0 15314 = 16 := by native_decide ;           have hfinal : 28 < ArithmeticFunction.sigma 0 (15314 * p) := by ;             rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcopg, hsg, hsigp] ;             norm_num ;           exact hclose p hpdvd hfinal` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `38cbad08c44c…` → `32be7a321621…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
