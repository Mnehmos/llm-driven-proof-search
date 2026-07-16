# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdős 647 direct-full-value residue closure for N≡39325 (mod 46189), replicating Hughes's technique (github.com/scottdhughes/erdos647-proof-chain, lean/Erdos647DirectFullValueClosure.lean, residues2584_16 family) in our environment for the first time. For shift k=16 (16∤2520, outside our clean 13-coefficient set), n-16 = 2584·eval exactly for all N in this class (2584=2³·17·19, verified via the modular identity 2520·39325-16=2584·38351 and 2520·46189=2584·45045), with eval≥2 always. Since σ₀(2584)=16 and ANY prime factor p of eval (whether p|2584 or coprime) forces σ₀(2584p)≥19 (=20/24/24 if p∈{2,17,19} via native_decide, or =16·2=32 if coprime via multiplicativity), and 2584p | n-16 forces σ₀(n-16)≥19, contradicting the shift-16 budget σ₀(n-16)≤18. This closes N=39325 unconditionally (not just a bridging closure for one ℓ) — removes this residue from our environment's 45-class open frontier. Cites Hughes (github.com/scottdhughes/erdos647-proof-chain) and dossier 83bf3744.

> This proof establishes:
>
> `∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 46189 = 39325 → False`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 46189 = 39325 → False`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `abbba24e-42d0-4771-927c-dcdfbbcccfc9` | terminated (root_proved) | 1 | — | 2026-07-13T11:13:52 | 2026-07-13T11:14:43 |

## Proof tree

- ✅ **root_theorem** : `∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 46189 = 39325 → False`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ n N : ℕ, 84 < n → (⨆ m : Fin n, (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 → n = 2520 * N → N % 46189 = 39325 → False := by
  intro n N hn H hnN hres
  have shift : ArithmeticFunction.sigma 0 (n - 16) ≤ 18 := by
    have hsub : n - 16 < n := by omega
    let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x
    have hbdd : BddAbove (Set.range f) := by
      refine ⟨2 * n, ?_⟩
      rintro y ⟨x, rfl⟩
      dsimp [f]
      rw [ArithmeticFunction.sigma_zero_apply]
      have hc := Nat.card_divisors_le_self (x : ℕ)
      have hx : (x : ℕ) < n := x.isLt
      omega
    let mm : Fin n := ⟨n - 16, hsub⟩
    have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H
    dsimp [f, mm] at hm
    omega
  set q := N / 46189 with hq_def
  have hNeq : N = 46189 * q + 39325 := by omega
  have hn16lin : n = 2584 * 45045 * q + 2584 * 38351 + 16 := by rw [hnN, hNeq]; ring
  have hn16 : n - 16 = 2584 * (45045 * q + 38351) := by
    have : n - 16 = 2584 * 45045 * q + 2584 * 38351 := by omega
    rw [this]; ring
  set eval := 45045 * q + 38351 with heval_def
  have heval2 : eval ≠ 1 := by dsimp [eval]; omega
  have hsig2584 : ArithmeticFunction.sigma 0 2584 = 16 := by native_decide
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd heval2
  have hn16ne : n - 16 ≠ 0 := by omega
  by_cases hp2584 : p ∣ 2584
  · have hp2584fac : p = 2 ∨ p = 17 ∨ p = 19 := by
      have h2584eq : (2584 : ℕ) = 8 * (17 * 19) := by norm_num
      rw [h2584eq] at hp2584
      rcases (hpp.dvd_mul).mp hp2584 with h8 | h1719
      · left
        have h8pow : (8:ℕ) = 2 ^ 3 := by norm_num
        rw [h8pow] at h8
        have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow h8
        exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hp2
      · rcases (hpp.dvd_mul).mp h1719 with h17 | h19
        · right; left
          exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h17
        · right; right
          exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h19
    have h2584p_dvd : 2584 * p ∣ (n - 16) := by
      rw [hn16]; exact Nat.mul_dvd_mul_left 2584 hpdvd
    have hsig_ge : 19 ≤ ArithmeticFunction.sigma 0 (2584 * p) := by
      rcases hp2584fac with rfl | rfl | rfl
      · native_decide
      · native_decide
      · native_decide
    have hsub2 : (2584 * p).divisors ⊆ (n - 16).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans h2584p_dvd, hn16ne⟩
    have hcard_le : ArithmeticFunction.sigma 0 (2584 * p) ≤ ArithmeticFunction.sigma 0 (n - 16) := by
      rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
      exact Finset.card_le_card hsub2
    omega
  · have hcop : Nat.Coprime 2584 p := ((hpp.coprime_iff_not_dvd).mpr hp2584).symm
    have h2584p_dvd : 2584 * p ∣ (n - 16) := by
      rw [hn16]; exact Nat.mul_dvd_mul_left 2584 hpdvd
    have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
      rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hpp]
    have hsig_mul : ArithmeticFunction.sigma 0 (2584 * p) = ArithmeticFunction.sigma 0 2584 * ArithmeticFunction.sigma 0 p :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
    have hsig_ge : 19 ≤ ArithmeticFunction.sigma 0 (2584 * p) := by
      rw [hsig_mul, hsig2584, hsigp]; norm_num
    have hsub2 : (2584 * p).divisors ⊆ (n - 16).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨hd.1.trans h2584p_dvd, hn16ne⟩
    have hcard_le : ArithmeticFunction.sigma 0 (2584 * p) ≤ ArithmeticFunction.sigma 0 (n - 16) := by
      rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
      exact Finset.card_le_card hsub2
    omega

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro n N hn H hnN hres ;   have shift : ArithmeticFunction.sigma 0 (n - 16) ≤ 18 := by ;     have hsub : n - 16 < n := by omega ;     let f : Fin n → ℕ := fun x => (x : ℕ) + ArithmeticFunction.sigma 0 x ;     have hbdd : BddAbove (Set.range f) := by ;       refine ⟨2 * n, ?_⟩ ;       rintro y ⟨x, rfl⟩ ;       dsimp [f] ;       rw [ArithmeticFunction.sigma_zero_apply] ;       have hc := Nat.card_divisors_le_self (x : ℕ) ;       have hx : (x : ℕ) < n := x.isLt ;       omega ;     let mm : Fin n := ⟨n - 16, hsub⟩ ;     have hm : f mm ≤ n + 2 := le_trans (le_ciSup hbdd mm) H ;     dsimp [f, mm] at hm ;     omega ;   set q := N / 46189 with hq_def ;   have hNeq : N = 46189 * q + 39325 := by omega ;   have hn16lin : n = 2584 * 45045 * q + 2584 * 38351 + 16 := by rw [hnN, hNeq]; ring ;   have hn16 : n - 16 = 2584 * (45045 * q + 38351) := by ;     have : n - 16 = 2584 * 45045 * q + 2584 * 38351 := by omega ;     rw [this]; ring ;   set eval := 45045 * q + 38351 with heval_def ;   have heval2 : eval ≠ 1 := by dsimp [eval]; omega ;   have hsig2584 : ArithmeticFunction.sigma 0 2584 = 16 := by native_decide ;   obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd heval2 ;   have hn16ne : n - 16 ≠ 0 := by omega ;   by_cases hp2584 : p ∣ 2584 ;   · have hp2584fac : p = 2 ∨ p = 17 ∨ p = 19 := by ;       have h2584eq : (2584 : ℕ) = 8 * (17 * 19) := by norm_num ;       rw [h2584eq] at hp2584 ;       rcases (hpp.dvd_mul).mp hp2584 with h8 \| h1719 ;       · left ;         have h8pow : (8:ℕ) = 2 ^ 3 := by norm_num ;         rw [h8pow] at h8 ;         have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow h8 ;         exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hp2 ;       · rcases (hpp.dvd_mul).mp h1719 with h17 \| h19 ;         · right; left ;           exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h17 ;         · right; right ;           exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).mp h19 ;     have h2584p_dvd : 2584 * p ∣ (n - 16) := by ;       rw [hn16]; exact Nat.mul_dvd_mul_left 2584 hpdvd ;     have hsig_ge : 19 ≤ ArithmeticFunction.sigma 0 (2584 * p) := by ;       rcases hp2584fac with rfl \| rfl \| rfl ;       · native_decide ;       · native_decide ;       · native_decide ;     have hsub2 : (2584 * p).divisors ⊆ (n - 16).divisors := by ;       intro d hd ;       rw [Nat.mem_divisors] at hd ⊢ ;       exact ⟨hd.1.trans h2584p_dvd, hn16ne⟩ ;     have hcard_le : ArithmeticFunction.sigma 0 (2584 * p) ≤ ArithmeticFunction.sigma 0 (n - 16) := by ;       rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply] ;       exact Finset.card_le_card hsub2 ;     omega ;   · have hcop : Nat.Coprime 2584 p := ((hpp.coprime_iff_not_dvd).mpr hp2584).symm ;     have h2584p_dvd : 2584 * p ∣ (n - 16) := by ;       rw [hn16]; exact Nat.mul_dvd_mul_left 2584 hpdvd ;     have hsigp : ArithmeticFunction.sigma 0 p = 2 := by ;       rw [show p = p ^ 1 from (pow_one p).symm, ArithmeticFunction.sigma_zero_apply_prime_pow hpp] ;     have hsig_mul : ArithmeticFunction.sigma 0 (2584 * p) = ArithmeticFunction.sigma 0 2584 * ArithmeticFunction.sigma 0 p := ;       ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop ;     have hsig_ge : 19 ≤ ArithmeticFunction.sigma 0 (2584 * p) := by ;       rw [hsig_mul, hsig2584, hsigp]; norm_num ;     have hsub2 : (2584 * p).divisors ⊆ (n - 16).divisors := by ;       intro d hd ;       rw [Nat.mem_divisors] at hd ⊢ ;       exact ⟨hd.1.trans h2584p_dvd, hn16ne⟩ ;     have hcard_le : ArithmeticFunction.sigma 0 (2584 * p) ≤ ArithmeticFunction.sigma 0 (n - 16) := by ;       rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply] ;       exact Finset.card_le_card hsub2 ;     omega` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `6c9200f008ca…` → `9952cec3776e…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
