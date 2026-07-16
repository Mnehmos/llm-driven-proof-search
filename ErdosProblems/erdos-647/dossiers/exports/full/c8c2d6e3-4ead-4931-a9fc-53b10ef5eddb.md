# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Finite exceptional-prime set divisor-power bound: local constants on S and the rough threshold outside S imply a global divisor-power estimate.

> This proof establishes:
>
> `∀ (r m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ),
      0 < r →
      1 ≤ m →
      (∀ p ∈ S, 1 ≤ c p) →
      (∀ p ∈ S, p.Prime → p ∣ m → ∀ a : ℕ, 1 ≤ a →
        (a + 1) ^ r ≤ c p * p ^ a) →
      (∀ p : ℕ, p.Prime → p ∣ m → p ∉ S → 2 ^ r ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ r ≤ (∏ p ∈ S, c p) * m`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (r m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ),
      0 < r →
      1 ≤ m →
      (∀ p ∈ S, 1 ≤ c p) →
      (∀ p ∈ S, p.Prime → p ∣ m → ∀ a : ℕ, 1 ≤ a →
        (a + 1) ^ r ≤ c p * p ^ a) →
      (∀ p : ℕ, p.Prime → p ∣ m → p ∉ S → 2 ^ r ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ r ≤ (∏ p ∈ S, c p) * m`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `c8c2d6e3-4ead-4931-a9fc-53b10ef5eddb` | terminated (root_proved) | 1 | — | 2026-07-16T19:28:03 | 2026-07-16T19:28:29 |

## Proof tree

- ✅ **root_theorem** : `∀ (r m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ),
      0 < r →
      1 ≤ m →
      (∀ p ∈ S, 1 ≤ c p) →
      (∀ p ∈ S, p.Prime → p ∣ m → ∀ a : ℕ, 1 ≤ a →
        (a + 1) ^ r ≤ c p * p ^ a) →
      (∀ p : ℕ, p.Prime → p ∣ m → p ∉ S → 2 ^ r ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ r ≤ (∏ p ∈ S, c p) * m`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ (r m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ),
      0 < r →
      1 ≤ m →
      (∀ p ∈ S, 1 ≤ c p) →
      (∀ p ∈ S, p.Prime → p ∣ m → ∀ a : ℕ, 1 ≤ a →
        (a + 1) ^ r ≤ c p * p ^ a) →
      (∀ p : ℕ, p.Prime → p ∣ m → p ∉ S → 2 ^ r ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ r ≤ (∏ p ∈ S, c p) * m := by

  intro r m S c hr hm hc hsmall hrough
  have hm0 : m ≠ 0 := by omega
  have hbinary : ∀ b : ℕ, b + 1 ≤ 2 ^ b := by
    intro b
    induction b with
    | zero => simp
    | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hlocal : ∀ p ∈ m.primeFactors,
      (m.factorization p + 1) ^ r ≤
        (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    have hpa : 1 ≤ m.factorization p :=
      hpp.factorization_pos_of_dvd hm0 hpd
    by_cases hpS : p ∈ S
    · simp only [hpS, if_true]
      exact hsmall p hpS hpp hpd _ hpa
    · simp only [hpS, if_false, one_mul]
      calc
        (m.factorization p + 1) ^ r ≤ (2 ^ (m.factorization p)) ^ r :=
          Nat.pow_le_pow_left (hbinary _) r
        _ = (2 ^ r) ^ (m.factorization p) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p ^ (m.factorization p) :=
          Nat.pow_le_pow_left (hrough p hpp hpd hpS) _
  have hsigma : ArithmeticFunction.sigma 0 m =
      ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
    simp
  have hmprod : (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) = m := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hm0
  have hbase : (ArithmeticFunction.sigma 0 m) ^ r ≤
      (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by
    rw [hsigma, ← Finset.prod_pow]
    calc
      ∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ r
          ≤ ∏ p ∈ m.primeFactors,
              (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by
                exact Finset.prod_le_prod' hlocal
      _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) *
            (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
              rw [Finset.prod_mul_distrib]
      _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by
            rw [hmprod]
  have hprod_eq :
      (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) =
        ∏ p ∈ m.primeFactors.filter (fun p => p ∈ S), c p := by
    rw [Finset.prod_filter]
  have hsub : m.primeFactors.filter (fun p => p ∈ S) ⊆ S := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hprod_le :
      (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) ≤
        ∏ p ∈ S, c p := by
    rw [hprod_eq]
    exact Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun _ _ => Nat.zero_le _)
      (fun p hpS _ => hc p hpS)
  exact hbase.trans (Nat.mul_le_mul_right m hprod_le)

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro r m S c hr hm hc hsmall hrough ;   have hm0 : m ≠ 0 := by omega ;   have hbinary : ∀ b : ℕ, b + 1 ≤ 2 ^ b := by ;     intro b ;     induction b with ;     \| zero => simp ;     \| succ k ih => ;       calc ;         k + 1 + 1 ≤ 2 * (k + 1) := by omega ;         _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih ;         _ = 2 ^ (k + 1) := by rw [pow_succ]; ring ;   have hlocal : ∀ p ∈ m.primeFactors, ;       (m.factorization p + 1) ^ r ≤ ;         (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by ;     intro p hp ;     have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp ;     have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp ;     have hpa : 1 ≤ m.factorization p := ;       hpp.factorization_pos_of_dvd hm0 hpd ;     by_cases hpS : p ∈ S ;     · simp only [hpS, if_true] ;       exact hsmall p hpS hpp hpd _ hpa ;     · simp only [hpS, if_false, one_mul] ;       calc ;         (m.factorization p + 1) ^ r ≤ (2 ^ (m.factorization p)) ^ r := ;           Nat.pow_le_pow_left (hbinary _) r ;         _ = (2 ^ r) ^ (m.factorization p) := by ;           rw [← pow_mul, ← pow_mul, Nat.mul_comm] ;         _ ≤ p ^ (m.factorization p) := ;           Nat.pow_le_pow_left (hrough p hpp hpd hpS) _ ;   have hsigma : ArithmeticFunction.sigma 0 m = ;       ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by ;     rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0] ;     simp ;   have hmprod : (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) = m := by ;     rw [← Nat.prod_factorization_eq_prod_primeFactors] ;     exact Nat.prod_factorization_pow_eq_self hm0 ;   have hbase : (ArithmeticFunction.sigma 0 m) ^ r ≤ ;       (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by ;     rw [hsigma, ← Finset.prod_pow] ;     calc ;       ∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ r ;           ≤ ∏ p ∈ m.primeFactors, ;               (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by ;                 exact Finset.prod_le_prod' hlocal ;       _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * ;             (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by ;               rw [Finset.prod_mul_distrib] ;       _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by ;             rw [hmprod] ;   have hprod_eq : ;       (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) = ;         ∏ p ∈ m.primeFactors.filter (fun p => p ∈ S), c p := by ;     rw [Finset.prod_filter] ;   have hsub : m.primeFactors.filter (fun p => p ∈ S) ⊆ S := by ;     intro p hp ;     exact (Finset.mem_filter.mp hp).2 ;   have hprod_le : ;       (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) ≤ ;         ∏ p ∈ S, c p := by ;     rw [hprod_eq] ;     exact Finset.prod_le_prod_of_subset_of_one_le hsub ;       (fun _ _ => Nat.zero_le _) ;       (fun p hpS _ => hc p hpS) ;   exact hbase.trans (Nat.mul_le_mul_right m hprod_le)` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `543d014434eb…` → `22c7454e1af5…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
