# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdős 647 candidate bridge: eliminate the prime-square branch in the shift-1 classification using 2520-divisibility, hence divisibility by 8.

> This proof establishes:
>
> `∀ n : ℕ, 84 < n → 2520 ∣ n → (Nat.Prime (n - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ n - 1 = p ^ 2) → Nat.Prime (n - 1)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ n : ℕ, 84 < n → 2520 ∣ n → (Nat.Prime (n - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ n - 1 = p ^ 2) → Nat.Prime (n - 1)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `74ae7201-fabb-468e-bd1d-83c2da3bb8ef` | terminated (root_proved) | 1 | — | 2026-07-15T22:34:22 | 2026-07-15T22:34:55 |

## Proof tree

- ✅ **root_theorem** : `∀ n : ℕ, 84 < n → 2520 ∣ n → (Nat.Prime (n - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ n - 1 = p ^ 2) → Nat.Prime (n - 1)`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ n : ℕ, 84 < n → 2520 ∣ n → (Nat.Prime (n - 1) ∨ ∃ p : ℕ, Nat.Prime p ∧ n - 1 = p ^ 2) → Nat.Prime (n - 1) := by
  intro n hn hdvd hclass
  rcases hclass with hp | ⟨p, hp, hp2⟩
  · exact hp
  · exfalso
    obtain ⟨q, hq⟩ := hdvd
    rcases hp.eq_two_or_odd' with htwo | hodd
    · rw [htwo] at hp2
      norm_num at hp2
      omega
    · obtain ⟨r, hr⟩ := hodd
      obtain ⟨t, ht⟩ := Nat.even_mul_succ_self r
      have hsq : p ^ 2 = 8 * t + 1 := by
        rw [hr]
        nlinarith [ht]
      omega

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro n hn hdvd hclass ;   rcases hclass with hp \| ⟨p, hp, hp2⟩ ;   · exact hp ;   · exfalso ;     obtain ⟨q, hq⟩ := hdvd ;     rcases hp.eq_two_or_odd' with htwo \| hodd ;     · rw [htwo] at hp2 ;       norm_num at hp2 ;       omega ;     · obtain ⟨r, hr⟩ := hodd ;       obtain ⟨t, ht⟩ := Nat.even_mul_succ_self r ;       have hsq : p ^ 2 = 8 * t + 1 := by ;         rw [hr] ;         nlinarith [ht] ;       omega` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `2fbaadabdd6c…` → `bf97d519562a…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
