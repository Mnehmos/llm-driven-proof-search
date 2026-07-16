# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Arithmetic assembly bridge for the Erdős 647 divisibility ladder.

> This proof establishes:
>
> `∀ n : ℕ, 30 ∣ n → 7 ∣ n → 8 ∣ n → 9 ∣ n → 2520 ∣ n`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ n : ℕ, 30 ∣ n → 7 ∣ n → 8 ∣ n → 9 ∣ n → 2520 ∣ n`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `aab8fbdc-c688-4511-b2f6-6f1f9aa5af2e` | terminated (root_proved) | 1 | — | 2026-07-12T19:58:27 | 2026-07-12T19:59:00 |

## Proof tree

- ✅ **root_theorem** : `∀ n : ℕ, 30 ∣ n → 7 ∣ n → 8 ∣ n → 9 ∣ n → 2520 ∣ n`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ n : ℕ, 30 ∣ n → 7 ∣ n → 8 ∣ n → 9 ∣ n → 2520 ∣ n := by
  intro n h30 h7 h8 h9
  have h5 : 5 ∣ n := dvd_trans (by norm_num : 5 ∣ 30) h30
  have h72 : 8 * 9 ∣ n :=
    (show Nat.Coprime 8 9 by norm_num).mul_dvd_of_dvd_of_dvd h8 h9
  have h360 : (8 * 9) * 5 ∣ n :=
    (show Nat.Coprime (8 * 9) 5 by norm_num).mul_dvd_of_dvd_of_dvd h72 h5
  have h2520 : ((8 * 9) * 5) * 7 ∣ n :=
    (show Nat.Coprime ((8 * 9) * 5) 7 by norm_num).mul_dvd_of_dvd_of_dvd h360 h7
  norm_num at h2520 ⊢
  exact h2520

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro n h30 h7 h8 h9 ;   have h5 : 5 ∣ n := dvd_trans (by norm_num : 5 ∣ 30) h30 ;   have h72 : 8 * 9 ∣ n := ;     (show Nat.Coprime 8 9 by norm_num).mul_dvd_of_dvd_of_dvd h8 h9 ;   have h360 : (8 * 9) * 5 ∣ n := ;     (show Nat.Coprime (8 * 9) 5 by norm_num).mul_dvd_of_dvd_of_dvd h72 h5 ;   have h2520 : ((8 * 9) * 5) * 7 ∣ n := ;     (show Nat.Coprime ((8 * 9) * 5) 7 by norm_num).mul_dvd_of_dvd_of_dvd h360 h7 ;   norm_num at h2520 ⊢ ;   exact h2520` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `2005b71e77de…` → `88d7bdbe5a7f…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.

## Exposition (prose — not part of the verified proof)

### Completed 2520 divisibility milestone — _verified_claim_ · _formalized (linked to a formal artifact — the prose itself is still not the proof)_ · by Codex

The verifier-backed artifact chain now reaches the reported necessary condition 2520∣n for every Erdős #647 candidate n>84. Inputs are the previously established 30-divisibility chain, the completed modulo-7 residue chain, the direct 8-divisibility theorem (episode 4edd4cea-3c41-4b16-aa93-0cb747908c00), and the direct 9-divisibility theorem (episode 4884fb8e-01a6-41b8-8c8a-d407faa9b7e9). The arithmetic assembly 30∣n ∧ 7∣n ∧ 8∣n ∧ 9∣n ⇒ 2520∣n is kernel-verified in episode aab8fbdc-c688-4511-b2f6-6f1f9aa5af2e with replay matched(1). The earlier episode 1652d3c6-70f6-4640-bbcd-f0641f80c3d9 contains only a timed-out modular-omega attempt and is not the evidence for this claim.
