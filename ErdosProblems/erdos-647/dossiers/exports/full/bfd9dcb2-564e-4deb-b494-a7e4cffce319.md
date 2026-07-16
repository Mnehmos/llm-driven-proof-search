# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Erdos #647 second-layer bookkeeping: deleting at most one primary-square exception and at most one nonsmooth-cofactor exception leaves at least W-2 usable indices.

> This proof establishes:
>
> `∀ (W : ℕ) (A B : Finset (Fin W)),
      A.card ≤ 1 → B.card ≤ 1 →
      W ≤ (Finset.univ \ (A ∪ B)).card + 2`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (W : ℕ) (A B : Finset (Fin W)),
      A.card ≤ 1 → B.card ≤ 1 →
      W ≤ (Finset.univ \ (A ∪ B)).card + 2`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `bfd9dcb2-564e-4deb-b494-a7e4cffce319` | terminated (root_proved) | 1 | — | 2026-07-16T21:00:43 | 2026-07-16T21:01:19 |

## Proof tree

- ✅ **root_theorem** : `∀ (W : ℕ) (A B : Finset (Fin W)),
      A.card ≤ 1 → B.card ≤ 1 →
      W ≤ (Finset.univ \ (A ∪ B)).card + 2`

## The proof, assembled

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ (W : ℕ) (A B : Finset (Fin W)),
      A.card ≤ 1 → B.card ≤ 1 →
      W ≤ (Finset.univ \ (A ∪ B)).card + 2 := by
  intro W A B hA hB
  have hAB : (A ∪ B).card ≤ A.card + B.card :=
    Finset.card_union_le A B
  have hsub : A ∪ B ⊆ (Finset.univ : Finset (Fin W)) :=
    Finset.subset_univ _
  have hpartition := Finset.card_sdiff_add_card_eq_card hsub
  have huniv : (Finset.univ : Finset (Fin W)).card = W := by simp
  omega

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro W A B hA hB ;   have hAB : (A ∪ B).card ≤ A.card + B.card := ;     Finset.card_union_le A B ;   have hsub : A ∪ B ⊆ (Finset.univ : Finset (Fin W)) := ;     Finset.subset_univ _ ;   have hpartition := Finset.card_sdiff_add_card_eq_card hsub ;   have huniv : (Finset.univ : Finset (Fin W)).card = W := by simp ;   omega` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- **Import manifest:** `["Mathlib.Tactic.Ring","Mathlib.Tactic.NormNum","Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `a7757f8057c0…` → `154903471c74…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
