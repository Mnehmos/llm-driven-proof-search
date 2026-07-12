# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Capstone step 37: compose an expansion flow, conservation localization, the cubic even-cover construction, and expansion-cover projection to obtain an indexed even double cover of the original graph.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h : E × Fin 2,
    endAt (next h).1 (next h).2 = endAt h.1 h.2) →
  (∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0) →
    ∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
  ((∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
    ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        member s e = 1).card = 2)) →
  ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
      member s e = 1).card = 2)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h : E × Fin 2,
    endAt (next h).1 (next h).2 = endAt h.1 h.2) →
  (∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0) →
    ∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
  ((∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
    ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        member s e = 1).card = 2)) →
  ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
      member s e = 1).card = 2)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `50dad87f-d22e-4200-be67-8761c79d20cd` | terminated (root_proved) | 1 | — | 2026-07-11T23:49:02 | 2026-07-11T23:49:44 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h : E × Fin 2,
    endAt (next h).1 (next h).2 = endAt h.1 h.2) →
  (∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0) →
    ∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
  ((∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
    ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        member s e = 1).card = 2)) →
  ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
      member s e = 1).card = 2)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h : E × Fin 2,
    endAt (next h).1 (next h).2 = endAt h.1 h.2) →
  (∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0) →
    ∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
  (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
  ((∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
    ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        member s e = 1).card = 2)) →
  ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
      member s e = 1).card = 2) := by
intro V E _ _ _ _ endAt next endAtK hsame hflowK hlocalize
  hExpansionCover hProject
obtain ⟨fK, hnzK, hendsK⟩ := hflowK
have hlocal : ∀ h : E × Fin 2,
    fK (Sum.inl h.1) + fK (Sum.inr h) +
      fK (Sum.inr (next.symm h)) = 0 :=
  hlocalize fK hendsK
have hcoverK := hExpansionCover fK hnzK hlocal
exact hProject hsame hcoverK

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt next endAtK hsame hflowK hlocalize ;   hExpansionCover hProject ; obtain ⟨fK, hnzK, hendsK⟩ := hflowK ; have hlocal : ∀ h : E × Fin 2, ;     fK (Sum.inl h.1) + fK (Sum.inr h) + ;       fK (Sum.inr (next.symm h)) = 0 := ;   hlocalize fK hendsK ; have hcoverK := hExpansionCover fK hnzK hlocal ; exact hProject hsame hcoverK` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `e2fdbec0176c…` → `6427462b64bf…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
