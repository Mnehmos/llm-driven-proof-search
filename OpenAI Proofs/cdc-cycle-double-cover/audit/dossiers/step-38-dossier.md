# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Corrected capstone step 38: rotation plus expansion flow and projection yields an indexed even double cover of the original bridgeless graph.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ e : E, endAt e 0 ≠ endAt e 1) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ next : Equiv.Perm (E × Fin 2),
      (∀ h : E × Fin 2,
        endAt (next h).1 (next h).2 = endAt h.1 h.2) ∧
      (∀ h : E × Fin 2, next h ≠ h) ∧
      (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
        ∃ n : ℕ, (⇑next)^[n] h = k)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
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
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ e : E, endAt e 0 ≠ endAt e 1) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ next : Equiv.Perm (E × Fin 2),
      (∀ h : E × Fin 2,
        endAt (next h).1 (next h).2 = endAt h.1 h.2) ∧
      (∀ h : E × Fin 2, next h ≠ h) ∧
      (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
        ∃ n : ℕ, (⇑next)^[n] h = k)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
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
| `e078a0a6-3a45-404d-84f0-1fa7c9c92c60` | terminated (root_proved) | 1 | — | 2026-07-11T23:51:29 | 2026-07-11T23:52:17 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ e : E, endAt e 0 ≠ endAt e 1) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ next : Equiv.Perm (E × Fin 2),
      (∀ h : E × Fin 2,
        endAt (next h).1 (next h).2 = endAt h.1 h.2) ∧
      (∀ h : E × Fin 2, next h ≠ h) ∧
      (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
        ∃ n : ℕ, (⇑next)^[n] h = k)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
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
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ e : E, endAt e 0 ≠ endAt e 1) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ next : Equiv.Perm (E × Fin 2),
      (∀ h : E × Fin 2,
        endAt (next h).1 (next h).2 = endAt h.1 h.2) ∧
      (∀ h : E × Fin 2, next h ≠ h) ∧
      (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
        ∃ n : ℕ, (⇑next)^[n] h = k)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
  (∀ next : Equiv.Perm (E × Fin 2),
    (∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
      (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
          (if endAtK k 1 = h then fK k i else 0))) = 0)) →
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
intro V E _ _ _ _ endAt hloop hbridge hRotation
  hExpansionFlow hFlowToCover
obtain ⟨next, hsame, hne, htrans⟩ := hRotation hloop hbridge
have hflowK := hExpansionFlow next htrans hbridge
exact hFlowToCover next hsame hflowK

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt hloop hbridge hRotation ;   hExpansionFlow hFlowToCover ; obtain ⟨next, hsame, hne, htrans⟩ := hRotation hloop hbridge ; have hflowK := hExpansionFlow next htrans hbridge ; exact hFlowToCover next hsame hflowK` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `bf11b402fa34…` → `9202ec6f9e77…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
