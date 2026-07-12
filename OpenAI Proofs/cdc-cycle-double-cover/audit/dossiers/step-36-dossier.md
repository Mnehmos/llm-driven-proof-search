# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — Capstone step 36: compose expansion bridgelessness with the completed 8-flow theorem to obtain a nowhere-zero ends-form F₂³ flow on the concrete cubic expansion.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
    ∃ n : ℕ, (⇑next)^[n] h = k) →
  (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∀ S : Finset (E × Fin 2), (Finset.univ.filter
      (fun k : E ⊕ (E × Fin 2) =>
        ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S)))).card ≠ 1) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E']
      [DecidableEq V'] [DecidableEq E'] (endAt' : E' → Fin 2 → V'),
    (∀ S : Finset V', (Finset.univ.filter
      (fun e : E' => ¬((endAt' e 0 ∈ S) ↔ (endAt' e 1 ∈ S)))).card ≠ 1) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  ∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
    ∃ n : ℕ, (⇑next)^[n] h = k) →
  (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∀ S : Finset (E × Fin 2), (Finset.univ.filter
      (fun k : E ⊕ (E × Fin 2) =>
        ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S)))).card ≠ 1) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E']
      [DecidableEq V'] [DecidableEq E'] (endAt' : E' → Fin 2 → V'),
    (∀ S : Finset V', (Finset.univ.filter
      (fun e : E' => ¬((endAt' e 0 ∈ S) ↔ (endAt' e 1 ∈ S)))).card ≠ 1) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  ∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `cbb5ffbb-e951-4ac5-b1b5-c62873d1a958` | terminated (root_proved) | 1 | — | 2026-07-11T23:47:39 | 2026-07-11T23:48:30 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
    ∃ n : ℕ, (⇑next)^[n] h = k) →
  (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∀ S : Finset (E × Fin 2), (Finset.univ.filter
      (fun k : E ⊕ (E × Fin 2) =>
        ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S)))).card ≠ 1) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E']
      [DecidableEq V'] [DecidableEq E'] (endAt' : E' → Fin 2 → V'),
    (∀ S : Finset V', (Finset.univ.filter
      (fun e : E' => ¬((endAt' e 0 ∈ S) ↔ (endAt' e 1 ∈ S)))).card ≠ 1) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  ∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
    ∃ n : ℕ, (⇑next)^[n] h = k) →
  (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
    (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∀ S : Finset (E × Fin 2), (Finset.univ.filter
      (fun k : E ⊕ (E × Fin 2) =>
        ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S)))).card ≠ 1) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E']
      [DecidableEq V'] [DecidableEq E'] (endAt' : E' → Fin 2 → V'),
    (∀ S : Finset V', (Finset.univ.filter
      (fun e : E' => ¬((endAt' e 0 ∈ S) ↔ (endAt' e 1 ∈ S)))).card ≠ 1) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  ∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) ∧
    (∀ (h : E × Fin 2) (i : Fin 3),
      (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
        (if endAtK k 1 = h then fK k i else 0))) = 0) := by
intro V E _ _ _ _ endAt next endAtK htrans hKs hK0 hK1 hbridge
  hExpansionBridgeless hEightFlow
have hbridgeK : ∀ S : Finset (E × Fin 2), (Finset.univ.filter
    (fun k : E ⊕ (E × Fin 2) =>
      ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S)))).card ≠ 1 :=
  hExpansionBridgeless htrans hKs hK0 hK1 hbridge
exact hEightFlow (E × Fin 2) (E ⊕ (E × Fin 2)) endAtK hbridgeK

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt next endAtK htrans hKs hK0 hK1 hbridge ;   hExpansionBridgeless hEightFlow ; have hbridgeK : ∀ S : Finset (E × Fin 2), (Finset.univ.filter ;     (fun k : E ⊕ (E × Fin 2) => ;       ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S)))).card ≠ 1 := ;   hExpansionBridgeless htrans hKs hK0 hK1 hbridge ; exact hEightFlow (E × Fin 2) (E ⊕ (E × Fin 2)) endAtK hbridgeK` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `5d8dd20fa2f9…` → `b7d2b5792b67…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
