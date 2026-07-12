# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow campaign step JK-D (omission form; mirrors CDCLean.nowhereZeroGammaFlow_of_threeEdgeConnected's glue, JaegerKilpatrick.lean 388-399): three connected spanning edge sets T i such that EVERY edge is omitted by at least one T i imply a nowhere-zero F2^3 flow in ends form. Takes the verified statements of steps 17 (993b9826), 18 (68e5b80e), 19 (c09edee4) as theorem-hypotheses, exactly like the already-verified step 20 (problem 43da22a1) but with the pairwise-disjointness hypothesis replaced by the omission hypothesis (for all e, exists i, e not in T i), because the Nash-Williams packing lives in the DOUBLED graph and the Prod.fst projections to E are connected and omit every edge somewhere but are NOT pairwise disjoint. This is the interface the doubled-packing projection (registered separately) actually discharges. Coverage is immediate: the even superset F i of the complement of T i contains e for the omitting index i. Pre-flighted clean first try on the pinned lean-checker.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Fin 3 → Finset E),
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E'),
    (∀ (i : Fin 3) (v : V'),
      (∑ e ∈ F i, ((if endAt' e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    (∀ e : E', ∃ i : Fin 3, e ∈ F i) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
    ∃ F : Finset E',
      (∀ v : V', (∑ k ∈ F, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E', e ∉ T' → e ∈ F)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ T', (endAt' t 0 = a ∧ endAt' t 1 = b) ∨
        (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    ∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ e : E, ∃ i : Fin 3, e ∉ T i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Fin 3 → Finset E),
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E'),
    (∀ (i : Fin 3) (v : V'),
      (∑ e ∈ F i, ((if endAt' e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    (∀ e : E', ∃ i : Fin 3, e ∈ F i) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
    ∃ F : Finset E',
      (∀ v : V', (∑ k ∈ F, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E', e ∉ T' → e ∈ F)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ T', (endAt' t 0 = a ∧ endAt' t 1 = b) ∨
        (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    ∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ e : E, ∃ i : Fin 3, e ∉ T i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `40271639-6dcd-4ffd-93a0-b87dfc3d7e75` | terminated (root_proved) | 1 | — | 2026-07-11T18:11:45 | 2026-07-11T18:12:46 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Fin 3 → Finset E),
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E'),
    (∀ (i : Fin 3) (v : V'),
      (∑ e ∈ F i, ((if endAt' e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    (∀ e : E', ∃ i : Fin 3, e ∈ F i) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
    ∃ F : Finset E',
      (∀ v : V', (∑ k ∈ F, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E', e ∉ T' → e ∈ F)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ T', (endAt' t 0 = a ∧ endAt' t 1 = b) ∨
        (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    ∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ e : E, ∃ i : Fin 3, e ∉ T i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Fin 3 → Finset E),
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E'),
    (∀ (i : Fin 3) (v : V'),
      (∑ e ∈ F i, ((if endAt' e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    (∀ e : E', ∃ i : Fin 3, e ∈ F i) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
    ∃ F : Finset E',
      (∀ v : V', (∑ k ∈ F, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E', e ∉ T' → e ∈ F)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ T', (endAt' t 0 = a ∧ endAt' t 1 = b) ∨
        (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    ∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ e : E, ∃ i : Fin 3, e ∉ T i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0) := by
intro V E _ _ _ _ endAt T h17 h18 h19 hconn homit
choose F hFe hFs using fun i : Fin 3 =>
  h18 V E endAt (T i) (h19 V E endAt (T i) (hconn i))
have hcov : ∀ e : E, ∃ i : Fin 3, e ∈ F i := by
  intro e
  obtain ⟨i, hi⟩ := homit e
  exact ⟨i, hFs i e hi⟩
exact h17 V E endAt F hFe hcov

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt T h17 h18 h19 hconn homit ; choose F hFe hFs using fun i : Fin 3 => ;   h18 V E endAt (T i) (h19 V E endAt (T i) (hconn i)) ; have hcov : ∀ e : E, ∃ i : Fin 3, e ∈ F i := by ;   intro e ;   obtain ⟨i, hi⟩ := homit e ;   exact ⟨i, hFs i e hi⟩ ; exact h17 V E endAt F hFe hcov` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `e51adac0d22d…` → `0d0e0aa0062f…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
