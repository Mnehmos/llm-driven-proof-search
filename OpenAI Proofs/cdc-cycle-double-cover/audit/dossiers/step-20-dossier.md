# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow campaign step JK-D-lite (composition of nowhereZeroGammaFlow_of_evenCover with the even-superset construction, i.e. Jaeger's argument given a 3-tree packing): if a finite multigraph carries three pairwise-disjoint connected spanning edge sets, it has a nowhere-zero F2^3 flow in ends form. Takes the verified statements of steps 17 (problem 993b9826), 18 (68e5b80e) and 19 (c09edee4) as theorem-hypotheses; per tree i, chain connectivity to fundamental cycles to an even superset F i of the complement; every edge lies in at most one tree by disjointness hence outside at least one of trees 0 and 1, so the F i cover all edges; conclude by the flow-combination theorem. Together with a tree packing of the expansion (Nash-Williams, pending) and the ends-to-localized conservation glue this discharges the flow hypothesis of the CDC reduction chain. Pre-flighted clean first try on the pinned lean-checker (14s).

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
  (∀ i j : Fin 3, i ≠ j → Disjoint (T i) (T j)) →
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
  (∀ i j : Fin 3, i ≠ j → Disjoint (T i) (T j)) →
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
| `c4caad40-c393-4c67-aac4-d4d51aed3f3f` | terminated (root_proved) | 1 | — | 2026-07-11T17:55:55 | 2026-07-11T17:58:45 |

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
  (∀ i j : Fin 3, i ≠ j → Disjoint (T i) (T j)) →
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
  (∀ i j : Fin 3, i ≠ j → Disjoint (T i) (T j)) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0) := by
intro V E _ _ _ _ endAt T h17 h18 h19 hconn hdisj
choose F hFe hFs using fun i : Fin 3 =>
  h18 V E endAt (T i) (h19 V E endAt (T i) (hconn i))
have hcov : ∀ e : E, ∃ i : Fin 3, e ∈ F i := by
  intro e
  by_cases h0 : e ∈ T 0
  · refine ⟨1, hFs 1 e ?_⟩
    intro h1
    exact Finset.disjoint_left.mp (hdisj 0 1 (by decide)) h0 h1
  · exact ⟨0, hFs 0 e h0⟩
exact h17 V E endAt F hFe hcov

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt T h17 h18 h19 hconn hdisj ; choose F hFe hFs using fun i : Fin 3 => ;   h18 V E endAt (T i) (h19 V E endAt (T i) (hconn i)) ; have hcov : ∀ e : E, ∃ i : Fin 3, e ∈ F i := by ;   intro e ;   by_cases h0 : e ∈ T 0 ;   · refine ⟨1, hFs 1 e ?_⟩ ;     intro h1 ;     exact Finset.disjoint_left.mp (hdisj 0 1 (by decide)) h0 h1 ;   · exact ⟨0, hFs 0 e h0⟩ ; exact h17 V E endAt F hFe hcov` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `bbe7d08abf71…` → `b97bf3508bc9…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
