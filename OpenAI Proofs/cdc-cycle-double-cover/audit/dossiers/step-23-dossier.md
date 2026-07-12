# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow campaign step JK-D projection (mirrors the packing-to-omission half of CDCLean.exists_three_spanningTrees_omitting_each_edge, JaegerKilpatrick.lean 334-386): three pairwise-disjoint connected spanning edge sets in the DOUBLED multigraph (edge type E x Fin 2, both copies with the ends of the base edge) project under Prod.fst to three connected spanning edge sets in E such that every edge is omitted by at least one of them. Connectivity of each projection is Relation.ReflTransGen.mono (each doubled step becomes the base-edge step with the same ends). Omission is the pigeonhole: if e lay in all three projections, choosing a witness copy x i in U i with (x i).1 = e makes i to (x i).2 an injective map Fin 3 to Fin 2 (equal second components force equal witnesses, contradicting pairwise disjointness), contradicting cardinality. Unlike the reference we need no spanning-tree structure, only connectivity plus omission -- our even-superset layer (steps 18-19) works for arbitrary connected sets. Conclusion matches the T-hypotheses of verified step 22 (problem 1cd81f06); hypotheses match the tree-packing conclusion the Nash-Williams campaign will produce at edge type E x Fin 2. Pre-flighted clean first try on the pinned lean-checker.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (U : Fin 3 → Finset (E × Fin 2)),
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
      (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) →
  (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) →
  ∃ T : Fin 3 → Finset E,
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) u v) ∧
    (∀ e : E, ∃ i : Fin 3, e ∉ T i)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (U : Fin 3 → Finset (E × Fin 2)),
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
      (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) →
  (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) →
  ∃ T : Fin 3 → Finset E,
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) u v) ∧
    (∀ e : E, ∃ i : Fin 3, e ∉ T i)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `10f70a28-eb75-45e4-bee8-5b8379977a96` | terminated (root_proved) | 1 | — | 2026-07-11T18:13:27 | 2026-07-11T18:14:29 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (U : Fin 3 → Finset (E × Fin 2)),
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
      (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) →
  (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) →
  ∃ T : Fin 3 → Finset E,
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) u v) ∧
    (∀ e : E, ∃ i : Fin 3, e ∉ T i)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (U : Fin 3 → Finset (E × Fin 2)),
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
      (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) →
  (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) →
  ∃ T : Fin 3 → Finset E,
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) u v) ∧
    (∀ e : E, ∃ i : Fin 3, e ∉ T i) := by
intro V E _ _ _ _ endAt U hconn hdisj
refine ⟨fun i => (U i).image Prod.fst, ?_, ?_⟩
· intro i u v
  refine Relation.ReflTransGen.mono ?_ (hconn i u v)
  rintro a b ⟨t, htU, hends⟩
  exact ⟨t.1, Finset.mem_image_of_mem Prod.fst htU, hends⟩
· intro e
  by_contra hall
  push Not at hall
  choose x hxU hxe using fun i => Finset.mem_image.mp (hall i)
  have hjinj : Function.Injective (fun i : Fin 3 => (x i).2) := by
    intro i k hj
    have hx : x i = x k := Prod.ext ((hxe i).trans (hxe k).symm) hj
    by_contra hik
    exact Finset.disjoint_left.mp (hdisj i k hik) (hxU i) (hx ▸ hxU k)
  have hle := Fintype.card_le_of_injective _ hjinj
  norm_num at hle

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt U hconn hdisj ; refine ⟨fun i => (U i).image Prod.fst, ?_, ?_⟩ ; · intro i u v ;   refine Relation.ReflTransGen.mono ?_ (hconn i u v) ;   rintro a b ⟨t, htU, hends⟩ ;   exact ⟨t.1, Finset.mem_image_of_mem Prod.fst htU, hends⟩ ; · intro e ;   by_contra hall ;   push Not at hall ;   choose x hxU hxe using fun i => Finset.mem_image.mp (hall i) ;   have hjinj : Function.Injective (fun i : Fin 3 => (x i).2) := by ;     intro i k hj ;     have hx : x i = x k := Prod.ext ((hxe i).trans (hxe k).symm) hj ;     by_contra hik ;     exact Finset.disjoint_left.mp (hdisj i k hik) (hxU i) (hx ▸ hxU k) ;   have hle := Fintype.card_le_of_injective _ hjinj ;   norm_num at hle` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `6c72e8b17f97…` → `eb063501544c…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
