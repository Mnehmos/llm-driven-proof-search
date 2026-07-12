# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Nash-Williams tree-packing campaign step NW-2 (mirrors CDCLean.connects_of_internal_of_quotient_connects, NashWilliams.lean 884-958, in the classifier encoding): if an edge set S of a finite multigraph has (a) every fiber of a classifier c : V -> V internally S-connected (paths whose every step stays inside the fiber of the endpoints, encoded by conjoining c a = c u and c b = c u onto the step relation) and (b) the quotient by c is S-connected (walk steps either stay within a class, c a = c b, or jump along an edge of S whose end-classes are the classes of a and b), then S connects all of V outright. Proof: head induction on the quotient walk; class-internal steps embed by ReflTransGen.mono; a crossing step through edge t is replaced by fiber-internal path to the matching end of t, the edge step itself, and a fiber-internal path from the other end. This is the connectivity glue consumed by the campaign's final assembly, whose partition classes will be built internally connected by construction. Pre-flighted clean first try on the pinned lean-checker (~15s).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `5272c958-f18d-412b-84a2-86150c9ee396` | terminated (root_proved) | 1 | — | 2026-07-11T21:07:20 | 2026-07-11T21:08:29 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v := by
intro V E _ _ _ _ endAt S c hint hquot u v
have hemb : ∀ w x : V, c w = c x → Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) w x := by
  intro w x hwx
  refine Relation.ReflTransGen.mono ?_ (hint w x hwx)
  rintro a b ⟨-, -, ht⟩
  exact ht
refine Relation.ReflTransGen.head_induction_on (hquot u v) ?_ ?_
· exact Relation.ReflTransGen.refl
· rintro a b hab hbv ih
  rcases hab with hcab | ⟨t, htS, hends⟩
  · exact (hemb a b hcab).trans ih
  · rcases hends with ⟨h0a, h1b⟩ | ⟨h0b, h1a⟩
    · exact ((hemb a (endAt t 0) h0a.symm).tail ⟨t, htS, Or.inl ⟨rfl, rfl⟩⟩).trans
        ((hemb (endAt t 1) b h1b).trans ih)
    · exact ((hemb a (endAt t 1) h1a.symm).tail ⟨t, htS, Or.inr ⟨rfl, rfl⟩⟩).trans
        ((hemb (endAt t 0) b h0b).trans ih)

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt S c hint hquot u v ; have hemb : ∀ w x : V, c w = c x → Relation.ReflTransGen ;     (fun a b => ∃ t ∈ S, ;       (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) w x := by ;   intro w x hwx ;   refine Relation.ReflTransGen.mono ?_ (hint w x hwx) ;   rintro a b ⟨-, -, ht⟩ ;   exact ht ; refine Relation.ReflTransGen.head_induction_on (hquot u v) ?_ ?_ ; · exact Relation.ReflTransGen.refl ; · rintro a b hab hbv ih ;   rcases hab with hcab \| ⟨t, htS, hends⟩ ;   · exact (hemb a b hcab).trans ih ;   · rcases hends with ⟨h0a, h1b⟩ \| ⟨h0b, h1a⟩ ;     · exact ((hemb a (endAt t 0) h0a.symm).tail ⟨t, htS, Or.inl ⟨rfl, rfl⟩⟩).trans ;         ((hemb (endAt t 1) b h1b).trans ih) ;     · exact ((hemb a (endAt t 1) h1a.symm).tail ⟨t, htS, Or.inr ⟨rfl, rfl⟩⟩).trans ;         ((hemb (endAt t 0) b h0b).trans ih)` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `28925f7c5c63…` → `f3cf73c47df1…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
