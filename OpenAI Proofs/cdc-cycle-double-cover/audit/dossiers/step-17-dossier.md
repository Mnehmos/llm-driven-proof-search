# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow campaign step JK-A (mirrors CDCLean.nowhereZeroGammaFlow_of_evenCover): three even edge sets of a finite multigraph that jointly cover every edge define a nowhere-zero F2^3-valued flow: coordinate i of the flow at edge e is the indicator of e in the i-th set. Nowhere-zero because every edge lies in some set; conservation per coordinate (unsigned char-2 form, both ends counted) reduces to the evenness of the corresponding set by commuting the indicator with the incidence indicators. First step of the Jaeger-Kilpatrick campaign: it remains to produce three even sets covering the edges (from spanning-tree complements via tree packing) and to convert this ends-form conservation to the localized expansion form consumed by step 15. Pre-flighted clean first try on the pinned lean-checker (14.5s).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (F : Fin 3 → Finset E),
  (∀ (i : Fin 3) (v : V),
    (∑ e ∈ F i, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
      (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
  (∀ e : E, ∃ i : Fin 3, e ∈ F i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (F : Fin 3 → Finset E),
  (∀ (i : Fin 3) (v : V),
    (∑ e ∈ F i, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
      (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
  (∀ e : E, ∃ i : Fin 3, e ∈ F i) →
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
| `045a2345-7bc2-4469-8784-179d6870e554` | terminated (root_proved) | 1 | — | 2026-07-11T17:30:14 | 2026-07-11T17:31:18 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (F : Fin 3 → Finset E),
  (∀ (i : Fin 3) (v : V),
    (∑ e ∈ F i, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
      (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
  (∀ e : E, ∃ i : Fin 3, e ∈ F i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (F : Fin 3 → Finset E),
  (∀ (i : Fin 3) (v : V),
    (∑ e ∈ F i, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
      (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
  (∀ e : E, ∃ i : Fin 3, e ∈ F i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0) := by
intro V E _ _ _ _ endAt F hEven hCover
refine ⟨fun e i => if e ∈ F i then 1 else 0, ?_, ?_⟩
· intro e h0
  obtain ⟨i, hi⟩ := hCover e
  have hc := congrFun h0 i
  simp [hi] at hc
· intro v i
  have hsum : ∀ (j : Fin 2),
      (∑ e : E, (if endAt e j = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0)) =
      ∑ e ∈ F i, (if endAt e j = v then (1 : ZMod 2) else 0) := by
    intro j
    have hcomm : ∀ e : E,
        (if endAt e j = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0) =
        (if e ∈ F i then (if endAt e j = v then (1 : ZMod 2) else 0) else 0) := by
      intro e
      by_cases he : e ∈ F i <;> by_cases hv : endAt e j = v <;> simp [he, hv]
    rw [Finset.sum_congr rfl fun e _ => hcomm e]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  show (∑ e : E, ((if endAt e 0 = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0) +
    (if endAt e 1 = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0))) = 0
  rw [Finset.sum_add_distrib, hsum 0, hsum 1, ← Finset.sum_add_distrib]
  exact hEven i v

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt F hEven hCover ; refine ⟨fun e i => if e ∈ F i then 1 else 0, ?_, ?_⟩ ; · intro e h0 ;   obtain ⟨i, hi⟩ := hCover e ;   have hc := congrFun h0 i ;   simp [hi] at hc ; · intro v i ;   have hsum : ∀ (j : Fin 2), ;       (∑ e : E, (if endAt e j = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0)) = ;       ∑ e ∈ F i, (if endAt e j = v then (1 : ZMod 2) else 0) := by ;     intro j ;     have hcomm : ∀ e : E, ;         (if endAt e j = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0) = ;         (if e ∈ F i then (if endAt e j = v then (1 : ZMod 2) else 0) else 0) := by ;       intro e ;       by_cases he : e ∈ F i <;> by_cases hv : endAt e j = v <;> simp [he, hv] ;     rw [Finset.sum_congr rfl fun e _ => hcomm e] ;     rw [Finset.sum_ite_mem, Finset.univ_inter] ;   show (∑ e : E, ((if endAt e 0 = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0) + ;     (if endAt e 1 = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0))) = 0 ;   rw [Finset.sum_add_distrib, hsum 0, hsum 1, ← Finset.sum_add_distrib] ;   exact hEven i v` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `00003f0b9800…` → `03b8687bb8d3…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
