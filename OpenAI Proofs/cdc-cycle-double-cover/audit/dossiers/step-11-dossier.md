# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper: the toCycleDoubleCover assembly isolated (mirrors CDCLean.IndexedEvenDoubleCover.toCycleDoubleCover with its two inputs as hypotheses): for a finite loopless multigraph, IF every even edge set decomposes exactly into cycles (the conclusion of problem d269b928, kernel-verified) AND there is an F2^3-indexed exact even double cover in the ends sense (the conclusion of the ends-form cover problem 2667a666), THEN the graph has a cycle double cover: a list of cycles with every edge in exactly two entries. Proof: choose a decomposition of each of the eight supports, concatenate with flatMap over Finset.univ.toList, and account multiplicities via a list-induction filter-length lemma, List.map_congr_left, Finset.sum_toList and Finset.card_filter. Hypothesis-chaining is forced by the verifier's 60-second wall-clock cap per invocation, which rules out inlining the strong-induction decomposition here.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ F : Finset E,
    (∀ v : V,
      (∑ e ∈ F, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    ∃ L : List (Finset E),
      (∀ C ∈ L, C.Nonempty ∧
        (∀ v : V,
          (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
        (∀ D : Finset E, D.Nonempty → D ⊆ C →
          (∀ v : V,
            (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
              (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
          D = C)) ∧
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)) →
  (∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E,
      (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∃ L : List (Finset E),
    (∀ C ∈ L, C.Nonempty ∧
      (∀ v : V,
        (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ D : Finset E, D.Nonempty → D ⊆ C →
        (∀ v : V,
          (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
        D = C)) ∧
    (∀ e : E, (L.filter fun C => e ∈ C).length = 2)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ F : Finset E,
    (∀ v : V,
      (∑ e ∈ F, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    ∃ L : List (Finset E),
      (∀ C ∈ L, C.Nonempty ∧
        (∀ v : V,
          (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
        (∀ D : Finset E, D.Nonempty → D ⊆ C →
          (∀ v : V,
            (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
              (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
          D = C)) ∧
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)) →
  (∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E,
      (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∃ L : List (Finset E),
    (∀ C ∈ L, C.Nonempty ∧
      (∀ v : V,
        (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ D : Finset E, D.Nonempty → D ⊆ C →
        (∀ v : V,
          (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
        D = C)) ∧
    (∀ e : E, (L.filter fun C => e ∈ C).length = 2)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `c28d8df1-780e-4bd9-8018-34d4952c0f9d` | terminated (root_proved) | 3 | — | 2026-07-11T16:24:48 | 2026-07-11T16:42:54 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ F : Finset E,
    (∀ v : V,
      (∑ e ∈ F, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    ∃ L : List (Finset E),
      (∀ C ∈ L, C.Nonempty ∧
        (∀ v : V,
          (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
        (∀ D : Finset E, D.Nonempty → D ⊆ C →
          (∀ v : V,
            (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
              (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
          D = C)) ∧
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)) →
  (∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E,
      (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∃ L : List (Finset E),
    (∀ C ∈ L, C.Nonempty ∧
      (∀ v : V,
        (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ D : Finset E, D.Nonempty → D ⊆ C →
        (∀ v : V,
          (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
        D = C)) ∧
    (∀ e : E, (L.filter fun C => e ∈ C).length = 2)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ F : Finset E,
    (∀ v : V,
      (∑ e ∈ F, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    ∃ L : List (Finset E),
      (∀ C ∈ L, C.Nonempty ∧
        (∀ v : V,
          (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
        (∀ D : Finset E, D.Nonempty → D ⊆ C →
          (∀ v : V,
            (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
              (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
          D = C)) ∧
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)) →
  (∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E,
      (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∃ L : List (Finset E),
    (∀ C ∈ L, C.Nonempty ∧
      (∀ v : V,
        (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ D : Finset E, D.Nonempty → D ⊆ C →
        (∀ v : V,
          (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
        D = C)) ∧
    (∀ e : E, (L.filter fun C => e ∈ C).length = 2) := by
intro V E _ _ _ _ endAt hloop hdecomp hcover
obtain ⟨member, hEven, hTwo⟩ := hcover
choose pieces hp using fun s : Fin 3 → ZMod 2 =>
  hdecomp (Finset.univ.filter fun e => member s e = 1) (hEven s)
refine ⟨(Finset.univ : Finset (Fin 3 → ZMod 2)).toList.flatMap pieces, ?_, ?_⟩
· intro C hC
  rw [List.mem_flatMap] at hC
  obtain ⟨s, hs, hCs⟩ := hC
  exact (hp s).1 C hCs
· intro e
  have hflat : ∀ xs : List (Fin 3 → ZMod 2),
      ((xs.flatMap pieces).filter fun C => e ∈ C).length =
        (xs.map fun s => ((pieces s).filter fun C => e ∈ C).length).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp [List.flatMap_cons, List.filter_append, ih]
  rw [hflat]
  have hmap : ((Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map
      fun s => ((pieces s).filter fun C => e ∈ C).length) =
      (Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map
        fun s => if member s e = 1 then 1 else 0 := by
    refine List.map_congr_left fun s _ => ?_
    rw [(hp s).2 e]
    by_cases h : member s e = 1
    · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩), if_pos h]
    · rw [if_neg (fun hmem : e ∈ Finset.univ.filter (fun e' => member s e' = 1) =>
        h (Finset.mem_filter.mp hmem).2), if_neg h]
  rw [hmap, Finset.sum_map_toList, ← Finset.card_filter]
  exact hTwo e

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt hloop hdecomp hcover ; obtain ⟨member, hEven, hTwo⟩ := hcover ; choose pieces hp using fun s : Fin 3 → ZMod 2 => ;   hdecomp (Finset.univ.filter fun e => member s e = 1) (hEven s) ; refine ⟨(Finset.univ : Finset (Fin 3 → ZMod 2)).toList.flatMap pieces, ?_, ?_⟩ ; · intro C hC ;   rw [List.mem_flatMap] at hC ;   obtain ⟨s, hs, hCs⟩ := hC ;   exact (hp s).1 C hCs ; · intro e ;   have hflat : ∀ xs : List (Fin 3 → ZMod 2), ;       ((xs.flatMap pieces).filter fun C => e ∈ C).length = ;         (xs.map fun s => ((pieces s).filter fun C => e ∈ C).length).sum := by ;     intro xs ;     induction xs with ;     \| nil => simp ;     \| cons x xs ih => simp [List.flatMap_cons, List.filter_append, ih] ;   rw [hflat] ;   have hmap : ((Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map ;       fun s => ((pieces s).filter fun C => e ∈ C).length) = ;       (Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map ;         fun s => if member s e = 1 then 1 else 0 := by ;     refine List.map_congr_left fun s _ => ?_ ;     rw [(hp s).2 e] ;     by_cases h : member s e = 1 ;     · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩), if_pos h] ;     · rw [if_neg (fun hmem => h (Finset.mem_filter.mp hmem).2), if_neg h] ;   rw [hmap, Finset.sum_toList, ← Finset.card_filter] ;   exact hTwo e` | ❌ kernel_fail |
| 3 | `root_theorem` | solve | `intro V E _ _ _ _ endAt hloop hdecomp hcover ; obtain ⟨member, hEven, hTwo⟩ := hcover ; choose pieces hp using fun s : Fin 3 → ZMod 2 => ;   hdecomp (Finset.univ.filter fun e => member s e = 1) (hEven s) ; refine ⟨(Finset.univ : Finset (Fin 3 → ZMod 2)).toList.flatMap pieces, ?_, ?_⟩ ; · intro C hC ;   rw [List.mem_flatMap] at hC ;   obtain ⟨s, hs, hCs⟩ := hC ;   exact (hp s).1 C hCs ; · intro e ;   have hflat : ∀ xs : List (Fin 3 → ZMod 2), ;       ((xs.flatMap pieces).filter fun C => e ∈ C).length = ;         (xs.map fun s => ((pieces s).filter fun C => e ∈ C).length).sum := by ;     intro xs ;     induction xs with ;     \| nil => simp ;     \| cons x xs ih => simp [List.flatMap_cons, List.filter_append, ih] ;   rw [hflat] ;   have hmap : ((Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map ;       fun s => ((pieces s).filter fun C => e ∈ C).length) = ;       (Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map ;         fun s => if member s e = 1 then 1 else 0 := by ;     refine List.map_congr_left fun s _ => ?_ ;     rw [(hp s).2 e] ;     by_cases h : member s e = 1 ;     · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩), if_pos h] ;     · rw [if_neg (fun hmem => h (Finset.mem_filter.mp hmem).2), if_neg h] ;   rw [hmap, Finset.sum_toList, ← Finset.card_filter] ;   exact hTwo e` | ❌ kernel_fail |
| 4 | `root_theorem` | solve | `intro V E _ _ _ _ endAt hloop hdecomp hcover ; obtain ⟨member, hEven, hTwo⟩ := hcover ; choose pieces hp using fun s : Fin 3 → ZMod 2 => ;   hdecomp (Finset.univ.filter fun e => member s e = 1) (hEven s) ; refine ⟨(Finset.univ : Finset (Fin 3 → ZMod 2)).toList.flatMap pieces, ?_, ?_⟩ ; · intro C hC ;   rw [List.mem_flatMap] at hC ;   obtain ⟨s, hs, hCs⟩ := hC ;   exact (hp s).1 C hCs ; · intro e ;   have hflat : ∀ xs : List (Fin 3 → ZMod 2), ;       ((xs.flatMap pieces).filter fun C => e ∈ C).length = ;         (xs.map fun s => ((pieces s).filter fun C => e ∈ C).length).sum := by ;     intro xs ;     induction xs with ;     \| nil => simp ;     \| cons x xs ih => simp [List.flatMap_cons, List.filter_append, ih] ;   rw [hflat] ;   have hmap : ((Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map ;       fun s => ((pieces s).filter fun C => e ∈ C).length) = ;       (Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map ;         fun s => if member s e = 1 then 1 else 0 := by ;     refine List.map_congr_left fun s _ => ?_ ;     rw [(hp s).2 e] ;     by_cases h : member s e = 1 ;     · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩), if_pos h] ;     · rw [if_neg (fun hmem : e ∈ Finset.univ.filter (fun e' => member s e' = 1) => ;         h (Finset.mem_filter.mp hmem).2), if_neg h] ;   rw [hmap, Finset.sum_map_toList, ← Finset.card_filter] ;   exact hTwo e` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

5 hash-chained trajectory events, `303d7240d690…` → `7a6b4da44c5f…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
