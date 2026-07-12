# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper cycle-decomposition step (mirrors CDCLean.decompose_even_edge_set): in a finite loopless multigraph (endAt : E -> Fin 2 -> V with distinct edge ends), every even edge set F (every vertex has mod-2 incidence sum zero, both edge ends counted) decomposes into a list of multigraph cycles - nonempty inclusion-minimal even edge sets, which for loopless multigraphs are exactly the circuits - such that every edge of F lies in exactly one list entry and every edge outside F in none. The displayed filter-length equation records edge multiplicities exactly. Reference proof: Finset strong induction; if F is itself minimal it is a single cycle, otherwise split off a proper nonempty even subset D and recurse on D and F \ D (the sdiff stays even in characteristic two).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  ∀ F : Finset E,
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
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  ∀ F : Finset E,
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
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `82fc190d-0f34-48bf-b4f3-f65641ebc129` | terminated (root_proved) | 1 | — | 2026-07-11T16:06:47 | 2026-07-11T16:08:01 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  ∀ F : Finset E,
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
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  ∀ F : Finset E,
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
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0) := by
intro V E _ _ _ _ endAt hloop F
refine Finset.strongInductionOn F ?_
intro F ih hF
by_cases hne : F.Nonempty
· by_cases hmin : ∀ D : Finset E, D.Nonempty → D ⊆ F →
      (∀ v : V,
        (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) → D = F
  · refine ⟨[F], ?_, ?_⟩
    · intro C hC
      rw [List.mem_singleton] at hC
      subst hC
      exact ⟨hne, hF, hmin⟩
    · intro e
      by_cases he : e ∈ F <;> simp [he]
  · push_neg at hmin
    obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin
    have hsdiff : ∀ v : V,
        (∑ e ∈ F \ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0 := by
      intro v
      have hsplit := Finset.sum_sdiff (f := fun e =>
        (if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0)) hDF
      rw [hDeven v, hF v] at hsplit
      simpa using hsplit
    have hDssub : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDF, hDproper⟩
    have hRssub : F \ D ⊂ F := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro heq
      obtain ⟨e, heD⟩ := hDne
      have hmem : e ∈ F \ D := by
        rw [heq]
        exact hDF heD
      simp [heD] at hmem
    obtain ⟨LD, hLDprops, hLD⟩ := ih D hDssub hDeven
    obtain ⟨LR, hLRprops, hLR⟩ := ih (F \ D) hRssub hsdiff
    refine ⟨LD ++ LR, ?_, ?_⟩
    · intro C hC
      rcases List.mem_append.mp hC with h | h
      · exact hLDprops C h
      · exact hLRprops C h
    · intro e
      rw [List.filter_append, List.length_append, hLD e, hLR e]
      by_cases heD : e ∈ D
      · have heF : e ∈ F := hDF heD
        simp [Finset.mem_sdiff, heD, heF]
      · by_cases heF : e ∈ F <;> simp [Finset.mem_sdiff, heD, heF]
· have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  subst hzero
  refine ⟨[], ?_, ?_⟩
  · intro C hC
    simp at hC
  · intro e
    simp

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt hloop F ; refine Finset.strongInductionOn F ?_ ; intro F ih hF ; by_cases hne : F.Nonempty ; · by_cases hmin : ∀ D : Finset E, D.Nonempty → D ⊆ F → ;       (∀ v : V, ;         (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) + ;           (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) → D = F ;   · refine ⟨[F], ?_, ?_⟩ ;     · intro C hC ;       rw [List.mem_singleton] at hC ;       subst hC ;       exact ⟨hne, hF, hmin⟩ ;     · intro e ;       by_cases he : e ∈ F <;> simp [he] ;   · push_neg at hmin ;     obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin ;     have hsdiff : ∀ v : V, ;         (∑ e ∈ F \ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) + ;           (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0 := by ;       intro v ;       have hsplit := Finset.sum_sdiff (f := fun e => ;         (if endAt e 0 = v then (1 : ZMod 2) else 0) + ;           (if endAt e 1 = v then (1 : ZMod 2) else 0)) hDF ;       rw [hDeven v, hF v] at hsplit ;       simpa using hsplit ;     have hDssub : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDF, hDproper⟩ ;     have hRssub : F \ D ⊂ F := by ;       apply Finset.ssubset_iff_subset_ne.mpr ;       refine ⟨Finset.sdiff_subset, ?_⟩ ;       intro heq ;       obtain ⟨e, heD⟩ := hDne ;       have hmem : e ∈ F \ D := by ;         rw [heq] ;         exact hDF heD ;       simp [heD] at hmem ;     obtain ⟨LD, hLDprops, hLD⟩ := ih D hDssub hDeven ;     obtain ⟨LR, hLRprops, hLR⟩ := ih (F \ D) hRssub hsdiff ;     refine ⟨LD ++ LR, ?_, ?_⟩ ;     · intro C hC ;       rcases List.mem_append.mp hC with h \| h ;       · exact hLDprops C h ;       · exact hLRprops C h ;     · intro e ;       rw [List.filter_append, List.length_append, hLD e, hLR e] ;       by_cases heD : e ∈ D ;       · have heF : e ∈ F := hDF heD ;         simp [Finset.mem_sdiff, heD, heF] ;       · by_cases heF : e ∈ F <;> simp [Finset.mem_sdiff, heD, heF] ; · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne ;   subst hzero ;   refine ⟨[], ?_, ?_⟩ ;   · intro C hC ;     simp at hC ;   · intro e ;     simp` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `b5da61389091…` → `39b6d06ef4c6…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
