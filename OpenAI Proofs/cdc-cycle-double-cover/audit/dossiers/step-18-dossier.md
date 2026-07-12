# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow campaign step JK-B1 (char-2 simplification of CDCLean.exists_even_superset_compl_of_spanningTree): if every edge outside T has a fundamental cycle - an even edge set containing it whose other edges all lie in T - then the mod-2 sum of these cycles is an even edge set containing the whole complement of T. The reference proof routes through integer circulations; in characteristic two the even-set property is linear in indicator functions, so the parity-weight w(k) = number of fundamental cycles through k mod 2 defines the set directly: evenness by exchanging the double sum and using each cycle's evenness, and membership because a non-tree edge e lies only in its own fundamental cycle. The remaining input (fundamental cycles exist for spanning-tree complements, via walk induction over Relation.ReflTransGen connectivity) is deferred to step JK-B2. Pre-flighted clean on the pinned lean-checker (14.4s, one beta-reduction fix).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) →
  ∃ F : Finset E,
    (∀ v : V, (∑ k ∈ F, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, e ∉ T → e ∈ F)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) →
  ∃ F : Finset E,
    (∀ v : V, (∑ k ∈ F, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, e ∉ T → e ∈ F)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `35479379-9829-498c-af26-ab45e65fe4d4` | terminated (root_proved) | 1 | — | 2026-07-11T17:35:49 | 2026-07-11T17:37:05 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) →
  ∃ F : Finset E,
    (∀ v : V, (∑ k ∈ F, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, e ∉ T → e ∈ F)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) →
  ∃ F : Finset E,
    (∀ v : V, (∑ k ∈ F, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, e ∉ T → e ∈ F) := by
intro V E _ _ _ _ endAt T hcyc
have hcyc' : ∀ e : E, ∃ C : Finset E, e ∉ T →
    ((∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) := by
  intro e
  by_cases he : e ∈ T
  · exact ⟨∅, fun h => absurd he h⟩
  · obtain ⟨C, hCp⟩ := hcyc e he
    exact ⟨C, fun _ => hCp⟩
choose C hC using hcyc'
set w : E → ZMod 2 := fun k =>
  ∑ e' ∈ Finset.univ.filter (fun x => x ∉ T), (if k ∈ C e' then (1 : ZMod 2) else 0)
  with hw
have h2c : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
refine ⟨Finset.univ.filter (fun k => w k = 1), ?_, ?_⟩
· intro v
  rw [Finset.sum_filter]
  have hB : ∀ k : E,
      (if w k = 1 then ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt k 1 = v then (1 : ZMod 2) else 0)) else 0) =
      w k * ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt k 1 = v then (1 : ZMod 2) else 0)) := by
    intro k
    rcases h2c (w k) with h | h
    · rw [h, if_neg (by decide : ¬(0 : ZMod 2) = 1), zero_mul]
    · rw [h, if_pos rfl, one_mul]
  rw [Finset.sum_congr rfl fun k _ => hB k]
  have hpt : ∀ k : E,
      w k * ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt k 1 = v then (1 : ZMod 2) else 0)) =
      ∑ e' ∈ Finset.univ.filter (fun x => x ∉ T),
        (if k ∈ C e' then (1 : ZMod 2) else 0) *
          ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
            (if endAt k 1 = v then (1 : ZMod 2) else 0)) := by
    intro k
    rw [hw]
    exact Finset.sum_mul _ _ _
  rw [Finset.sum_congr rfl fun k _ => hpt k]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e' he' => ?_
  have heT : e' ∉ T := (Finset.mem_filter.mp he').2
  obtain ⟨hCe_even, hCe_mem, hCe_sub⟩ := hC e' heT
  have hpt2 : ∀ k : E,
      (if k ∈ C e' then (1 : ZMod 2) else 0) *
        ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
          (if endAt k 1 = v then (1 : ZMod 2) else 0)) =
      (if k ∈ C e' then ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt k 1 = v then (1 : ZMod 2) else 0)) else 0) := by
    intro k
    by_cases hk : k ∈ C e' <;> simp [hk]
  rw [Finset.sum_congr rfl fun k _ => hpt2 k]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact hCe_even v
· intro e heT
  have hwe : w e = 1 := by
    simp only [hw]
    have h1 : (∑ e' ∈ Finset.univ.filter (fun x => x ∉ T),
        (if e ∈ C e' then (1 : ZMod 2) else 0)) =
        (if e ∈ C e then (1 : ZMod 2) else 0) := by
      refine Finset.sum_eq_single e ?_ ?_
      · intro b hb hbe
        have hbT : b ∉ T := (Finset.mem_filter.mp hb).2
        rw [if_neg]
        intro hmem
        exact heT ((hC b hbT).2.2 e hmem (Ne.symm hbe))
      · intro hnot
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ e, heT⟩) hnot
    rw [h1, if_pos (hC e heT).2.1]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hwe⟩

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt T hcyc ; have hcyc' : ∀ e : E, ∃ C : Finset E, e ∉ T → ;     ((∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) + ;       (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧ ;     e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) := by ;   intro e ;   by_cases he : e ∈ T ;   · exact ⟨∅, fun h => absurd he h⟩ ;   · obtain ⟨C, hCp⟩ := hcyc e he ;     exact ⟨C, fun _ => hCp⟩ ; choose C hC using hcyc' ; set w : E → ZMod 2 := fun k => ;   ∑ e' ∈ Finset.univ.filter (fun x => x ∉ T), (if k ∈ C e' then (1 : ZMod 2) else 0) ;   with hw ; have h2c : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide ; refine ⟨Finset.univ.filter (fun k => w k = 1), ?_, ?_⟩ ; · intro v ;   rw [Finset.sum_filter] ;   have hB : ∀ k : E, ;       (if w k = 1 then ((if endAt k 0 = v then (1 : ZMod 2) else 0) + ;         (if endAt k 1 = v then (1 : ZMod 2) else 0)) else 0) = ;       w k * ((if endAt k 0 = v then (1 : ZMod 2) else 0) + ;         (if endAt k 1 = v then (1 : ZMod 2) else 0)) := by ;     intro k ;     rcases h2c (w k) with h \| h ;     · rw [h, if_neg (by decide : ¬(0 : ZMod 2) = 1), zero_mul] ;     · rw [h, if_pos rfl, one_mul] ;   rw [Finset.sum_congr rfl fun k _ => hB k] ;   have hpt : ∀ k : E, ;       w k * ((if endAt k 0 = v then (1 : ZMod 2) else 0) + ;         (if endAt k 1 = v then (1 : ZMod 2) else 0)) = ;       ∑ e' ∈ Finset.univ.filter (fun x => x ∉ T), ;         (if k ∈ C e' then (1 : ZMod 2) else 0) * ;           ((if endAt k 0 = v then (1 : ZMod 2) else 0) + ;             (if endAt k 1 = v then (1 : ZMod 2) else 0)) := by ;     intro k ;     rw [hw] ;     exact Finset.sum_mul _ _ _ ;   rw [Finset.sum_congr rfl fun k _ => hpt k] ;   rw [Finset.sum_comm] ;   refine Finset.sum_eq_zero fun e' he' => ?_ ;   have heT : e' ∉ T := (Finset.mem_filter.mp he').2 ;   obtain ⟨hCe_even, hCe_mem, hCe_sub⟩ := hC e' heT ;   have hpt2 : ∀ k : E, ;       (if k ∈ C e' then (1 : ZMod 2) else 0) * ;         ((if endAt k 0 = v then (1 : ZMod 2) else 0) + ;           (if endAt k 1 = v then (1 : ZMod 2) else 0)) = ;       (if k ∈ C e' then ((if endAt k 0 = v then (1 : ZMod 2) else 0) + ;         (if endAt k 1 = v then (1 : ZMod 2) else 0)) else 0) := by ;     intro k ;     by_cases hk : k ∈ C e' <;> simp [hk] ;   rw [Finset.sum_congr rfl fun k _ => hpt2 k] ;   rw [Finset.sum_ite_mem, Finset.univ_inter] ;   exact hCe_even v ; · intro e heT ;   have hwe : w e = 1 := by ;     simp only [hw] ;     have h1 : (∑ e' ∈ Finset.univ.filter (fun x => x ∉ T), ;         (if e ∈ C e' then (1 : ZMod 2) else 0)) = ;         (if e ∈ C e then (1 : ZMod 2) else 0) := by ;       refine Finset.sum_eq_single e ?_ ?_ ;       · intro b hb hbe ;         have hbT : b ∉ T := (Finset.mem_filter.mp hb).2 ;         rw [if_neg] ;         intro hmem ;         exact heT ((hC b hbT).2.2 e hmem (Ne.symm hbe)) ;       · intro hnot ;         exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ e, heT⟩) hnot ;     rw [h1, if_pos (hC e heT).2.1] ;   exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hwe⟩` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `edeac2705cdb…` → `fe337434b8b5…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
