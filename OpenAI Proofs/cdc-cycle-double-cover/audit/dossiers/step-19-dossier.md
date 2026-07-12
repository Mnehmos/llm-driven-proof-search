# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow campaign step JK-B2: in a multigraph whose edge set T connects all vertices (connectivity encoded as Relation.ReflTransGen of the one-step T-adjacency relation - the connectivity convention for the whole Nash-Williams/Jaeger layer), every edge outside T has a fundamental cycle: an even edge set containing it whose other edges lie in T. Proof: by ReflTransGen induction build an F2 path certificate w : E -> ZMod 2 supported in T whose incidence parity at x is [u = x] + [v = x] (refl: zero certificate, char-2 collapses the endpoint terms; tail: add the step edge's indicator, telescoping the intermediate vertex in characteristic two); then for e outside T the weight w + indicator(e) taken along a path between e's own ends has even parity everywhere, its support is the fundamental cycle. Conclusion is verbatim the hypothesis of JK-B1 (problem 68e5b80e), so together: T connected implies an even superset of the complement of T. Pre-flighted clean on the pinned lean-checker (14.8s).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `0a521779-1dd0-4454-b62f-1a9978576729` | terminated (root_proved) | 1 | — | 2026-07-11T17:42:29 | 2026-07-11T17:44:17 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T) := by
intro V E _ _ _ _ endAt T hconn
have h2c : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
have hpath : ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v →
    ∃ w : E → ZMod 2,
      (∀ k : E, w k = 1 → k ∈ T) ∧
      (∀ x : V, (∑ k : E, ((if endAt k 0 = x then w k else 0) +
        (if endAt k 1 = x then w k else 0))) =
        (if u = x then (1 : ZMod 2) else 0) + (if v = x then (1 : ZMod 2) else 0)) := by
  intro u v h
  induction h with
  | refl =>
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro k hk
      have hk' : (0 : ZMod 2) = 1 := hk
      exact absurd hk' (by decide)
    · intro x
      show (∑ k : E, ((if endAt k 0 = x then (0 : ZMod 2) else 0) +
        (if endAt k 1 = x then (0 : ZMod 2) else 0))) =
        (if u = x then (1 : ZMod 2) else 0) + (if u = x then (1 : ZMod 2) else 0)
      rw [CharTwo.add_self_eq_zero]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [ite_self, ite_self, add_zero]
  | @tail b c hab hstep ih =>
    obtain ⟨w, hwT, hwpar⟩ := ih
    obtain ⟨t, htT, hor⟩ := hstep
    refine ⟨fun k => w k + (if k = t then 1 else 0), ?_, ?_⟩
    · intro k hk
      have hk' : w k + (if k = t then (1 : ZMod 2) else 0) = 1 := hk
      by_cases hkt : k = t
      · rw [hkt]; exact htT
      · rw [if_neg hkt, add_zero] at hk'
        exact hwT k hk'
    · intro x
      show (∑ k : E, ((if endAt k 0 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0) +
        (if endAt k 1 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0))) =
        (if u = x then (1 : ZMod 2) else 0) + (if c = x then (1 : ZMod 2) else 0)
      have hsplit : (∑ k : E, ((if endAt k 0 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0) +
          (if endAt k 1 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0))) =
          (∑ k : E, ((if endAt k 0 = x then w k else 0) +
            (if endAt k 1 = x then w k else 0))) +
          (∑ k : E, ((if endAt k 0 = x then (if k = t then (1 : ZMod 2) else 0) else 0) +
            (if endAt k 1 = x then (if k = t then (1 : ZMod 2) else 0) else 0))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases h0 : endAt k 0 = x <;> by_cases h1 : endAt k 1 = x
        · simp only [if_pos h0, if_pos h1]; ring
        · simp only [if_pos h0, if_neg h1]; ring
        · simp only [if_neg h0, if_pos h1]; ring
        · simp only [if_neg h0, if_neg h1]; ring
      have htinc : (∑ k : E, ((if endAt k 0 = x then (if k = t then (1 : ZMod 2) else 0) else 0) +
          (if endAt k 1 = x then (if k = t then (1 : ZMod 2) else 0) else 0))) =
          ((if endAt t 0 = x then (1 : ZMod 2) else 0) +
            (if endAt t 1 = x then (1 : ZMod 2) else 0)) := by
        refine (Finset.sum_eq_single t ?_ ?_).trans ?_
        · intro b2 hb2 hbt
          simp [hbt]
        · intro ht'
          exact absurd (Finset.mem_univ t) ht'
        · simp
      rw [hsplit, hwpar, htinc]
      rcases hor with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
        have harr : ∀ a b2 c2 : ZMod 2, (a + b2) + (b2 + c2) = a + c2 := by decide
        exact harr _ _ _
      · rw [h0, h1]
        have harr : ∀ a b2 c2 : ZMod 2, (a + b2) + (c2 + b2) = a + c2 := by decide
        exact harr _ _ _
intro e heT
obtain ⟨w, hwT, hwpar⟩ := hpath (endAt e 1) (endAt e 0) (hconn _ _)
have hwe0 : w e = 0 := by
  rcases h2c (w e) with h | h
  · exact h
  · exact absurd (hwT e h) heT
set W : E → ZMod 2 := fun k => w k + (if k = e then 1 else 0) with hW
refine ⟨Finset.univ.filter (fun k => W k = 1), ?_, ?_, ?_⟩
· intro x
  rw [Finset.sum_filter]
  have hB : ∀ k : E,
      (if W k = 1 then ((if endAt k 0 = x then (1 : ZMod 2) else 0) +
        (if endAt k 1 = x then (1 : ZMod 2) else 0)) else 0) =
      (if endAt k 0 = x then W k else 0) + (if endAt k 1 = x then W k else 0) := by
    intro k
    rcases h2c (W k) with h | h
    · rw [h, if_neg (by decide : ¬(0 : ZMod 2) = 1), ite_self, ite_self, add_zero]
    · rw [h, if_pos rfl]
  rw [Finset.sum_congr rfl fun k _ => hB k]
  have hsplit2 : (∑ k : E, ((if endAt k 0 = x then W k else 0) +
      (if endAt k 1 = x then W k else 0))) =
      (∑ k : E, ((if endAt k 0 = x then w k else 0) +
        (if endAt k 1 = x then w k else 0))) +
      (∑ k : E, ((if endAt k 0 = x then (if k = e then (1 : ZMod 2) else 0) else 0) +
        (if endAt k 1 = x then (if k = e then (1 : ZMod 2) else 0) else 0))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hW]
    by_cases h0 : endAt k 0 = x <;> by_cases h1 : endAt k 1 = x
    · simp only [if_pos h0, if_pos h1]; ring
    · simp only [if_pos h0, if_neg h1]; ring
    · simp only [if_neg h0, if_pos h1]; ring
    · simp only [if_neg h0, if_neg h1]; ring
  have heinc : (∑ k : E, ((if endAt k 0 = x then (if k = e then (1 : ZMod 2) else 0) else 0) +
      (if endAt k 1 = x then (if k = e then (1 : ZMod 2) else 0) else 0))) =
      ((if endAt e 0 = x then (1 : ZMod 2) else 0) +
        (if endAt e 1 = x then (1 : ZMod 2) else 0)) := by
    refine (Finset.sum_eq_single e ?_ ?_).trans ?_
    · intro b2 hb2 hbe
      simp [hbe]
    · intro he'
      exact absurd (Finset.mem_univ e) he'
    · simp
  rw [hsplit2, hwpar, heinc]
  have harr2 : ∀ a b2 : ZMod 2, (a + b2) + (b2 + a) = 0 := by decide
  exact harr2 _ _
· have hWe : W e = 1 := by
    simp [hW, hwe0]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hWe⟩
· intro k hk hke
  have hWk : W k = 1 := (Finset.mem_filter.mp hk).2
  simp only [hW] at hWk
  rw [if_neg hke, add_zero] at hWk
  exact hwT k hWk

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt T hconn ; have h2c : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide ; have hpath : ∀ u v : V, Relation.ReflTransGen ;     (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨ ;       (endAt t 0 = b ∧ endAt t 1 = a)) u v → ;     ∃ w : E → ZMod 2, ;       (∀ k : E, w k = 1 → k ∈ T) ∧ ;       (∀ x : V, (∑ k : E, ((if endAt k 0 = x then w k else 0) + ;         (if endAt k 1 = x then w k else 0))) = ;         (if u = x then (1 : ZMod 2) else 0) + (if v = x then (1 : ZMod 2) else 0)) := by ;   intro u v h ;   induction h with ;   \| refl => ;     refine ⟨fun _ => 0, ?_, ?_⟩ ;     · intro k hk ;       have hk' : (0 : ZMod 2) = 1 := hk ;       exact absurd hk' (by decide) ;     · intro x ;       show (∑ k : E, ((if endAt k 0 = x then (0 : ZMod 2) else 0) + ;         (if endAt k 1 = x then (0 : ZMod 2) else 0))) = ;         (if u = x then (1 : ZMod 2) else 0) + (if u = x then (1 : ZMod 2) else 0) ;       rw [CharTwo.add_self_eq_zero] ;       refine Finset.sum_eq_zero fun k _ => ?_ ;       rw [ite_self, ite_self, add_zero] ;   \| @tail b c hab hstep ih => ;     obtain ⟨w, hwT, hwpar⟩ := ih ;     obtain ⟨t, htT, hor⟩ := hstep ;     refine ⟨fun k => w k + (if k = t then 1 else 0), ?_, ?_⟩ ;     · intro k hk ;       have hk' : w k + (if k = t then (1 : ZMod 2) else 0) = 1 := hk ;       by_cases hkt : k = t ;       · rw [hkt]; exact htT ;       · rw [if_neg hkt, add_zero] at hk' ;         exact hwT k hk' ;     · intro x ;       show (∑ k : E, ((if endAt k 0 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0) + ;         (if endAt k 1 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0))) = ;         (if u = x then (1 : ZMod 2) else 0) + (if c = x then (1 : ZMod 2) else 0) ;       have hsplit : (∑ k : E, ((if endAt k 0 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0) + ;           (if endAt k 1 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0))) = ;           (∑ k : E, ((if endAt k 0 = x then w k else 0) + ;             (if endAt k 1 = x then w k else 0))) + ;           (∑ k : E, ((if endAt k 0 = x then (if k = t then (1 : ZMod 2) else 0) else 0) + ;             (if endAt k 1 = x then (if k = t then (1 : ZMod 2) else 0) else 0))) := by ;         rw [← Finset.sum_add_distrib] ;         refine Finset.sum_congr rfl fun k _ => ?_ ;         by_cases h0 : endAt k 0 = x <;> by_cases h1 : endAt k 1 = x ;         · simp only [if_pos h0, if_pos h1]; ring ;         · simp only [if_pos h0, if_neg h1]; ring ;         · simp only [if_neg h0, if_pos h1]; ring ;         · simp only [if_neg h0, if_neg h1]; ring ;       have htinc : (∑ k : E, ((if endAt k 0 = x then (if k = t then (1 : ZMod 2) else 0) else 0) + ;           (if endAt k 1 = x then (if k = t then (1 : ZMod 2) else 0) else 0))) = ;           ((if endAt t 0 = x then (1 : ZMod 2) else 0) + ;             (if endAt t 1 = x then (1 : ZMod 2) else 0)) := by ;         refine (Finset.sum_eq_single t ?_ ?_).trans ?_ ;         · intro b2 hb2 hbt ;           simp [hbt] ;         · intro ht' ;           exact absurd (Finset.mem_univ t) ht' ;         · simp ;       rw [hsplit, hwpar, htinc] ;       rcases hor with ⟨h0, h1⟩ \| ⟨h0, h1⟩ ;       · rw [h0, h1] ;         have harr : ∀ a b2 c2 : ZMod 2, (a + b2) + (b2 + c2) = a + c2 := by decide ;         exact harr _ _ _ ;       · rw [h0, h1] ;         have harr : ∀ a b2 c2 : ZMod 2, (a + b2) + (c2 + b2) = a + c2 := by decide ;         exact harr _ _ _ ; intro e heT ; obtain ⟨w, hwT, hwpar⟩ := hpath (endAt e 1) (endAt e 0) (hconn _ _) ; have hwe0 : w e = 0 := by ;   rcases h2c (w e) with h \| h ;   · exact h ;   · exact absurd (hwT e h) heT ; set W : E → ZMod 2 := fun k => w k + (if k = e then 1 else 0) with hW ; refine ⟨Finset.univ.filter (fun k => W k = 1), ?_, ?_, ?_⟩ ; · intro x ;   rw [Finset.sum_filter] ;   have hB : ∀ k : E, ;       (if W k = 1 then ((if endAt k 0 = x then (1 : ZMod 2) else 0) + ;         (if endAt k 1 = x then (1 : ZMod 2) else 0)) else 0) = ;       (if endAt k 0 = x then W k else 0) + (if endAt k 1 = x then W k else 0) := by ;     intro k ;     rcases h2c (W k) with h \| h ;     · rw [h, if_neg (by decide : ¬(0 : ZMod 2) = 1), ite_self, ite_self, add_zero] ;     · rw [h, if_pos rfl] ;   rw [Finset.sum_congr rfl fun k _ => hB k] ;   have hsplit2 : (∑ k : E, ((if endAt k 0 = x then W k else 0) + ;       (if endAt k 1 = x then W k else 0))) = ;       (∑ k : E, ((if endAt k 0 = x then w k else 0) + ;         (if endAt k 1 = x then w k else 0))) + ;       (∑ k : E, ((if endAt k 0 = x then (if k = e then (1 : ZMod 2) else 0) else 0) + ;         (if endAt k 1 = x then (if k = e then (1 : ZMod 2) else 0) else 0))) := by ;     rw [← Finset.sum_add_distrib] ;     refine Finset.sum_congr rfl fun k _ => ?_ ;     simp only [hW] ;     by_cases h0 : endAt k 0 = x <;> by_cases h1 : endAt k 1 = x ;     · simp only [if_pos h0, if_pos h1]; ring ;     · simp only [if_pos h0, if_neg h1]; ring ;     · simp only [if_neg h0, if_pos h1]; ring ;     · simp only [if_neg h0, if_neg h1]; ring ;   have heinc : (∑ k : E, ((if endAt k 0 = x then (if k = e then (1 : ZMod 2) else 0) else 0) + ;       (if endAt k 1 = x then (if k = e then (1 : ZMod 2) else 0) else 0))) = ;       ((if endAt e 0 = x then (1 : ZMod 2) else 0) + ;         (if endAt e 1 = x then (1 : ZMod 2) else 0)) := by ;     refine (Finset.sum_eq_single e ?_ ?_).trans ?_ ;     · intro b2 hb2 hbe ;       simp [hbe] ;     · intro he' ;       exact absurd (Finset.mem_univ e) he' ;     · simp ;   rw [hsplit2, hwpar, heinc] ;   have harr2 : ∀ a b2 : ZMod 2, (a + b2) + (b2 + a) = 0 := by decide ;   exact harr2 _ _ ; · have hWe : W e = 1 := by ;     simp [hW, hwe0] ;   exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hWe⟩ ; · intro k hk hke ;   have hWk : W k = 1 := (Finset.mem_filter.mp hk).2 ;   simp only [hW] at hWk ;   rw [if_neg hke, add_zero] at hWk ;   exact hwT k hWk` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `ae0b165bc6f0…` → `3964cca67e68…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
