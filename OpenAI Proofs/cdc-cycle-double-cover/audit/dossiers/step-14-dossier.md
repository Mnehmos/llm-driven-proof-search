# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper: a bridgeless loopless finite multigraph has no vertex of exactly one incident half-edge (mirrors CDCLean.degree_ne_one_of_bridgeless): if vertex v had a unique incident half-edge h, the singleton vertex set {v} would have edge cut exactly {h.1} (the forward inclusion because any crossing edge contributes an incident half-edge at v which must equal h; the reverse because h's other end differs from v by looplessness), contradicting bridgelessness (no cut of cardinality one, with crossing encoded decidably as the negated membership biconditional). Conclusion is verbatim the hypothesis of the rotation-existence step (problem abd3fd7f), completing the chain: bridgeless => rotation system => (with a flow-derived expansion cover) cycle double cover. Pre-flighted clean on the pinned lean-checker in 15s.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ∀ v : V, (Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v)).card ≠ 1`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ∀ v : V, (Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v)).card ≠ 1`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `fb3502ad-11b3-4848-8c5a-630f6bb5d0c0` | terminated (root_proved) | 1 | — | 2026-07-11T17:09:58 | 2026-07-11T17:11:08 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ∀ v : V, (Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v)).card ≠ 1`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ∀ v : V, (Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v)).card ≠ 1 := by
intro V E _ _ _ _ endAt hloop hbridge v hd
obtain ⟨h, hh⟩ := Finset.card_eq_one.mp hd
have hmem : ∀ x : E × Fin 2, endAt x.1 x.2 = v → x = h := by
  intro x hx
  have hx2 : x ∈ Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v) := by
    simp [hx]
  rw [hh] at hx2
  exact Finset.mem_singleton.mp hx2
have hhv : endAt h.1 h.2 = v := by
  have hself : h ∈ Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v) := by
    rw [hh]
    exact Finset.mem_singleton_self h
  simpa using hself
have hcut : (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ ({v} : Finset V)) ↔ (endAt e 1 ∈ ({v} : Finset V))))) = {h.1} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hk
    by_cases hk0 : endAt k 0 = v
    · exact congrArg Prod.fst (hmem (k, 0) hk0)
    · have hk1 : endAt k 1 = v := by
        by_contra hk1
        exact hk (by simp [hk0, hk1])
      exact congrArg Prod.fst (hmem (k, 1) hk1)
  · intro hke
    subst hke
    have hj2 : h.2 = 0 ∨ h.2 = 1 := by omega
    rcases hj2 with hj | hj
    · have h0v : endAt h.1 0 = v := by rw [← hj]; exact hhv
      have h1v : endAt h.1 1 ≠ v := by
        intro hz
        exact hloop h.1 (h0v.trans hz.symm)
      simp [h0v, h1v]
    · have h1v : endAt h.1 1 = v := by rw [← hj]; exact hhv
      have h0v : endAt h.1 0 ≠ v := by
        intro hz
        exact hloop h.1 (hz.trans h1v.symm)
      simp [h0v, h1v]
have hb := hbridge {v}
rw [hcut] at hb
exact hb (Finset.card_singleton h.1)

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt hloop hbridge v hd ; obtain ⟨h, hh⟩ := Finset.card_eq_one.mp hd ; have hmem : ∀ x : E × Fin 2, endAt x.1 x.2 = v → x = h := by ;   intro x hx ;   have hx2 : x ∈ Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v) := by ;     simp [hx] ;   rw [hh] at hx2 ;   exact Finset.mem_singleton.mp hx2 ; have hhv : endAt h.1 h.2 = v := by ;   have hself : h ∈ Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v) := by ;     rw [hh] ;     exact Finset.mem_singleton_self h ;   simpa using hself ; have hcut : (Finset.univ.filter ;     (fun e => ¬((endAt e 0 ∈ ({v} : Finset V)) ↔ (endAt e 1 ∈ ({v} : Finset V))))) = {h.1} := by ;   ext k ;   simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] ;   constructor ;   · intro hk ;     by_cases hk0 : endAt k 0 = v ;     · exact congrArg Prod.fst (hmem (k, 0) hk0) ;     · have hk1 : endAt k 1 = v := by ;         by_contra hk1 ;         exact hk (by simp [hk0, hk1]) ;       exact congrArg Prod.fst (hmem (k, 1) hk1) ;   · intro hke ;     subst hke ;     have hj2 : h.2 = 0 ∨ h.2 = 1 := by omega ;     rcases hj2 with hj \| hj ;     · have h0v : endAt h.1 0 = v := by rw [← hj]; exact hhv ;       have h1v : endAt h.1 1 ≠ v := by ;         intro hz ;         exact hloop h.1 (h0v.trans hz.symm) ;       simp [h0v, h1v] ;     · have h1v : endAt h.1 1 = v := by rw [← hj]; exact hhv ;       have h0v : endAt h.1 0 ≠ v := by ;         intro hz ;         exact hloop h.1 (hz.trans h1v.symm) ;       simp [h0v, h1v] ; have hb := hbridge {v} ; rw [hcut] at hb ; exact hb (Finset.card_singleton h.1)` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `d5f01235b173…` → `63169d687752…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
