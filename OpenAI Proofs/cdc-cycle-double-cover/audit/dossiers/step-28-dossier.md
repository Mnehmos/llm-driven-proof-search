# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger-Kilpatrick 8-flow, contraction reduction step JK-E-1 (the char-2 core of CDCLean.nowhereZeroGammaFlow_of_contractEdge_of_twoCut, JaegerKilpatrick.lean 686-793): conservation completes across a 2-edge cut. Let endAt : E -> Fin 2 -> V be a finite multigraph and phi : E -> Gamma (= Fin 3 -> ZMod 2) an edge function such that (i) the cut of the vertex set S -- the edges e with endAt e 0 in S not-iff endAt e 1 in S -- is exactly {e1, e2} with e1 <> e2, (ii) phi takes equal values on the two cut edges, and (iii) phi conserves in ends-form (char 2, so signed = unsigned) at every vertex except possibly the two ends of e1. Then phi conserves at every vertex. This is the flow-transfer heart of the recursive two-cut contraction: when a flow on the contracted graph is pulled back by assigning both cut edges the common value a, conservation is automatic away from the contracted pair and the two boundary equations close by the global char-2 sum (unconditionally 0) and the cut sum (phi e1 + phi e2 = 2a = 0). Proof: global sum of the defect d over all vertices is 0 (each edge contributes phi e + phi e = 0); the cut sum equals the sum of phi over the cut = phi e1 + phi e2 = 0 (per-edge case analysis reducing to sum_filter over {e1,e2}); e1 crosses S so exactly one end is in S, making the single-vertex extractions (sum_eq_single_of_mem) force d = 0 at both ends. Simpler than the reference (no sign bookkeeping) because char 2 collapses the signed conservation to the unsigned ends form our whole flow layer already uses. Pre-flighted clean on the pinned lean-checker (3 iterations: sum_ite_eq direction, sum_comm, and the sum_filter branch orientation via ite-not).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  φ e₁ = φ e₂ →
  (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
    (∑ e, ((if endAt e 0 = w then φ e else 0) +
      (if endAt e 1 = w then φ e else 0))) = 0) →
  ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
    (if endAt e 1 = v then φ e else 0))) = 0`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  φ e₁ = φ e₂ →
  (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
    (∑ e, ((if endAt e 0 = w then φ e else 0) +
      (if endAt e 1 = w then φ e else 0))) = 0) →
  ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
    (if endAt e 1 = v then φ e else 0))) = 0`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `1e07b2b0-cb95-413d-9e8e-bba0921b5211` | terminated (root_proved) | 1 | — | 2026-07-11T22:15:01 | 2026-07-11T22:16:35 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  φ e₁ = φ e₂ →
  (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
    (∑ e, ((if endAt e 0 = w then φ e else 0) +
      (if endAt e 1 = w then φ e else 0))) = 0) →
  ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
    (if endAt e 1 = v then φ e else 0))) = 0`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  φ e₁ = φ e₂ →
  (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
    (∑ e, ((if endAt e 0 = w then φ e else 0) +
      (if endAt e 1 = w then φ e else 0))) = 0) →
  ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
    (if endAt e 1 = v then φ e else 0))) = 0 := by
intro V E _ _ _ _ endAt φ S e₁ e₂ hcut he₁₂ hφeq hoff
have hchar2 : ∀ x : ZMod 2, x + x = 0 := by decide
set d : V → (Fin 3 → ZMod 2) := fun v =>
  ∑ e, ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))
  with hd
-- global sum is zero (char 2)
have hsumUniv : ∑ v : V, d v = 0 := by
  simp only [hd]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq Finset.univ (endAt e 0) (fun _ => φ e)]
  rw [Finset.sum_ite_eq Finset.univ (endAt e 1) (fun _ => φ e)]
  simp only [Finset.mem_univ, if_true]
  -- φ e + φ e = 0 in char 2
  funext i
  exact hchar2 _
-- e₁ crosses S
have he₁cut : e₁ ∈ Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) := by
  rw [hcut]; exact Finset.mem_insert_self e₁ {e₂}
have hcross₁ : ¬((endAt e₁ 0 ∈ S) ↔ (endAt e₁ 1 ∈ S)) := (Finset.mem_filter.mp he₁cut).2
-- cut sum equals φ e₁ + φ e₂ = 0
have hsumS : ∑ v ∈ S, d v = 0 := by
  simp only [hd]
  rw [Finset.sum_comm]
  have hterm : ∀ e : E, (∑ v ∈ S, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) =
      if ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)) then φ e else 0 := by
    intro e
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq S (endAt e 0) (fun _ => φ e),
        Finset.sum_ite_eq S (endAt e 1) (fun _ => φ e)]
    by_cases h0 : endAt e 0 ∈ S <;> by_cases h1 : endAt e 1 ∈ S
    · rw [if_pos h0, if_pos h1, if_neg (by simp [h0, h1])]
      funext i; exact hchar2 _
    · rw [if_pos h0, if_neg h1, if_pos (by simp [h0, h1]), add_zero]
    · rw [if_neg h0, if_pos h1, if_pos (by simp [h0, h1]), zero_add]
    · rw [if_neg h0, if_neg h1, if_neg (by simp [h0, h1]), add_zero]
  rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.sum_filter, hcut,
    Finset.sum_pair he₁₂, hφeq]
  funext i; exact hchar2 _
-- e₁ crosses: exactly one end in S
have hendsZero : d (endAt e₁ 0) = 0 ∧ d (endAt e₁ 1) = 0 := by
  by_cases h0 : endAt e₁ 0 ∈ S
  · have h1 : endAt e₁ 1 ∉ S := fun h1 => hcross₁ ⟨fun _ => h1, fun _ => h0⟩
    have hd0 : d (endAt e₁ 0) = 0 := by
      have hsingle : ∑ v ∈ S, d v = d (endAt e₁ 0) := by
        apply Finset.sum_eq_single_of_mem (endAt e₁ 0) h0
        intro v hv hvne
        exact hoff v hvne (fun h => h1 (h ▸ hv))
      rw [← hsingle]; exact hsumS
    have hd1 : d (endAt e₁ 1) = 0 := by
      have hsingle : ∑ v : V, d v = d (endAt e₁ 1) := by
        apply Finset.sum_eq_single_of_mem (endAt e₁ 1) (Finset.mem_univ _)
        intro v _ hvne
        by_cases hv0 : v = endAt e₁ 0
        · rw [hv0]; exact hd0
        · exact hoff v hv0 hvne
      rw [← hsingle]; exact hsumUniv
    exact ⟨hd0, hd1⟩
  · have h1 : endAt e₁ 1 ∈ S := by
      by_contra h1
      exact hcross₁ ⟨fun h => (h0 h).elim, fun h => (h1 h).elim⟩
    have hd1 : d (endAt e₁ 1) = 0 := by
      have hsingle : ∑ v ∈ S, d v = d (endAt e₁ 1) := by
        apply Finset.sum_eq_single_of_mem (endAt e₁ 1) h1
        intro v hv hvne
        exact hoff v (fun h => h0 (h ▸ hv)) hvne
      rw [← hsingle]; exact hsumS
    have hd0 : d (endAt e₁ 0) = 0 := by
      have hsingle : ∑ v : V, d v = d (endAt e₁ 0) := by
        apply Finset.sum_eq_single_of_mem (endAt e₁ 0) (Finset.mem_univ _)
        intro v _ hvne
        by_cases hv1 : v = endAt e₁ 1
        · rw [hv1]; exact hd1
        · exact hoff v hvne hv1
      rw [← hsingle]; exact hsumUniv
    exact ⟨hd0, hd1⟩
intro v
by_cases hv0 : v = endAt e₁ 0
· rw [hv0]; exact hendsZero.1
· by_cases hv1 : v = endAt e₁ 1
  · rw [hv1]; exact hendsZero.2
  · exact hoff v hv0 hv1

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt φ S e₁ e₂ hcut he₁₂ hφeq hoff ; have hchar2 : ∀ x : ZMod 2, x + x = 0 := by decide ; set d : V → (Fin 3 → ZMod 2) := fun v => ;   ∑ e, ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0)) ;   with hd ; -- global sum is zero (char 2) ; have hsumUniv : ∑ v : V, d v = 0 := by ;   simp only [hd] ;   rw [Finset.sum_comm] ;   apply Finset.sum_eq_zero ;   intro e _ ;   rw [Finset.sum_add_distrib] ;   rw [Finset.sum_ite_eq Finset.univ (endAt e 0) (fun _ => φ e)] ;   rw [Finset.sum_ite_eq Finset.univ (endAt e 1) (fun _ => φ e)] ;   simp only [Finset.mem_univ, if_true] ;   -- φ e + φ e = 0 in char 2 ;   funext i ;   exact hchar2 _ ; -- e₁ crosses S ; have he₁cut : e₁ ∈ Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) := by ;   rw [hcut]; exact Finset.mem_insert_self e₁ {e₂} ; have hcross₁ : ¬((endAt e₁ 0 ∈ S) ↔ (endAt e₁ 1 ∈ S)) := (Finset.mem_filter.mp he₁cut).2 ; -- cut sum equals φ e₁ + φ e₂ = 0 ; have hsumS : ∑ v ∈ S, d v = 0 := by ;   simp only [hd] ;   rw [Finset.sum_comm] ;   have hterm : ∀ e : E, (∑ v ∈ S, ((if endAt e 0 = v then φ e else 0) + ;       (if endAt e 1 = v then φ e else 0))) = ;       if ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)) then φ e else 0 := by ;     intro e ;     rw [Finset.sum_add_distrib] ;     rw [Finset.sum_ite_eq S (endAt e 0) (fun _ => φ e), ;         Finset.sum_ite_eq S (endAt e 1) (fun _ => φ e)] ;     by_cases h0 : endAt e 0 ∈ S <;> by_cases h1 : endAt e 1 ∈ S ;     · rw [if_pos h0, if_pos h1, if_neg (by simp [h0, h1])] ;       funext i; exact hchar2 _ ;     · rw [if_pos h0, if_neg h1, if_pos (by simp [h0, h1]), add_zero] ;     · rw [if_neg h0, if_pos h1, if_pos (by simp [h0, h1]), zero_add] ;     · rw [if_neg h0, if_neg h1, if_neg (by simp [h0, h1]), add_zero] ;   rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.sum_filter, hcut, ;     Finset.sum_pair he₁₂, hφeq] ;   funext i; exact hchar2 _ ; -- e₁ crosses: exactly one end in S ; have hendsZero : d (endAt e₁ 0) = 0 ∧ d (endAt e₁ 1) = 0 := by ;   by_cases h0 : endAt e₁ 0 ∈ S ;   · have h1 : endAt e₁ 1 ∉ S := fun h1 => hcross₁ ⟨fun _ => h1, fun _ => h0⟩ ;     have hd0 : d (endAt e₁ 0) = 0 := by ;       have hsingle : ∑ v ∈ S, d v = d (endAt e₁ 0) := by ;         apply Finset.sum_eq_single_of_mem (endAt e₁ 0) h0 ;         intro v hv hvne ;         exact hoff v hvne (fun h => h1 (h ▸ hv)) ;       rw [← hsingle]; exact hsumS ;     have hd1 : d (endAt e₁ 1) = 0 := by ;       have hsingle : ∑ v : V, d v = d (endAt e₁ 1) := by ;         apply Finset.sum_eq_single_of_mem (endAt e₁ 1) (Finset.mem_univ _) ;         intro v _ hvne ;         by_cases hv0 : v = endAt e₁ 0 ;         · rw [hv0]; exact hd0 ;         · exact hoff v hv0 hvne ;       rw [← hsingle]; exact hsumUniv ;     exact ⟨hd0, hd1⟩ ;   · have h1 : endAt e₁ 1 ∈ S := by ;       by_contra h1 ;       exact hcross₁ ⟨fun h => (h0 h).elim, fun h => (h1 h).elim⟩ ;     have hd1 : d (endAt e₁ 1) = 0 := by ;       have hsingle : ∑ v ∈ S, d v = d (endAt e₁ 1) := by ;         apply Finset.sum_eq_single_of_mem (endAt e₁ 1) h1 ;         intro v hv hvne ;         exact hoff v (fun h => h0 (h ▸ hv)) hvne ;       rw [← hsingle]; exact hsumS ;     have hd0 : d (endAt e₁ 0) = 0 := by ;       have hsingle : ∑ v : V, d v = d (endAt e₁ 0) := by ;         apply Finset.sum_eq_single_of_mem (endAt e₁ 0) (Finset.mem_univ _) ;         intro v _ hvne ;         by_cases hv1 : v = endAt e₁ 1 ;         · rw [hv1]; exact hd1 ;         · exact hoff v hvne hv1 ;       rw [← hsingle]; exact hsumUniv ;     exact ⟨hd0, hd1⟩ ; intro v ; by_cases hv0 : v = endAt e₁ 0 ; · rw [hv0]; exact hendsZero.1 ; · by_cases hv1 : v = endAt e₁ 1 ;   · rw [hv1]; exact hendsZero.2 ;   · exact hoff v hv0 hv1` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `69b278fa23f8…` → `beb13a4fc619…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
