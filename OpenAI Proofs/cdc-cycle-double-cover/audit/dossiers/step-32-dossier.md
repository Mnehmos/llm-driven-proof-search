# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger-Kilpatrick bridgeless-to-3EC contraction reduction, step JK-E-3a (2-cut existence): a finite multigraph that is bridgeless, connected, and NOT 3-edge-connected has a 2-edge cut. Proof: negating 3-edge-connectivity gives a nonempty proper subset S with fewer than 3 crossing edges; connectivity forces the crossing edge set of S to be nonempty (any walk from a witness inside S to a witness outside S must cross, by a support-graph reachability induction proving membership in S is preserved along non-crossing steps); bridgelessness rules out cardinality 1; so the cardinality is exactly 2, and Finset.card_eq_two extracts the two distinct witnessing edges. This produces the 2-cut consumed downstream by the contraction pullback (step 31, problem 0cf0561e) in the bridgeless-implies-3-edge-connected recursion. Pre-flighted on the pinned lean-checker (2 iterations: push_neg/push Not normalizes nested ¬Iff inside filter lambdas into an xor form, breaking later syntactic matches -- fixed by naming the cut predicate once via `set` and destructuring the negated 3EC hypothesis with targeted not_imp/not_le rewrites instead of a blanket push_neg; also an induction tactic accidentally generalized unrelated hypotheses -- fixed by isolating the walk-preserves-membership lemma in its own have-block before those hypotheses were introduced).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
    ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ¬ (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ (S : Finset V) (e₁ e₂ : E), e₁ ≠ e₂ ∧
    Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
    ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ¬ (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ (S : Finset V) (e₁ e₂ : E), e₁ ≠ e₂ ∧
    Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `67dd9620-f09d-4642-8552-4450f4afcf07` | terminated (root_proved) | 1 | — | 2026-07-11T22:54:59 | 2026-07-11T22:56:12 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
    ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ¬ (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ (S : Finset V) (e₁ e₂ : E), e₁ ≠ e₂ ∧
    Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
    ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ¬ (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ (S : Finset V) (e₁ e₂ : E), e₁ ≠ e₂ ∧
    Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂} := by
intro V E _ _ _ _ endAt hbridge hconn h3ec
set cut : Finset V → Finset E := fun T =>
  Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ T) ↔ (endAt e 1 ∈ T))) with hcutdef
have hcutdef' : ∀ T : Finset V, cut T =
    Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ T) ↔ (endAt e 1 ∈ T))) := fun T => rfl
have hbridge' : ∀ T : Finset V, (cut T).card ≠ 1 := by
  intro T; rw [hcutdef']; exact hbridge T
simp only [← hcutdef'] at h3ec
obtain ⟨S, hS⟩ := not_forall.mp h3ec
rw [Classical.not_imp, Classical.not_imp, not_le] at hS
obtain ⟨hSne, hSuniv, hlt'⟩ := hS
have hcutne : (cut S).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hprop : ∀ a b : V, (∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) → a ∈ S → b ∈ S := by
    intro a b hstep ha
    by_contra hb
    obtain ⟨t, ht⟩ := hstep
    have htmem : t ∈ cut S := by
      rw [hcutdef']
      rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · simp [h0, h1, ha, hb]
      · simp [h0, h1, ha, hb]
    rw [hempty] at htmem
    exact absurd htmem (Finset.notMem_empty t)
  have hwalk : ∀ x y : V, Relation.ReflTransGen
      (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) x y →
      x ∈ S → y ∈ S := by
    intro x y hxy
    induction hxy with
    | refl => exact id
    | tail hab hbc ih => intro hx; exact hprop _ _ hbc (ih hx)
  obtain ⟨u, hu⟩ := hSne
  have hcompl : (Finset.univ \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hSuniv (Finset.eq_univ_of_forall (fun x => hsub (Finset.mem_univ x)))
  obtain ⟨v, hv⟩ := hcompl
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
  have hvmem : v ∈ S := hwalk u v (hconn u v) hu
  exact hvS hvmem
have hcard : (cut S).card = 2 := by
  have h1 := hbridge' S
  have hpos := hcutne.card_pos
  have h3 := hlt'
  omega
rw [hcutdef'] at hcard
obtain ⟨e₁, e₂, he₁₂, heq⟩ := Finset.card_eq_two.mp hcard
exact ⟨S, e₁, e₂, he₁₂, heq⟩

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt hbridge hconn h3ec ; set cut : Finset V → Finset E := fun T => ;   Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ T) ↔ (endAt e 1 ∈ T))) with hcutdef ; have hcutdef' : ∀ T : Finset V, cut T = ;     Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ T) ↔ (endAt e 1 ∈ T))) := fun T => rfl ; have hbridge' : ∀ T : Finset V, (cut T).card ≠ 1 := by ;   intro T; rw [hcutdef']; exact hbridge T ; simp only [← hcutdef'] at h3ec ; obtain ⟨S, hS⟩ := not_forall.mp h3ec ; rw [Classical.not_imp, Classical.not_imp, not_le] at hS ; obtain ⟨hSne, hSuniv, hlt'⟩ := hS ; have hcutne : (cut S).Nonempty := by ;   by_contra hempty ;   rw [Finset.not_nonempty_iff_eq_empty] at hempty ;   have hprop : ∀ a b : V, (∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ ;       (endAt t 0 = b ∧ endAt t 1 = a)) → a ∈ S → b ∈ S := by ;     intro a b hstep ha ;     by_contra hb ;     obtain ⟨t, ht⟩ := hstep ;     have htmem : t ∈ cut S := by ;       rw [hcutdef'] ;       rcases ht with ⟨h0, h1⟩ \| ⟨h0, h1⟩ ;       · simp [h0, h1, ha, hb] ;       · simp [h0, h1, ha, hb] ;     rw [hempty] at htmem ;     exact absurd htmem (Finset.notMem_empty t) ;   have hwalk : ∀ x y : V, Relation.ReflTransGen ;       (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) x y → ;       x ∈ S → y ∈ S := by ;     intro x y hxy ;     induction hxy with ;     \| refl => exact id ;     \| tail hab hbc ih => intro hx; exact hprop _ _ hbc (ih hx) ;   obtain ⟨u, hu⟩ := hSne ;   have hcompl : (Finset.univ \ S).Nonempty := by ;     rw [Finset.sdiff_nonempty] ;     intro hsub ;     exact hSuniv (Finset.eq_univ_of_forall (fun x => hsub (Finset.mem_univ x))) ;   obtain ⟨v, hv⟩ := hcompl ;   have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2 ;   have hvmem : v ∈ S := hwalk u v (hconn u v) hu ;   exact hvS hvmem ; have hcard : (cut S).card = 2 := by ;   have h1 := hbridge' S ;   have hpos := hcutne.card_pos ;   have h3 := hlt' ;   omega ; rw [hcutdef'] at hcard ; obtain ⟨e₁, e₂, he₁₂, heq⟩ := Finset.card_eq_two.mp hcard ; exact ⟨S, e₁, e₂, he₁₂, heq⟩` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `0d138ab01178…` → `1222823e9980…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
