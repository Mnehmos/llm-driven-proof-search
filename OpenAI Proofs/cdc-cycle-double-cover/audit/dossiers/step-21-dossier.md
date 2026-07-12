# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow campaign step JK-C (mirrors CDCLean.doubleGraph_satisfiesTreePackingCondition_of_threeEdgeConnected, JaegerKilpatrick.lean 181-333): if a finite multigraph (endAt : E -> Fin 2 -> V) is 3-edge-connected (every nonempty proper vertex set has cut of size at least 3, crossing encoded as the negated membership biconditional, matching our bridgeless convention), then its doubled multigraph (edge type E x Fin 2, both copies with the same ends) satisfies the Nash-Williams/Tutte tree-packing condition for k = 3: for every partition of V -- encoded as an arbitrary classifier c : V -> V whose classes are the fibers over Finset.univ.image c -- the number of doubled edges whose ends lie in different classes is at least 3 * (number of classes - 1). Proof is the reference counting argument: each class fiber is a nonempty proper subset (properness from having at least 2 classes), so its cut has >= 3 edges; summing over classes counts each crossing edge exactly twice (the fibers of its two end-classes), giving 3 * m <= 2 * crossings(G); the doubled graph has exactly 2 * crossings(G) crossing edges (product with Fin 2), and 3 * (m - 1) <= 3 * m follows by omega. The single-class and empty cases are trivial by Nat subtraction. Pre-flighted on the pinned lean-checker (2 iterations; only fix was replacing a nonexistent lemma name with Finset.card_filter + Finset.card_pair).

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `472fc585-97d4-4e96-a00f-df338308555c` | terminated (root_proved) | 1 | — | 2026-07-11T18:05:52 | 2026-07-11T18:07:22 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card := by
intro V E _ _ _ _ endAt h3 c
by_cases hm : (Finset.univ.image c).card < 2
· have h1 : (Finset.univ.image c).card - 1 = 0 := by omega
  rw [h1]
  simp
· have h3' : ∀ k ∈ Finset.univ.image c,
      3 ≤ (Finset.univ.filter (fun e : E =>
        ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card := by
    intro k hk
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hk
    have hne : (Finset.univ.filter (fun v => c v = k)).Nonempty :=
      ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
    have hproper : (Finset.univ.filter (fun v => c v = k)) ≠ Finset.univ := by
      intro hEq
      have hall : ∀ w : V, c w = k := by
        intro w
        have hw : w ∈ Finset.univ.filter (fun v => c v = k) := by
          rw [hEq]; exact Finset.mem_univ w
        exact (Finset.mem_filter.mp hw).2
      have himg : Finset.univ.image c ⊆ {k} := by
        intro x hx
        obtain ⟨w, _, hwx⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_singleton, ← hwx]
        exact hall w
      have hle := Finset.card_le_card himg
      simp at hle
      omega
    have hfe : (Finset.univ.filter (fun e : E =>
        ¬((endAt e 0 ∈ Finset.univ.filter (fun v => c v = k)) ↔
          (endAt e 1 ∈ Finset.univ.filter (fun v => c v = k))))) =
        (Finset.univ.filter (fun e : E =>
          ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))) := by
      apply Finset.filter_congr
      intro e _
      simp [Finset.mem_filter]
    have hcut := h3 _ hne hproper
    rwa [hfe] at hcut
  have hsum : 3 * (Finset.univ.image c).card ≤
      ∑ k ∈ Finset.univ.image c, (Finset.univ.filter (fun e : E =>
        ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card := by
    calc 3 * (Finset.univ.image c).card
        = ∑ k ∈ Finset.univ.image c, 3 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum h3'
  have hcount : (∑ k ∈ Finset.univ.image c, (Finset.univ.filter (fun e : E =>
        ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card) =
      2 * (Finset.univ.filter (fun e : E =>
        c (endAt e 0) ≠ c (endAt e 1))).card := by
    have hswap : (∑ k ∈ Finset.univ.image c, (Finset.univ.filter (fun e : E =>
          ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card) =
        ∑ e : E, ∑ k ∈ Finset.univ.image c,
          (if ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k) then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.card_filter]
    rw [hswap]
    have hedge : ∀ e : E, (∑ k ∈ Finset.univ.image c,
        (if ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k) then 1 else 0)) =
        if c (endAt e 0) ≠ c (endAt e 1) then 2 else 0 := by
      intro e
      by_cases hce : c (endAt e 0) = c (endAt e 1)
      · rw [if_neg (fun h => h hce)]
        apply Finset.sum_eq_zero
        intro k _
        rw [hce]
        simp
      · rw [if_pos hce, ← Finset.card_filter]
        have hfilter : ((Finset.univ.image c).filter (fun k =>
            ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))) =
            ({c (endAt e 0), c (endAt e 1)} : Finset V) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨_, hk⟩
            by_cases h0 : c (endAt e 0) = k
            · exact Or.inl h0.symm
            · by_cases h1 : c (endAt e 1) = k
              · exact Or.inr h1.symm
              · exact absurd (iff_of_false h0 h1) hk
          · rintro (rfl | rfl)
            · exact ⟨⟨endAt e 0, Finset.mem_univ _, rfl⟩,
                fun h => hce (h.mp rfl).symm⟩
            · exact ⟨⟨endAt e 1, Finset.mem_univ _, rfl⟩,
                fun h => hce (h.mpr rfl)⟩
        rw [hfilter]
        exact Finset.card_pair hce
    calc (∑ e : E, ∑ k ∈ Finset.univ.image c,
          (if ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k) then 1 else 0)) =
        ∑ e : E, (if c (endAt e 0) ≠ c (endAt e 1) then 2 else 0) := by
          apply Finset.sum_congr rfl
          intro e _
          exact hedge e
      _ = ∑ e ∈ Finset.univ.filter (fun e : E =>
            c (endAt e 0) ≠ c (endAt e 1)), 2 := by
          rw [Finset.sum_filter]
      _ = 2 * (Finset.univ.filter (fun e : E =>
            c (endAt e 0) ≠ c (endAt e 1))).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hdbl : (Finset.univ.filter (fun p : E × Fin 2 =>
      c (endAt p.1 0) ≠ c (endAt p.1 1))).card =
      2 * (Finset.univ.filter (fun e : E =>
        c (endAt e 0) ≠ c (endAt e 1))).card := by
    have hprod : (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))) =
        (Finset.univ.filter (fun e : E =>
          c (endAt e 0) ≠ c (endAt e 1))) ×ˢ (Finset.univ : Finset (Fin 2)) := by
      ext p
      simp [Finset.mem_product]
    rw [hprod, Finset.card_product]
    simp [mul_comm]
  rw [hcount] at hsum
  rw [hdbl]
  omega

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt h3 c ; by_cases hm : (Finset.univ.image c).card < 2 ; · have h1 : (Finset.univ.image c).card - 1 = 0 := by omega ;   rw [h1] ;   simp ; · have h3' : ∀ k ∈ Finset.univ.image c, ;       3 ≤ (Finset.univ.filter (fun e : E => ;         ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card := by ;     intro k hk ;     obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hk ;     have hne : (Finset.univ.filter (fun v => c v = k)).Nonempty := ;       ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩ ;     have hproper : (Finset.univ.filter (fun v => c v = k)) ≠ Finset.univ := by ;       intro hEq ;       have hall : ∀ w : V, c w = k := by ;         intro w ;         have hw : w ∈ Finset.univ.filter (fun v => c v = k) := by ;           rw [hEq]; exact Finset.mem_univ w ;         exact (Finset.mem_filter.mp hw).2 ;       have himg : Finset.univ.image c ⊆ {k} := by ;         intro x hx ;         obtain ⟨w, _, hwx⟩ := Finset.mem_image.mp hx ;         rw [Finset.mem_singleton, ← hwx] ;         exact hall w ;       have hle := Finset.card_le_card himg ;       simp at hle ;       omega ;     have hfe : (Finset.univ.filter (fun e : E => ;         ¬((endAt e 0 ∈ Finset.univ.filter (fun v => c v = k)) ↔ ;           (endAt e 1 ∈ Finset.univ.filter (fun v => c v = k))))) = ;         (Finset.univ.filter (fun e : E => ;           ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))) := by ;       apply Finset.filter_congr ;       intro e _ ;       simp [Finset.mem_filter] ;     have hcut := h3 _ hne hproper ;     rwa [hfe] at hcut ;   have hsum : 3 * (Finset.univ.image c).card ≤ ;       ∑ k ∈ Finset.univ.image c, (Finset.univ.filter (fun e : E => ;         ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card := by ;     calc 3 * (Finset.univ.image c).card ;         = ∑ k ∈ Finset.univ.image c, 3 := by ;           rw [Finset.sum_const, smul_eq_mul, mul_comm] ;       _ ≤ _ := Finset.sum_le_sum h3' ;   have hcount : (∑ k ∈ Finset.univ.image c, (Finset.univ.filter (fun e : E => ;         ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card) = ;       2 * (Finset.univ.filter (fun e : E => ;         c (endAt e 0) ≠ c (endAt e 1))).card := by ;     have hswap : (∑ k ∈ Finset.univ.image c, (Finset.univ.filter (fun e : E => ;           ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))).card) = ;         ∑ e : E, ∑ k ∈ Finset.univ.image c, ;           (if ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k) then 1 else 0) := by ;       rw [Finset.sum_comm] ;       apply Finset.sum_congr rfl ;       intro k _ ;       rw [Finset.card_filter] ;     rw [hswap] ;     have hedge : ∀ e : E, (∑ k ∈ Finset.univ.image c, ;         (if ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k) then 1 else 0)) = ;         if c (endAt e 0) ≠ c (endAt e 1) then 2 else 0 := by ;       intro e ;       by_cases hce : c (endAt e 0) = c (endAt e 1) ;       · rw [if_neg (fun h => h hce)] ;         apply Finset.sum_eq_zero ;         intro k _ ;         rw [hce] ;         simp ;       · rw [if_pos hce, ← Finset.card_filter] ;         have hfilter : ((Finset.univ.image c).filter (fun k => ;             ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k))) = ;             ({c (endAt e 0), c (endAt e 1)} : Finset V) := by ;           ext k ;           simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_insert, ;             Finset.mem_singleton] ;           constructor ;           · rintro ⟨_, hk⟩ ;             by_cases h0 : c (endAt e 0) = k ;             · exact Or.inl h0.symm ;             · by_cases h1 : c (endAt e 1) = k ;               · exact Or.inr h1.symm ;               · exact absurd (iff_of_false h0 h1) hk ;           · rintro (rfl \| rfl) ;             · exact ⟨⟨endAt e 0, Finset.mem_univ _, rfl⟩, ;                 fun h => hce (h.mp rfl).symm⟩ ;             · exact ⟨⟨endAt e 1, Finset.mem_univ _, rfl⟩, ;                 fun h => hce (h.mpr rfl)⟩ ;         rw [hfilter] ;         exact Finset.card_pair hce ;     calc (∑ e : E, ∑ k ∈ Finset.univ.image c, ;           (if ¬(c (endAt e 0) = k ↔ c (endAt e 1) = k) then 1 else 0)) = ;         ∑ e : E, (if c (endAt e 0) ≠ c (endAt e 1) then 2 else 0) := by ;           apply Finset.sum_congr rfl ;           intro e _ ;           exact hedge e ;       _ = ∑ e ∈ Finset.univ.filter (fun e : E => ;             c (endAt e 0) ≠ c (endAt e 1)), 2 := by ;           rw [Finset.sum_filter] ;       _ = 2 * (Finset.univ.filter (fun e : E => ;             c (endAt e 0) ≠ c (endAt e 1))).card := by ;           rw [Finset.sum_const, smul_eq_mul, mul_comm] ;   have hdbl : (Finset.univ.filter (fun p : E × Fin 2 => ;       c (endAt p.1 0) ≠ c (endAt p.1 1))).card = ;       2 * (Finset.univ.filter (fun e : E => ;         c (endAt e 0) ≠ c (endAt e 1))).card := by ;     have hprod : (Finset.univ.filter (fun p : E × Fin 2 => ;         c (endAt p.1 0) ≠ c (endAt p.1 1))) = ;         (Finset.univ.filter (fun e : E => ;           c (endAt e 0) ≠ c (endAt e 1))) ×ˢ (Finset.univ : Finset (Fin 2)) := by ;       ext p ;       simp [Finset.mem_product] ;     rw [hprod, Finset.card_product] ;     simp [mul_comm] ;   rw [hcount] at hsum ;   rw [hdbl] ;   omega` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `e813c1f78d28…` → `eebcec1fa2df…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
