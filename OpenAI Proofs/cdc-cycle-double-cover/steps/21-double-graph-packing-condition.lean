/-
CDC step 21 — JK-C: three-edge-connectivity ⇒ the doubled multigraph satisfies
                the Nash-Williams–Tutte tree-packing condition for k = 3
                (mirrors CDCLean.doubleGraph_satisfiesTreePackingCondition_of_threeEdgeConnected,
                 JaegerKilpatrick.lean 181–333)
Problem version : cd0a7b4a-c670-4f6c-8b6d-3bbee2afc41f
Episode         : 472fc585-97d4-4e96-a00f-df338308555c
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : partitions encoded as arbitrary classifiers c : V → V with
                  classes = fibers over Finset.univ.image c (no Setoid, no
                  Quotient, no classical decidability). Each fiber is a
                  nonempty proper cut when ≥ 2 classes exist, so h3 gives ≥ 3
                  crossing edges per class; summing counts each crossing edge
                  exactly twice ({c end₀, c end₁} pair filter, card_pair);
                  the doubled crossing set is a product with Fin 2.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
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
