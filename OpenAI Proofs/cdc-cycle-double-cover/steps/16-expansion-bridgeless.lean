/-
CDC step 16 — The vertex-ring expansion of a bridgeless multigraph is
                bridgeless (mirrors CDCLean.expansionGraph_bridgeless):
                a unique ring cut contradicts the char-2 vanishing of the
                total ring-crossing indicator; a unique spoke cut descends
                (via orbit-invariance of S under the rotation and fiber
                transitivity) to a singleton cut of the original graph.
Problem version : f6d3b3d0-6a74-45dd-8fc3-17214fdec90f
Episode         : b05d039a-3fa5-413b-94c9-b8c226cc46ee
Outcome         : kernel_verified (2026-07-11, attempt 2 — attempt 1 was an
                  indentation transcription slip; math pre-flighted clean)
Chain           : makes the flow hypothesis of the reduction well-posed: the
                  8-flow theorem applies to the expansion.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false

theorem probe_expbridge : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)),
  (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
    ∃ n : ℕ, (⇑next)^[n] h = k) →
  (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ∀ S : Finset (E × Fin 2), (Finset.univ.filter
    (fun k : E ⊕ (E × Fin 2) => ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S)))).card ≠ 1 := by
  intro V E _ _ _ _ endAt next endAtK htrans hKs hK0 hK1 hbridge S hcard
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hcross : ∀ k : E ⊕ (E × Fin 2),
      (¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S))) ↔ k = x := by
    intro k
    constructor
    · intro hk
      have hmem : k ∈ Finset.univ.filter
          (fun k : E ⊕ (E × Fin 2) => ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S))) := by
        simp [hk]
      rw [hx] at hmem
      exact Finset.mem_singleton.mp hmem
    · intro hk
      subst hk
      have hmem : k ∈ Finset.univ.filter
          (fun k : E ⊕ (E × Fin 2) => ¬((endAtK k 0 ∈ S) ↔ (endAtK k 1 ∈ S))) := by
        rw [hx]
        exact Finset.mem_singleton_self k
      simpa using hmem
  have hringPoint : ∀ h : E × Fin 2,
      (if ¬((endAtK (Sum.inr h) 0 ∈ S) ↔ (endAtK (Sum.inr h) 1 ∈ S))
        then (1 : ZMod 2) else 0) =
      (if h ∈ S then (1 : ZMod 2) else 0) + (if next h ∈ S then (1 : ZMod 2) else 0) := by
    intro h
    rw [hK0 h, hK1 h]
    by_cases ha : h ∈ S <;> by_cases hb2 : next h ∈ S <;> simp [ha, hb2]
    all_goals decide
  have hringSum : (∑ h : E × Fin 2,
      (if ¬((endAtK (Sum.inr h) 0 ∈ S) ↔ (endAtK (Sum.inr h) 1 ∈ S))
        then (1 : ZMod 2) else 0)) = 0 := by
    rw [Finset.sum_congr rfl fun h _ => hringPoint h]
    rw [Finset.sum_add_distrib]
    rw [Equiv.sum_comp next (fun h : E × Fin 2 => if h ∈ S then (1 : ZMod 2) else 0)]
    exact CharTwo.add_self_eq_zero _
  cases x with
  | inr h0 =>
    have hone : (∑ h : E × Fin 2,
        (if ¬((endAtK (Sum.inr h) 0 ∈ S) ↔ (endAtK (Sum.inr h) 1 ∈ S))
          then (1 : ZMod 2) else 0)) = 1 := by
      have hpt : ∀ h : E × Fin 2,
          (if ¬((endAtK (Sum.inr h) 0 ∈ S) ↔ (endAtK (Sum.inr h) 1 ∈ S))
            then (1 : ZMod 2) else 0) = (if h = h0 then (1 : ZMod 2) else 0) := by
        intro h
        have hiff : (¬((endAtK (Sum.inr h) 0 ∈ S) ↔ (endAtK (Sum.inr h) 1 ∈ S))) ↔ h = h0 := by
          rw [hcross (Sum.inr h)]
          constructor
          · intro hi
            exact Sum.inr_injective hi
          · intro hi
            rw [hi]
        by_cases heq : h = h0
        · rw [if_pos (hiff.mpr heq), if_pos heq]
        · rw [if_neg (hiff.not.mpr heq), if_neg heq]
      rw [Finset.sum_congr rfl fun h _ => hpt h]
      simp
    rw [hringSum] at hone
    exact zero_ne_one hone
  | inl e0 =>
    have hnoRing : ∀ h : E × Fin 2, ¬¬((endAtK (Sum.inr h) 0 ∈ S) ↔ (endAtK (Sum.inr h) 1 ∈ S)) := by
      intro h hc
      have := (hcross (Sum.inr h)).mp hc
      exact Sum.inr_ne_inl this
    have hnextIff : ∀ h : E × Fin 2, (h ∈ S) ↔ (next h ∈ S) := by
      intro h
      have hn := not_not.mp (hnoRing h)
      rw [hK0 h, hK1 h] at hn
      exact hn
    have hiterate : ∀ (n : ℕ) (h : E × Fin 2), (h ∈ S) ↔ ((⇑next)^[n] h ∈ S) := by
      intro n
      induction n with
      | zero => intro h; exact Iff.rfl
      | succ n ih =>
        intro h
        rw [Function.iterate_succ_apply']
        exact (ih h).trans (hnextIff _)
    have hfiber : ∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
        ((h ∈ S) ↔ (k ∈ S)) := by
      intro h k hvk
      obtain ⟨n, hn⟩ := htrans h k hvk
      have hi := hiterate n h
      rw [hn] at hi
      exact hi
    have hmem : ∀ h : E × Fin 2,
        (endAt h.1 h.2 ∈ Finset.univ.filter
          (fun v => ∃ k : E × Fin 2, endAt k.1 k.2 = v ∧ k ∈ S)) ↔ h ∈ S := by
      intro h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hkv, hkS⟩
        exact (hfiber k h hkv).mp hkS
      · intro hh
        exact ⟨h, rfl, hh⟩
    have hspoke : ∀ e : E,
        (¬((endAtK (Sum.inl e) 0 ∈ S) ↔ (endAtK (Sum.inl e) 1 ∈ S))) ↔
        (¬((endAt e 0 ∈ Finset.univ.filter
            (fun v => ∃ k : E × Fin 2, endAt k.1 k.2 = v ∧ k ∈ S)) ↔
          (endAt e 1 ∈ Finset.univ.filter
            (fun v => ∃ k : E × Fin 2, endAt k.1 k.2 = v ∧ k ∈ S)))) := by
      intro e
      rw [hKs e 0, hKs e 1]
      exact (not_congr (iff_congr (hmem (e, 0)) (hmem (e, 1)))).symm
    have horiginal : (Finset.univ.filter
        (fun e => ¬((endAt e 0 ∈ Finset.univ.filter
            (fun v => ∃ k : E × Fin 2, endAt k.1 k.2 = v ∧ k ∈ S)) ↔
          (endAt e 1 ∈ Finset.univ.filter
            (fun v => ∃ k : E × Fin 2, endAt k.1 k.2 = v ∧ k ∈ S))))) = {e0} := by
      ext e
      rw [Finset.mem_filter, Finset.mem_singleton, and_iff_right (Finset.mem_univ e)]
      rw [← hspoke e, hcross (Sum.inl e)]
      constructor
      · intro hi
        exact Sum.inl_injective hi
      · intro hi
        rw [hi]
    have hc := hbridge (Finset.univ.filter
      (fun v => ∃ k : E × Fin 2, endAt k.1 k.2 = v ∧ k ∈ S))
    rw [horiginal] at hc
    exact hc (Finset.card_singleton e0)
