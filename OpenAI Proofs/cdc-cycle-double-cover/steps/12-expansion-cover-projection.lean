/-
CDC step 12 — Projection: an even double cover of the vertex-ring cubic
                expansion (in localized per-half-edge form) restricts to an
                exact ends-form even double cover of the original multigraph
                (mirrors CDCLean.projected_vertex_even / projectEvenDoubleCover;
                needs only the sameVertex property of the rotation)
Problem version : b202d6d2-6d22-432b-a74d-ef472621567b
Episode         : 99c5106b-1669-4318-ac4b-146bbe1ed5e0
Outcome         : kernel_verified (2026-07-11, first attempt, pre-flighted)
Chain           : conclusion = the cover hypothesis of step 11 (4adc1d0b), so
                  expansion cover ⇒ CDC of the original graph via steps 09+11.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false

theorem probe_projection : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2)),
  (∀ h : E × Fin 2, endAt (next h).1 (next h).2 = endAt h.1 h.2) →
  (∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
      memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
        memberK s (Sum.inr (next.symm h)) = 0) ∧
    (∀ e : E,
      (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2)) →
  ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
        ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E,
      (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2) := by
  intro V E _ _ _ _ endAt next hsame hcov
  obtain ⟨memberK, hloc, htwoK⟩ := hcov
  have hsymmSame : ∀ h : E × Fin 2,
      endAt (next.symm h).1 (next.symm h).2 = endAt h.1 h.2 := by
    intro h
    have hx := hsame (next.symm h)
    rw [Equiv.apply_symm_apply] at hx
    exact hx.symm
  have h2c : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  set member : (Fin 3 → ZMod 2) → E → ZMod 2 :=
    fun s e => memberK s (Sum.inl e) with hmember
  refine ⟨member, ?_, ?_⟩
  · intro s v
    simp only [hmember]
    rw [Finset.sum_filter]
    have hB : ∀ e : E,
        (if memberK s (Sum.inl e) = 1 then
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0)) else 0) =
        (if endAt e 0 = v then memberK s (Sum.inl e) else 0) +
          (if endAt e 1 = v then memberK s (Sum.inl e) else 0) := by
      intro e
      rcases h2c (memberK s (Sum.inl e)) with h | h
      · rw [h, if_neg (by decide : ¬(0 : ZMod 2) = 1), ite_self, ite_self, add_zero]
      · rw [h, if_pos rfl]
    rw [Finset.sum_congr rfl fun e _ => hB e]
    have hC : ∀ e : E,
        (if endAt e 0 = v then memberK s (Sum.inl e) else 0) +
          (if endAt e 1 = v then memberK s (Sum.inl e) else 0) =
        ∑ j : Fin 2, (if endAt e j = v then memberK s (Sum.inl e) else 0) := by
      intro e
      rw [Fin.sum_univ_two]
    rw [Finset.sum_congr rfl fun e _ => hC e]
    have hprod : (∑ e : E, ∑ j : Fin 2,
        (if endAt e j = v then memberK s (Sum.inl e) else 0)) =
        ∑ h : E × Fin 2, (if endAt h.1 h.2 = v then memberK s (Sum.inl h.1) else 0) :=
      (Fintype.sum_prod_type (f := fun h : E × Fin 2 =>
        if endAt h.1 h.2 = v then memberK s (Sum.inl h.1) else 0)).symm
    rw [hprod]
    have htotal : (∑ h : E × Fin 2,
        ((if endAt h.1 h.2 = v then memberK s (Sum.inl h.1) else 0) +
          ((if endAt h.1 h.2 = v then memberK s (Sum.inr h) else 0) +
            (if endAt h.1 h.2 = v then memberK s (Sum.inr (next.symm h)) else 0)))) = 0 := by
      refine Finset.sum_eq_zero fun h _ => ?_
      by_cases hv : endAt h.1 h.2 = v
      · rw [if_pos hv, if_pos hv, if_pos hv, ← add_assoc]
        exact hloc s h
      · rw [if_neg hv, if_neg hv, if_neg hv, add_zero, add_zero]
    rw [Finset.sum_add_distrib] at htotal
    rw [Finset.sum_add_distrib] at htotal
    have hP : (∑ h : E × Fin 2,
        (if endAt h.1 h.2 = v then memberK s (Sum.inr (next.symm h)) else 0)) =
        ∑ h : E × Fin 2, (if endAt h.1 h.2 = v then memberK s (Sum.inr h) else 0) := by
      have hpoint : ∀ h : E × Fin 2,
          (if endAt h.1 h.2 = v then memberK s (Sum.inr (next.symm h)) else 0) =
          (fun k : E × Fin 2 =>
            if endAt k.1 k.2 = v then memberK s (Sum.inr k) else 0) (next.symm h) := by
        intro h
        show _ = (if endAt (next.symm h).1 (next.symm h).2 = v
          then memberK s (Sum.inr (next.symm h)) else 0)
        rw [hsymmSame h]
      rw [Finset.sum_congr rfl fun h _ => hpoint h]
      exact Equiv.sum_comp next.symm (fun k : E × Fin 2 =>
        if endAt k.1 k.2 = v then memberK s (Sum.inr k) else 0)
    rw [hP] at htotal
    rw [CharTwo.add_self_eq_zero, add_zero] at htotal
    exact htotal
  · intro e
    simp only [hmember]
    exact htwoK e
