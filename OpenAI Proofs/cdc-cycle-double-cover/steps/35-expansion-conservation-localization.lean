import Mathlib

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

-- Ends-form conservation on the cubic expansion incidence collapses to the
-- localized three-term form consumed by step 15.
theorem probe_CAP35 : ∀ (E : Type) [Fintype E] [DecidableEq E]
    (next : Equiv.Perm (E × Fin 2))
    (endAtK : (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2))
    (fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2)),
  (∀ (e : E) (j : Fin 2), endAtK (Sum.inl e) j = (e, j)) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 0 = h) →
  (∀ h : E × Fin 2, endAtK (Sum.inr h) 1 = next h) →
  (∀ (h : E × Fin 2) (i : Fin 3),
    (∑ k : E ⊕ (E × Fin 2), ((if endAtK k 0 = h then fK k i else 0) +
      (if endAtK k 1 = h then fK k i else 0))) = 0) →
  ∀ h : E × Fin 2,
    fK (Sum.inl h.1) + fK (Sum.inr h) + fK (Sum.inr (next.symm h)) = 0 := by
  intro E _ _ next endAtK fK hKs hK0 hK1 hcons h
  funext i
  have hc := hcons h i
  rw [Fintype.sum_sum_type] at hc
  -- The spoke part has exactly one incidence, through slot h.2.
  have hspoke : (∑ e : E,
      ((if endAtK (Sum.inl e) 0 = h then fK (Sum.inl e) i else 0) +
       (if endAtK (Sum.inl e) 1 = h then fK (Sum.inl e) i else 0))) =
      fK (Sum.inl h.1) i := by
    have hterm : ∀ e : E,
        ((if endAtK (Sum.inl e) 0 = h then fK (Sum.inl e) i else 0) +
         (if endAtK (Sum.inl e) 1 = h then fK (Sum.inl e) i else 0)) =
        (if e = h.1 then fK (Sum.inl e) i else 0) := by
      intro e
      rw [hKs e 0, hKs e 1]
      by_cases hee : e = h.1
      · by_cases h2 : (0 : Fin 2) = h.2
        · rw [if_pos (Prod.ext hee h2),
              if_neg (fun hc => by
                have h12 := (Prod.ext_iff.mp hc).2
                have h01 : (0 : Fin 2) ≠ 1 := by decide
                exact h01 (h2.trans h12.symm)),
              if_pos hee, add_zero]
        · have h2' : (1 : Fin 2) = h.2 := by omega
          rw [if_neg (fun hc => h2 (Prod.ext_iff.mp hc).2),
              if_pos (Prod.ext hee h2'), if_pos hee, zero_add]
      · rw [if_neg (fun hc => hee (Prod.ext_iff.mp hc).1),
            if_neg (fun hc => hee (Prod.ext_iff.mp hc).1),
            if_neg hee, add_zero]
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    rw [Finset.sum_ite_eq' Finset.univ h.1 (fun e => fK (Sum.inl e) i)]
    simp
  -- The ring part has incidences inr h and inr (next.symm h).
  have hring : (∑ k : E × Fin 2,
      ((if endAtK (Sum.inr k) 0 = h then fK (Sum.inr k) i else 0) +
       (if endAtK (Sum.inr k) 1 = h then fK (Sum.inr k) i else 0))) =
      fK (Sum.inr h) i + fK (Sum.inr (next.symm h)) i := by
    have hterm : ∀ k : E × Fin 2,
        ((if endAtK (Sum.inr k) 0 = h then fK (Sum.inr k) i else 0) +
         (if endAtK (Sum.inr k) 1 = h then fK (Sum.inr k) i else 0)) =
        ((if k = h then fK (Sum.inr k) i else 0) +
         (if k = next.symm h then fK (Sum.inr k) i else 0)) := by
      intro k
      rw [hK0 k, hK1 k]
      congr 1
      by_cases hk : next k = h
      · rw [if_pos hk, if_pos (by rw [Equiv.eq_symm_apply]; exact hk)]
      · rw [if_neg hk,
            if_neg (fun hc => hk (by rw [← Equiv.eq_symm_apply]; exact hc))]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ h (fun k => fK (Sum.inr k) i),
        Finset.sum_ite_eq' Finset.univ (next.symm h) (fun k => fK (Sum.inr k) i)]
    simp
  rw [hspoke, hring] at hc
  simpa [Pi.add_apply, add_assoc] using hc
