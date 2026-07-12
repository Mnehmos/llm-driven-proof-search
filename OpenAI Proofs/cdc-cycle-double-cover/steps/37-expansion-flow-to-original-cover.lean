import Mathlib

set_option linter.unusedVariables false

def expansionEndAt37 {E : Type} (next : Equiv.Perm (E × Fin 2)) :
    (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)
  | Sum.inl e, j => (e, j)
  | Sum.inr h, 0 => h
  | Sum.inr h, 1 => next h

-- Capstone B. Step 35 localizes the expansion flow, step 15+08 turns it into
-- a localized expansion cover, and step 12 projects that cover to G.
theorem probe_CAP37 :
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2)),
    (∀ h : E × Fin 2,
      endAt (next h).1 (next h).2 = endAt h.1 h.2) →
    (∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2),
          ((if expansionEndAt37 next k 0 = h then fK k i else 0) +
           (if expansionEndAt37 next k 1 = h then fK k i else 0))) = 0)) →
    (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2),
          ((if expansionEndAt37 next k 0 = h then fK k i else 0) +
           (if expansionEndAt37 next k 1 = h then fK k i else 0))) = 0) →
      ∀ h : E × Fin 2,
        fK (Sum.inl h.1) + fK (Sum.inr h) +
          fK (Sum.inr (next.symm h)) = 0) →
    (∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
      (∀ k, fK k ≠ 0) →
      (∀ h : E × Fin 2,
        fK (Sum.inl h.1) + fK (Sum.inr h) +
          fK (Sum.inr (next.symm h)) = 0) →
      ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
        (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
          memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
            memberK s (Sum.inr (next.symm h)) = 0) ∧
        (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
          memberK s (Sum.inl e) = 1).card = 2)) →
    ((∀ h : E × Fin 2,
        endAt (next h).1 (next h).2 = endAt h.1 h.2) →
      (∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
        (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
          memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
            memberK s (Sum.inr (next.symm h)) = 0) ∧
        (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
          memberK s (Sum.inl e) = 1).card = 2)) →
      ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
        (∀ (s : Fin 3 → ZMod 2) (v : V),
          (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
            ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
             (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
        (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
          member s e = 1).card = 2)) →
    ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
           (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        member s e = 1).card = 2) := by
  intro V E _ _ _ _ endAt next hsame hflowK hlocalize
    hExpansionCover hProject
  obtain ⟨fK, hnzK, hendsK⟩ := hflowK
  have hlocal : ∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) +
        fK (Sum.inr (next.symm h)) = 0 :=
    hlocalize fK hendsK
  have hcoverK := hExpansionCover fK hnzK hlocal
  exact hProject hsame hcoverK
