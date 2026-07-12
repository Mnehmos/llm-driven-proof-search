import Mathlib

set_option linter.unusedVariables false

def expansionEndAt38 {E : Type} (next : Equiv.Perm (E × Fin 2)) :
    (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)
  | Sum.inl e, j => (e, j)
  | Sum.inr h, 0 => h
  | Sum.inr h, 1 => next h

-- Capstone C. The rotation furnished by steps 14→13 is threaded through the
-- expansion-flow link (36) and the projection link (37).
theorem probe_CAP38 :
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V),
    (∀ e : E, endAt e 0 ≠ endAt e 1) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ((∀ e : E, endAt e 0 ≠ endAt e 1) →
      (∀ S : Finset V, (Finset.univ.filter
        (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
      ∃ next : Equiv.Perm (E × Fin 2),
        (∀ h : E × Fin 2,
          endAt (next h).1 (next h).2 = endAt h.1 h.2) ∧
        (∀ h : E × Fin 2, next h ≠ h) ∧
        (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
          ∃ n : ℕ, (⇑next)^[n] h = k)) →
    (∀ next : Equiv.Perm (E × Fin 2),
      (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
        ∃ n : ℕ, (⇑next)^[n] h = k) →
      (∀ S : Finset V, (Finset.univ.filter
        (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
      ∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
        (∀ k, fK k ≠ 0) ∧
        (∀ (h : E × Fin 2) (i : Fin 3),
          (∑ k : E ⊕ (E × Fin 2),
            ((if expansionEndAt38 next k 0 = h then fK k i else 0) +
             (if expansionEndAt38 next k 1 = h then fK k i else 0))) = 0)) →
    (∀ next : Equiv.Perm (E × Fin 2),
      (∀ h : E × Fin 2,
        endAt (next h).1 (next h).2 = endAt h.1 h.2) →
      (∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
        (∀ k, fK k ≠ 0) ∧
        (∀ (h : E × Fin 2) (i : Fin 3),
          (∑ k : E ⊕ (E × Fin 2),
            ((if expansionEndAt38 next k 0 = h then fK k i else 0) +
             (if expansionEndAt38 next k 1 = h then fK k i else 0))) = 0)) →
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
  intro V E _ _ _ _ endAt hloop hbridge hRotation
    hExpansionFlow hFlowToCover
  obtain ⟨next, hsame, hne, htrans⟩ := hRotation hloop hbridge
  have hflowK := hExpansionFlow next htrans hbridge
  exact hFlowToCover next hsame hflowK
