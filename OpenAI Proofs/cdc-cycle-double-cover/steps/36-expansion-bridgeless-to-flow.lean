import Mathlib

set_option linter.unusedVariables false

-- The standard cubic-expansion endpoint map used by steps 15, 16, and 35.
def expansionEndAt {E : Type} (next : Equiv.Perm (E × Fin 2)) :
    (E ⊕ (E × Fin 2)) → Fin 2 → (E × Fin 2)
  | Sum.inl e, j => (e, j)
  | Sum.inr h, 0 => h
  | Sum.inr h, 1 => next h

-- Capstone A. Step 16 supplies hExpansionBridgeless; step 34 supplies hEightFlow.
-- Their conclusions compose at the concrete expansion endpoint map.
theorem probe_CAP36 :
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (next : Equiv.Perm (E × Fin 2)),
    (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ((∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
        ∃ n : ℕ, (⇑next)^[n] h = k) →
      (∀ S : Finset V, (Finset.univ.filter
        (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
      ∀ S : Finset (E × Fin 2), (Finset.univ.filter
        (fun k : E ⊕ (E × Fin 2) =>
          ¬((expansionEndAt next k 0 ∈ S) ↔
            (expansionEndAt next k 1 ∈ S)))).card ≠ 1) →
    (∀ (V' E' : Type) [Fintype V'] [Fintype E']
        [DecidableEq V'] [DecidableEq E'] (endAt' : E' → Fin 2 → V'),
      (∀ S : Finset V', (Finset.univ.filter
        (fun e : E' => ¬((endAt' e 0 ∈ S) ↔ (endAt' e 1 ∈ S)))).card ≠ 1) →
      ∃ f : E' → (Fin 3 → ZMod 2),
        (∀ e : E', f e ≠ 0) ∧
        (∀ (v : V') (i : Fin 3),
          (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
            (if endAt' e 1 = v then f e i else 0))) = 0)) →
    ∃ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
      (∀ k, fK k ≠ 0) ∧
      (∀ (h : E × Fin 2) (i : Fin 3),
        (∑ k : E ⊕ (E × Fin 2),
          ((if expansionEndAt next k 0 = h then fK k i else 0) +
           (if expansionEndAt next k 1 = h then fK k i else 0))) = 0) := by
  intro V E _ _ _ _ endAt next htrans hbridge
    hExpansionBridgeless hEightFlow
  have hbridgeK : ∀ S : Finset (E × Fin 2), (Finset.univ.filter
      (fun k : E ⊕ (E × Fin 2) =>
        ¬((expansionEndAt next k 0 ∈ S) ↔
          (expansionEndAt next k 1 ∈ S)))).card ≠ 1 :=
    hExpansionBridgeless htrans hbridge
  exact hEightFlow (E × Fin 2) (E ⊕ (E × Fin 2))
    (expansionEndAt next) hbridgeK
