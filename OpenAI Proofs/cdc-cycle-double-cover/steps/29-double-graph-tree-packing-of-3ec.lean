/-
CDC step 29 — JK-E-2a: 3-edge-connected ⇒ three disjoint spanning-connected
                edge sets in the doubled multigraph (bundles steps 21+27,
                carrying 24/25/26 as 27's premises)
Problem version : 6edd347f-0058-4275-a8d7-67596c70f332
Episode         : 6bc3de88-43b8-4688-8ab4-d51377e6009b
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : one application — h27 at edge type E × Fin 2 (endAt' p =
                  endAt p.1), fed h21∘3EC (the classifier-form doubled packing
                  condition) and h24/h25/h26. Conclusion is step 23's hypothesis
                  shape. The five verified leaf statements are theorem-hypotheses.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ f ∈ S, ¬ Relation.ReflTransGen
    (fun a b => ∃ s ∈ S.erase f,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
    (endAt f 0) (endAt f 1)) →
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
  (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card ≤
      (Finset.univ.image c).card - 1 ∧
    ((S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
        (Finset.univ.image c).card - 1 →
      ∀ u v : V, Relation.ReflTransGen
        (fun a b => c a = c b ∨ ∃ s ∈ S,
          (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (F : Fin 3 → Finset E) (e : E),
  (∀ i j : Fin 3, i ≠ j → Disjoint (F i) (F j)) →
  (∀ i : Fin 3, ∀ h ∈ F i, ¬ Relation.ReflTransGen
    (fun a b => ∃ s ∈ (F i).erase h,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
    (endAt h 0) (endAt h 1)) →
  (∀ F' : Fin 3 → Finset E, (∀ i j : Fin 3, i ≠ j → Disjoint (F' i) (F' j)) →
    (∀ i : Fin 3, ∀ h ∈ F' i, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ (F' i).erase h,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt h 0) (endAt h 1)) →
    (∑ i : Fin 3, (F' i).card) ≤ ∑ i : Fin 3, (F i).card) →
  (∀ i : Fin 3, e ∉ F i) →
  ∃ P : V → Prop,
    P (endAt e 0) ∧ P (endAt e 1) ∧
    ∀ i : Fin 3, ∀ u v : V, P u → P v →
      Relation.ReflTransGen (fun a b => P a ∧ P b ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ c : V → V, 3 * ((Finset.univ.image c).card - 1) ≤
    (Finset.univ.filter (fun s : E => c (endAt s 0) ≠ c (endAt s 1))).card) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (S : Finset E') (c : V' → V'),
    (∀ u v : V', c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
        (endAt' t 0 = a ∧ endAt' t 1 = b) ∨ (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => c a = c b ∨ ∃ t ∈ S,
        (c (endAt' t 0) = c a ∧ c (endAt' t 1) = c b) ∨
        (c (endAt' t 0) = c b ∧ c (endAt' t 1) = c a)) u v) →
    ∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ S,
        (endAt' t 0 = a ∧ endAt' t 1 = b) ∨ (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (S : Finset E') (c : V' → V'),
    (∀ f ∈ S, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ S.erase f,
        (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a))
      (endAt' f 0) (endAt' f 1)) →
    (∀ u v : V', c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
        (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a)) u v) →
    (S.filter (fun s => c (endAt' s 0) ≠ c (endAt' s 1))).card ≤
        (Finset.univ.image c).card - 1 ∧
      ((S.filter (fun s => c (endAt' s 0) ≠ c (endAt' s 1))).card =
          (Finset.univ.image c).card - 1 →
        ∀ u v : V', Relation.ReflTransGen
          (fun a b => c a = c b ∨ ∃ s ∈ S,
            (c (endAt' s 0) = c a ∧ c (endAt' s 1) = c b) ∨
            (c (endAt' s 0) = c b ∧ c (endAt' s 1) = c a)) u v)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E') (e : E'),
    (∀ i j : Fin 3, i ≠ j → Disjoint (F i) (F j)) →
    (∀ i : Fin 3, ∀ h ∈ F i, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ (F i).erase h,
        (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a))
      (endAt' h 0) (endAt' h 1)) →
    (∀ F' : Fin 3 → Finset E', (∀ i j : Fin 3, i ≠ j → Disjoint (F' i) (F' j)) →
      (∀ i : Fin 3, ∀ h ∈ F' i, ¬ Relation.ReflTransGen
        (fun a b => ∃ s ∈ (F' i).erase h,
          (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a))
        (endAt' h 0) (endAt' h 1)) →
      (∑ i : Fin 3, (F' i).card) ≤ ∑ i : Fin 3, (F i).card) →
    (∀ i : Fin 3, e ∉ F i) →
    ∃ P : V' → Prop,
      P (endAt' e 0) ∧ P (endAt' e 1) ∧
      ∀ i : Fin 3, ∀ u v : V', P u → P v →
        Relation.ReflTransGen (fun a b => P a ∧ P b ∧ ∃ t ∈ F i,
          (endAt' t 0 = a ∧ endAt' t 1 = b) ∨ (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
  ∃ U : Fin 3 → Finset E,
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v)) →
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ U : Fin 3 → Finset (E × Fin 2),
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
        (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) := by
  intro V E _ _ _ _ endAt h21 h24 h25 h26 h27 h3ec
  exact h27 V (E × Fin 2) (fun p i => endAt p.1 i) (h21 V E endAt h3ec) h24 h25 h26
