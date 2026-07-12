/-
CDC step 30 — JK-E-2b: three disjoint spanning-connected sets in the doubled
                multigraph ⇒ nowhere-zero ends-form F₂³ flow over E (bundles
                steps 23+22, carrying 17/18/19 as 22's premises)
Problem version : 1a88148f-0169-4a60-b4e5-6365573274b8
Episode         : d4cb12d9-65e5-49cc-8abf-af9d4ed7e632
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : obtain the doubled tuple U; h23 projects (Prod.fst) to three
                  connected spanning sets in E omitting every edge; h22 (fed
                  h17/h18/h19) produces the flow. Composed after step 29 this
                  gives 3EC ⇒ flow (the monolithic form, problem 98a7b64d, is
                  registered but OPEN: its 10.8KB statement exceeds the episode
                  response cap; the two halves 29+30 establish the result).
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E'),
    (∀ (i : Fin 3) (v : V'),
      (∑ e ∈ F i, ((if endAt' e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    (∀ e : E', ∃ i : Fin 3, e ∈ F i) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
    ∃ F : Finset E',
      (∀ v : V', (∑ k ∈ F, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E', e ∉ T' → e ∈ F)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ T', (endAt' t 0 = a ∧ endAt' t 1 = b) ∨
        (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    ∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Fin 3 → Finset E),
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E'),
    (∀ (i : Fin 3) (v : V'),
      (∑ e ∈ F i, ((if endAt' e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    (∀ e : E', ∃ i : Fin 3, e ∈ F i) →
    ∃ f : E' → (Fin 3 → ZMod 2),
      (∀ e : E', f e ≠ 0) ∧
      (∀ (v : V') (i : Fin 3),
        (∑ e : E', ((if endAt' e 0 = v then f e i else 0) +
          (if endAt' e 1 = v then f e i else 0))) = 0)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
    ∃ F : Finset E',
      (∀ v : V', (∑ k ∈ F, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E', e ∉ T' → e ∈ F)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (T' : Finset E'),
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ T', (endAt' t 0 = a ∧ endAt' t 1 = b) ∨
        (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    ∀ e : E', e ∉ T' → ∃ C : Finset E',
      (∀ v : V', (∑ k ∈ C, ((if endAt' k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt' k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T')) →
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ e : E, ∃ i : Fin 3, e ∉ T i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0)) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (U : Fin 3 → Finset (E × Fin 2)),
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
      (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) →
  (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) →
  ∃ T : Fin 3 → Finset E,
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) u v) ∧
    (∀ e : E, ∃ i : Fin 3, e ∉ T i)) →
  (∃ U : Fin 3 → Finset (E × Fin 2),
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
        (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v)) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0) := by
  intro V E _ _ _ _ endAt h17 h18 h19 h22 h23 hU
  obtain ⟨U, hUdisj, hUconn⟩ := hU
  obtain ⟨T, hTconn, homit⟩ := h23 V E endAt U hUconn hUdisj
  exact h22 V E endAt T h17 h18 h19 hTconn homit
