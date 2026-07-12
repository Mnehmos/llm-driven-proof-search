/-
CDC step 22 — JK-D omission glue (main-chain form of step 20): three connected
                spanning edge sets with every edge omitted by at least one of
                them ⇒ nowhere-zero F₂³-flow in ends form; statements of steps
                17/18/19 as theorem-hypotheses
                (mirrors CDCLean.nowhereZeroGammaFlow_of_threeEdgeConnected's
                 glue, JaegerKilpatrick.lean 388–399)
Problem version : 1cd81f06-9a66-40ee-a070-11724bbd8d7d
Episode         : 40271639-6dcd-4ffd-93a0-b87dfc3d7e75
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : as step 20 but with the pairwise-disjointness hypothesis
                  replaced by omission (∀ e, ∃ i, e ∉ T i) — the interface the
                  doubled-graph packing projection (step 23) actually
                  discharges. Coverage is immediate at the omitting index.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (if endAt e 1 = v then f e i else 0))) = 0) := by
  intro V E _ _ _ _ endAt T h17 h18 h19 hconn homit
  choose F hFe hFs using fun i : Fin 3 =>
    h18 V E endAt (T i) (h19 V E endAt (T i) (hconn i))
  have hcov : ∀ e : E, ∃ i : Fin 3, e ∈ F i := by
    intro e
    obtain ⟨i, hi⟩ := homit e
    exact ⟨i, hFs i e hi⟩
  exact h17 V E endAt F hFe hcov
