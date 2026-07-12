/-
CDC step 20 — JK-D-lite (flow-layer glue): three pairwise-disjoint connected
                spanning edge sets ⇒ nowhere-zero F₂³-flow in ends form,
                composing steps 19 → 18 → 17 as theorem-hypotheses
                (mirrors the composition CDCLean.nowhereZeroGammaFlow_of_threeEdgeConnected
                 modulo the tree-packing input, JaegerKilpatrick.lean 334-399)
Problem version : 43da22a1-fd7e-4f76-9f52-084b2f1a6e9f
Episode         : c4caad40-c393-4c67-aac4-d4d51aed3f3f
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : theorem-as-hypothesis chaining — the verified root statements
                  of steps 17 (993b9826), 18 (68e5b80e) and 19 (c09edee4) are
                  hypotheses h17/h18/h19; per tree i, h19∘h18 yields an even
                  superset F i of the complement of T i; pairwise disjointness
                  puts each edge outside T 0 or T 1, so the F i cover all
                  edges; h17 concludes. Only two of the three trees are needed
                  for coverage.
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
  (∀ i j : Fin 3, i ≠ j → Disjoint (T i) (T j)) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0) := by
intro V E _ _ _ _ endAt T h17 h18 h19 hconn hdisj
choose F hFe hFs using fun i : Fin 3 =>
  h18 V E endAt (T i) (h19 V E endAt (T i) (hconn i))
have hcov : ∀ e : E, ∃ i : Fin 3, e ∈ F i := by
  intro e
  by_cases h0 : e ∈ T 0
  · refine ⟨1, hFs 1 e ?_⟩
    intro h1
    exact Finset.disjoint_left.mp (hdisj 0 1 (by decide)) h0 h1
  · exact ⟨0, hFs 0 e h0⟩
exact h17 V E endAt F hFe hcov
