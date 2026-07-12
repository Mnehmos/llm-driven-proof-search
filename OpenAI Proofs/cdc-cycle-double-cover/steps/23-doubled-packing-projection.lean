/-
CDC step 23 — JK-D projection: three pairwise-disjoint connected spanning sets
                in the doubled multigraph (E × Fin 2) project under Prod.fst to
                three connected spanning sets in E with every edge omitted by
                at least one — the pigeonhole on the two copies
                (mirrors the packing half of
                 CDCLean.exists_three_spanningTrees_omitting_each_edge,
                 JaegerKilpatrick.lean 334–386, minus all spanning-tree
                 structure: connectivity + omission suffice for our flow layer)
Problem version : 18818939-1981-47c2-be2d-db85b813ba9b
Episode         : 10f70a28-eb75-45e4-bee8-5b8379977a96
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : T i := image Prod.fst (U i); connectivity by
                  Relation.ReflTransGen.mono; omission by contradiction —
                  witness copies give an injective Fin 3 → Fin 2 via pairwise
                  disjointness, contradicting cardinality.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (U : Fin 3 → Finset (E × Fin 2)),
  (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
      (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) →
  (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) →
  ∃ T : Fin 3 → Finset E,
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ T i, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) u v) ∧
    (∀ e : E, ∃ i : Fin 3, e ∉ T i) := by
  intro V E _ _ _ _ endAt U hconn hdisj
  refine ⟨fun i => (U i).image Prod.fst, ?_, ?_⟩
  · intro i u v
    refine Relation.ReflTransGen.mono ?_ (hconn i u v)
    rintro a b ⟨t, htU, hends⟩
    exact ⟨t.1, Finset.mem_image_of_mem Prod.fst htU, hends⟩
  · intro e
    by_contra hall
    push Not at hall
    choose x hxU hxe using fun i => Finset.mem_image.mp (hall i)
    have hjinj : Function.Injective (fun i : Fin 3 => (x i).2) := by
      intro i k hj
      have hx : x i = x k := Prod.ext ((hxe i).trans (hxe k).symm) hj
      by_contra hik
      exact Finset.disjoint_left.mp (hdisj i k hik) (hxU i) (hx ▸ hxU k)
    have hle := Fintype.card_le_of_injective _ hjinj
    norm_num at hle
