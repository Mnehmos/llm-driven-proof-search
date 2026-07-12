/-
CDC step 17 — Jaeger flow combination (8-flow campaign step JK-A):
                three even edge sets covering every edge define a nowhere-zero
                F₂³-flow (coordinate i = indicator of the i-th set)
                (mirrors CDCLean.nowhereZeroGammaFlow_of_evenCover)
Problem version : 993b9826-f68c-4534-8517-877d118adf7b
Episode         : 045a2345-7bc2-4469-8784-179d6870e554
Outcome         : kernel_verified (2026-07-11, first attempt, pre-flighted)
Campaign        : remaining inputs are the three even covering sets (from
                  spanning-tree complements via Nash-Williams tree packing)
                  and the ends-form → localized-form conservation glue.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false

theorem probe_JKA : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (F : Fin 3 → Finset E),
  (∀ (i : Fin 3) (v : V),
    (∑ e ∈ F i, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
      (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
  (∀ e : E, ∃ i : Fin 3, e ∈ F i) →
  ∃ f : E → (Fin 3 → ZMod 2),
    (∀ e : E, f e ≠ 0) ∧
    (∀ (v : V) (i : Fin 3),
      (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
        (if endAt e 1 = v then f e i else 0))) = 0) := by
  intro V E _ _ _ _ endAt F hEven hCover
  refine ⟨fun e i => if e ∈ F i then 1 else 0, ?_, ?_⟩
  · intro e h0
    obtain ⟨i, hi⟩ := hCover e
    have hc := congrFun h0 i
    simp [hi] at hc
  · intro v i
    have hsum : ∀ (j : Fin 2),
        (∑ e : E, (if endAt e j = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0)) =
        ∑ e ∈ F i, (if endAt e j = v then (1 : ZMod 2) else 0) := by
      intro j
      have hcomm : ∀ e : E,
          (if endAt e j = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0) =
          (if e ∈ F i then (if endAt e j = v then (1 : ZMod 2) else 0) else 0) := by
        intro e
        by_cases he : e ∈ F i <;> by_cases hv : endAt e j = v <;> simp [he, hv]
      rw [Finset.sum_congr rfl fun e _ => hcomm e]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    show (∑ e : E, ((if endAt e 0 = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0) +
      (if endAt e 1 = v then (if e ∈ F i then (1 : ZMod 2) else 0) else 0))) = 0
    rw [Finset.sum_add_distrib, hsum 0, hsum 1, ← Finset.sum_add_distrib]
    exact hEven i v
