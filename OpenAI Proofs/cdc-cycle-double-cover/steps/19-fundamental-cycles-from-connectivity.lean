/-
CDC step 19 — Fundamental cycles from connectivity (8-flow campaign JK-B2):
                if T connects all vertices (Relation.ReflTransGen of one-step
                T-adjacency — the connectivity convention for the NW/JK layer),
                every edge outside T has a fundamental cycle. Built from F₂
                path-parity certificates by walk induction; the certificate
                plus the edge's own indicator is even everywhere.
Problem version : c09edee4-ede6-4204-a1ba-305f42c9f080
Episode         : 0a521779-1dd0-4454-b62f-1a9978576729
Outcome         : kernel_verified (2026-07-11, first attempt, pre-flighted)
Chain           : conclusion = hypothesis of step 18 (JK-B1), so:
                  T connected ⇒ even superset of the complement of T.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false

theorem probe_JKB2 : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨
      (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T) := by
  intro V E _ _ _ _ endAt T hconn
  have h2c : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hpath : ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ T, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) u v →
      ∃ w : E → ZMod 2,
        (∀ k : E, w k = 1 → k ∈ T) ∧
        (∀ x : V, (∑ k : E, ((if endAt k 0 = x then w k else 0) +
          (if endAt k 1 = x then w k else 0))) =
          (if u = x then (1 : ZMod 2) else 0) + (if v = x then (1 : ZMod 2) else 0)) := by
    intro u v h
    induction h with
    | refl =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro k hk
        have hk' : (0 : ZMod 2) = 1 := hk
        exact absurd hk' (by decide)
      · intro x
        show (∑ k : E, ((if endAt k 0 = x then (0 : ZMod 2) else 0) +
          (if endAt k 1 = x then (0 : ZMod 2) else 0))) =
          (if u = x then (1 : ZMod 2) else 0) + (if u = x then (1 : ZMod 2) else 0)
        rw [CharTwo.add_self_eq_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [ite_self, ite_self, add_zero]
    | @tail b c hab hstep ih =>
      obtain ⟨w, hwT, hwpar⟩ := ih
      obtain ⟨t, htT, hor⟩ := hstep
      refine ⟨fun k => w k + (if k = t then 1 else 0), ?_, ?_⟩
      · intro k hk
        have hk' : w k + (if k = t then (1 : ZMod 2) else 0) = 1 := hk
        by_cases hkt : k = t
        · rw [hkt]; exact htT
        · rw [if_neg hkt, add_zero] at hk'
          exact hwT k hk'
      · intro x
        show (∑ k : E, ((if endAt k 0 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0) +
          (if endAt k 1 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0))) =
          (if u = x then (1 : ZMod 2) else 0) + (if c = x then (1 : ZMod 2) else 0)
        have hsplit : (∑ k : E, ((if endAt k 0 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0) +
            (if endAt k 1 = x then (w k + (if k = t then (1 : ZMod 2) else 0)) else 0))) =
            (∑ k : E, ((if endAt k 0 = x then w k else 0) +
              (if endAt k 1 = x then w k else 0))) +
            (∑ k : E, ((if endAt k 0 = x then (if k = t then (1 : ZMod 2) else 0) else 0) +
              (if endAt k 1 = x then (if k = t then (1 : ZMod 2) else 0) else 0))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases h0 : endAt k 0 = x <;> by_cases h1 : endAt k 1 = x
          · simp only [if_pos h0, if_pos h1]; ring
          · simp only [if_pos h0, if_neg h1]; ring
          · simp only [if_neg h0, if_pos h1]; ring
          · simp only [if_neg h0, if_neg h1]; ring
        have htinc : (∑ k : E, ((if endAt k 0 = x then (if k = t then (1 : ZMod 2) else 0) else 0) +
            (if endAt k 1 = x then (if k = t then (1 : ZMod 2) else 0) else 0))) =
            ((if endAt t 0 = x then (1 : ZMod 2) else 0) +
              (if endAt t 1 = x then (1 : ZMod 2) else 0)) := by
          refine (Finset.sum_eq_single t ?_ ?_).trans ?_
          · intro b2 hb2 hbt
            simp [hbt]
          · intro ht'
            exact absurd (Finset.mem_univ t) ht'
          · simp
        rw [hsplit, hwpar, htinc]
        rcases hor with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · rw [h0, h1]
          have harr : ∀ a b2 c2 : ZMod 2, (a + b2) + (b2 + c2) = a + c2 := by decide
          exact harr _ _ _
        · rw [h0, h1]
          have harr : ∀ a b2 c2 : ZMod 2, (a + b2) + (c2 + b2) = a + c2 := by decide
          exact harr _ _ _
  intro e heT
  obtain ⟨w, hwT, hwpar⟩ := hpath (endAt e 1) (endAt e 0) (hconn _ _)
  have hwe0 : w e = 0 := by
    rcases h2c (w e) with h | h
    · exact h
    · exact absurd (hwT e h) heT
  set W : E → ZMod 2 := fun k => w k + (if k = e then 1 else 0) with hW
  refine ⟨Finset.univ.filter (fun k => W k = 1), ?_, ?_, ?_⟩
  · intro x
    rw [Finset.sum_filter]
    have hB : ∀ k : E,
        (if W k = 1 then ((if endAt k 0 = x then (1 : ZMod 2) else 0) +
          (if endAt k 1 = x then (1 : ZMod 2) else 0)) else 0) =
        (if endAt k 0 = x then W k else 0) + (if endAt k 1 = x then W k else 0) := by
      intro k
      rcases h2c (W k) with h | h
      · rw [h, if_neg (by decide : ¬(0 : ZMod 2) = 1), ite_self, ite_self, add_zero]
      · rw [h, if_pos rfl]
    rw [Finset.sum_congr rfl fun k _ => hB k]
    have hsplit2 : (∑ k : E, ((if endAt k 0 = x then W k else 0) +
        (if endAt k 1 = x then W k else 0))) =
        (∑ k : E, ((if endAt k 0 = x then w k else 0) +
          (if endAt k 1 = x then w k else 0))) +
        (∑ k : E, ((if endAt k 0 = x then (if k = e then (1 : ZMod 2) else 0) else 0) +
          (if endAt k 1 = x then (if k = e then (1 : ZMod 2) else 0) else 0))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hW]
      by_cases h0 : endAt k 0 = x <;> by_cases h1 : endAt k 1 = x
      · simp only [if_pos h0, if_pos h1]; ring
      · simp only [if_pos h0, if_neg h1]; ring
      · simp only [if_neg h0, if_pos h1]; ring
      · simp only [if_neg h0, if_neg h1]; ring
    have heinc : (∑ k : E, ((if endAt k 0 = x then (if k = e then (1 : ZMod 2) else 0) else 0) +
        (if endAt k 1 = x then (if k = e then (1 : ZMod 2) else 0) else 0))) =
        ((if endAt e 0 = x then (1 : ZMod 2) else 0) +
          (if endAt e 1 = x then (1 : ZMod 2) else 0)) := by
      refine (Finset.sum_eq_single e ?_ ?_).trans ?_
      · intro b2 hb2 hbe
        simp [hbe]
      · intro he'
        exact absurd (Finset.mem_univ e) he'
      · simp
    rw [hsplit2, hwpar, heinc]
    have harr2 : ∀ a b2 : ZMod 2, (a + b2) + (b2 + a) = 0 := by decide
    exact harr2 _ _
  · have hWe : W e = 1 := by
      simp [hW, hwe0]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hWe⟩
  · intro k hk hke
    have hWk : W k = 1 := (Finset.mem_filter.mp hk).2
    simp only [hW] at hWk
    rw [if_neg hke, add_zero] at hWk
    exact hwT k hWk
