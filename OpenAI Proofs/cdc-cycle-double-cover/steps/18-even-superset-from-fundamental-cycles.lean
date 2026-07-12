/-
CDC step 18 — Even superset from fundamental cycles (8-flow campaign JK-B1;
                char-2 simplification of exists_even_superset_compl_of_spanningTree):
                if every non-tree edge has a fundamental cycle (even set through
                it, other edges in T), the mod-2 sum of these cycles is an even
                set containing the whole complement of T. Bypasses the
                reference's integer-circulation route entirely.
Problem version : 68e5b80e-c41c-45b7-b2c3-ace4d05ebcb6
Episode         : 35479379-9829-498c-af26-ab45e65fe4d4
Outcome         : kernel_verified (2026-07-11, first attempt, pre-flighted)
Campaign        : JK-B2 (deferred): fundamental cycles exist for spanning-tree
                  complements, via Relation.ReflTransGen walk induction.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false

theorem probe_JKB1 : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (T : Finset E),
  (∀ e : E, e ∉ T → ∃ C : Finset E,
    (∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) →
  ∃ F : Finset E,
    (∀ v : V, (∑ k ∈ F, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
      (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
    (∀ e : E, e ∉ T → e ∈ F) := by
  intro V E _ _ _ _ endAt T hcyc
  have hcyc' : ∀ e : E, ∃ C : Finset E, e ∉ T →
      ((∀ v : V, (∑ k ∈ C, ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
        (if endAt k 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      e ∈ C ∧ (∀ k ∈ C, k ≠ e → k ∈ T)) := by
    intro e
    by_cases he : e ∈ T
    · exact ⟨∅, fun h => absurd he h⟩
    · obtain ⟨C, hCp⟩ := hcyc e he
      exact ⟨C, fun _ => hCp⟩
  choose C hC using hcyc'
  set w : E → ZMod 2 := fun k =>
    ∑ e' ∈ Finset.univ.filter (fun x => x ∉ T), (if k ∈ C e' then (1 : ZMod 2) else 0)
    with hw
  have h2c : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  refine ⟨Finset.univ.filter (fun k => w k = 1), ?_, ?_⟩
  · intro v
    rw [Finset.sum_filter]
    have hB : ∀ k : E,
        (if w k = 1 then ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
          (if endAt k 1 = v then (1 : ZMod 2) else 0)) else 0) =
        w k * ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
          (if endAt k 1 = v then (1 : ZMod 2) else 0)) := by
      intro k
      rcases h2c (w k) with h | h
      · rw [h, if_neg (by decide : ¬(0 : ZMod 2) = 1), zero_mul]
      · rw [h, if_pos rfl, one_mul]
    rw [Finset.sum_congr rfl fun k _ => hB k]
    have hpt : ∀ k : E,
        w k * ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
          (if endAt k 1 = v then (1 : ZMod 2) else 0)) =
        ∑ e' ∈ Finset.univ.filter (fun x => x ∉ T),
          (if k ∈ C e' then (1 : ZMod 2) else 0) *
            ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
              (if endAt k 1 = v then (1 : ZMod 2) else 0)) := by
      intro k
      rw [hw]
      exact Finset.sum_mul _ _ _
    rw [Finset.sum_congr rfl fun k _ => hpt k]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun e' he' => ?_
    have heT : e' ∉ T := (Finset.mem_filter.mp he').2
    obtain ⟨hCe_even, hCe_mem, hCe_sub⟩ := hC e' heT
    have hpt2 : ∀ k : E,
        (if k ∈ C e' then (1 : ZMod 2) else 0) *
          ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
            (if endAt k 1 = v then (1 : ZMod 2) else 0)) =
        (if k ∈ C e' then ((if endAt k 0 = v then (1 : ZMod 2) else 0) +
          (if endAt k 1 = v then (1 : ZMod 2) else 0)) else 0) := by
      intro k
      by_cases hk : k ∈ C e' <;> simp [hk]
    rw [Finset.sum_congr rfl fun k _ => hpt2 k]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact hCe_even v
  · intro e heT
    have hwe : w e = 1 := by
      simp only [hw]
      have h1 : (∑ e' ∈ Finset.univ.filter (fun x => x ∉ T),
          (if e ∈ C e' then (1 : ZMod 2) else 0)) =
          (if e ∈ C e then (1 : ZMod 2) else 0) := by
        refine Finset.sum_eq_single e ?_ ?_
        · intro b hb hbe
          have hbT : b ∉ T := (Finset.mem_filter.mp hb).2
          rw [if_neg]
          intro hmem
          exact heT ((hC b hbT).2.2 e hmem (Ne.symm hbe))
        · intro hnot
          exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ e, heT⟩) hnot
      rw [h1, if_pos (hC e heT).2.1]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, hwe⟩
