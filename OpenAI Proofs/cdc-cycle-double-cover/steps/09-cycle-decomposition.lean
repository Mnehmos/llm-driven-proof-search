/-
CDC step 09 — Cycle decomposition of even edge sets: every even edge set of a
                finite loopless multigraph splits exactly (multiplicity-exact
                filter-length equation) into nonempty inclusion-minimal even
                edge sets, i.e. multigraph cycles
                (mirrors CDCLean.decompose_even_edge_set)
Problem version : d269b928-fb3b-4ba5-b376-956bb15565d4
Episode         : 82fc190d-0f34-48bf-b4f3-f65641ebc129
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : Finset.strongInductionOn; minimal-or-split; char-2 evenness
                  of the complement via Finset.sum_sdiff. No decide lemmas.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  ∀ F : Finset E,
    (∀ v : V,
      (∑ e ∈ F, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
        (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
    ∃ L : List (Finset E),
      (∀ C ∈ L, C.Nonempty ∧
        (∀ v : V,
          (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
        (∀ D : Finset E, D.Nonempty → D ⊆ C →
          (∀ v : V,
            (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
              (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
          D = C)) ∧
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0) := by
intro V E _ _ _ _ endAt hloop F
refine Finset.strongInductionOn F ?_
intro F ih hF
by_cases hne : F.Nonempty
· by_cases hmin : ∀ D : Finset E, D.Nonempty → D ⊆ F →
      (∀ v : V,
        (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) → D = F
  · refine ⟨[F], ?_, ?_⟩
    · intro C hC
      rw [List.mem_singleton] at hC
      subst hC
      exact ⟨hne, hF, hmin⟩
    · intro e
      by_cases he : e ∈ F <;> simp [he]
  · push_neg at hmin
    obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin
    have hsdiff : ∀ v : V,
        (∑ e ∈ F \ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0 := by
      intro v
      have hsplit := Finset.sum_sdiff (f := fun e =>
        (if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0)) hDF
      rw [hDeven v, hF v] at hsplit
      simpa using hsplit
    have hDssub : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDF, hDproper⟩
    have hRssub : F \ D ⊂ F := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro heq
      obtain ⟨e, heD⟩ := hDne
      have hmem : e ∈ F \ D := by
        rw [heq]
        exact hDF heD
      simp [heD] at hmem
    obtain ⟨LD, hLDprops, hLD⟩ := ih D hDssub hDeven
    obtain ⟨LR, hLRprops, hLR⟩ := ih (F \ D) hRssub hsdiff
    refine ⟨LD ++ LR, ?_, ?_⟩
    · intro C hC
      rcases List.mem_append.mp hC with h | h
      · exact hLDprops C h
      · exact hLRprops C h
    · intro e
      rw [List.filter_append, List.length_append, hLD e, hLR e]
      by_cases heD : e ∈ D
      · have heF : e ∈ F := hDF heD
        simp [Finset.mem_sdiff, heD, heF]
      · by_cases heF : e ∈ F <;> simp [Finset.mem_sdiff, heD, heF]
· have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  subst hzero
  refine ⟨[], ?_, ?_⟩
  · intro C hC
    simp at hC
  · intro e
    simp
