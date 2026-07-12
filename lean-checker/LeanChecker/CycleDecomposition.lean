import LeanChecker.Multigraph

open Multigraph
open scoped BigOperators

namespace Multigraph

private theorem even_sdiff {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] {G : Multigraph V E} {F D : Finset E} (hDF : D ⊆ F)
    (hF : G.IsEulerianSubgraph F) (hD : G.IsEulerianSubgraph D) :
    G.IsEulerianSubgraph (F \ D) := by
  intro v
  have hsplit := Finset.sum_sdiff hDF (f := fun e ↦ if G.endpoints e = s(v, v) then 2 else if v ∈ G.endpoints e then 1 else 0)
  have hdF := hF v
  have hdD := hD v
  rw [IsEulerianSubgraph] at hF hD
  unfold degreeIn at *
  rw [← hsplit] at hdF
  obtain ⟨kF, hkF⟩ := hdF
  obtain ⟨kD, hkD⟩ := hdD
  use kF - kD
  omega

/-- Every finite even edge set is an edge-disjoint union of multigraph cycles. -/
theorem decompose_even_edge_set {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
    (G : Multigraph V E) (F : Finset E) (hF : G.IsEulerianSubgraph F) :
    ∃ L : List (Cycle G),
      ∀ e : E, (L.filter fun C ↦ decide (e ∈ C.edges)).length = if e ∈ F then 1 else 0 := by
  classical
  revert hF
  refine Finset.strongInductionOn F ?_
  intro F ih hF
  by_cases hne : F.Nonempty
  · by_cases hmin :
      (∀ D : Finset E, D.Nonempty → D ⊆ F → G.IsEulerianSubgraph D → D = F)
    · let C : Cycle G :=
        { edges := F
          nonempty := hne
          even := hF
          minimal := hmin }
      refine ⟨[C], ?_⟩
      intro e
      by_cases he : e ∈ F <;> simp [C, he]
    · push Not at hmin
      obtain ⟨D, hDne, hDF, hDeven, hDproper⟩ := hmin
      have hDssub : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDF, hDproper⟩
      have hRssub : F \ D ⊂ F := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨e, heD⟩ := hDne
        have : e ∈ F \ D := by simpa [heq] using hDF heD
        simp [heD] at this
      obtain ⟨LD, hLD⟩ := ih D hDssub hDeven
      obtain ⟨LR, hLR⟩ := ih (F \ D) hRssub (even_sdiff hDF hF hDeven)
      refine ⟨LD ++ LR, ?_⟩
      intro e
      rw [List.filter_append, List.length_append, hLD e, hLR e]
      by_cases heD : e ∈ D
      · have heF : e ∈ F := hDF heD
        simp [heD, heF]
      · by_cases heF : e ∈ F <;> simp [heD, heF]
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst F
    exact ⟨[], by simp⟩

end Multigraph
