import Mathlib

/-!
# Erdős #647 — deleting two exceptional indices

The second-layer large-factor argument produces at most one primary
square-scale exception and at most one nonsmooth-cofactor exception.  This
small combinatorial lemma records that deleting both exceptional sets from a
block of width `W` leaves at least `W - 2` usable indices.

Tracked proof-search provenance (2026-07-16): problem
`83cca71d-9412-40b7-950b-39a7d70cf31c`, episode
`bfd9dcb2-564e-4deb-b494-a7e4cffce319`, root hash
`e16aa2a7df868e330230201711d3c71e3ff6f0ab2fff74e24e10a8141aecf00a`;
outcome `kernel_verified`.
-/

/-- Removing two subsets of a `W`-element index type, each of cardinality at
most one, leaves a set whose cardinality is within two of `W`. -/
theorem erdos647_two_exceptional_indices :
    ∀ (W : ℕ) (A B : Finset (Fin W)),
      A.card ≤ 1 → B.card ≤ 1 →
      W ≤ (Finset.univ \ (A ∪ B)).card + 2 := by
  intro W A B hA hB
  have hAB : (A ∪ B).card ≤ A.card + B.card :=
    Finset.card_union_le A B
  have hsub : A ∪ B ⊆ (Finset.univ : Finset (Fin W)) :=
    Finset.subset_univ _
  have hpartition := Finset.card_sdiff_add_card_eq_card hsub
  have huniv : (Finset.univ : Finset (Fin W)).card = W := by simp
  omega
