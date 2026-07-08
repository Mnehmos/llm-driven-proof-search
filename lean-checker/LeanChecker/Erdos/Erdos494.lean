import Mathlib

/-!
# Erdős Problem #494 — the product version is false (Steinerberger's counterexample)

Erdős asked whether a finite set `A ⊆ ℂ` is determined by the multiset of sums of
its `k`-element subsets. The multiplicative analogue — is `A` determined by the
multiset of **products** of its `k`-subsets? — is **false**, by a counterexample
of Steinerberger. The corpus (`FormalConjectures/ErdosProblems/494.lean`,
`erdos_494.variants.product`) ships it as `sorry`; this is a self-contained,
kernel-verified proof.

## The counterexample

Let `ω` be a primitive cube root of unity and take
`A = {1, ω, ω², 2}`, `B = ω·A = {1, ω, ω², 2ω}` (`A ≠ B`). Then `B = A.map (ω·)`,
so its 3-subsets are the `ω·`-images of `A`'s 3-subsets, and **each** 3-subset
product scales by `ω³ = 1` — hence the two product-multisets are equal. The whole
proof reduces to one general lemma: multiplying every element of `A` by a scalar
`c` with `cᵏ = 1` leaves `prodMultiset A k` unchanged.
-/

namespace Erdos494

open Finset

/-- The multiset of products of `k`-element subsets of `A` (corpus definition). -/
noncomputable def prodMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map (fun s => s.prod id)

/-- **Key lemma.** Scaling every element of `A` by `c` with `c ^ k = 1` leaves the
multiset of `k`-subset products unchanged: each `k`-subset product picks up
`c ^ k = 1`. -/
theorem prodMultiset_map_mul (A : Finset ℂ) (c : ℂ) (k : ℕ) (hc : c ^ k = 1)
    (emb : ℂ ↪ ℂ) (hemb : ⇑emb = (c * ·)) :
    prodMultiset (A.map emb) k = prodMultiset A k := by
  unfold prodMultiset
  rw [Finset.powersetCard_map]
  simp only [Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro s hs
  have hcard : s.card = k := (Finset.mem_powersetCard.mp (Finset.mem_val.mp hs)).2
  rw [Function.comp_apply, show (mapEmbedding emb).toEmbedding s = s.map emb from rfl,
    Finset.prod_map]
  simp only [hemb, id_eq]
  rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, hc, one_mul]

/-- **Erdős #494 (product version, false — Steinerberger).** There are distinct
finite `A, B ⊆ ℂ` of equal cardinality with the same multiset of 3-subset
products. -/
theorem product :
    ∃ (A B : Finset ℂ), A.card = B.card ∧ prodMultiset A 3 = prodMultiset B 3 ∧
      A ≠ B := by
  have h3 : (3 : ℕ) ≠ 0 := by norm_num
  have hprim : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 h3
  set ω : ℂ := Complex.exp (2 * ↑Real.pi * Complex.I / 3) with hωdef
  have hω3 : ω ^ 3 = 1 := hprim.pow_eq_one
  have hω0 : ω ≠ 0 := by
    intro h; rw [h] at hω3; simp at hω3
  have hω1 : ω ≠ 1 := by
    intro h; exact hprim.ne_one (by norm_num) h
  let emb : ℂ ↪ ℂ := ⟨(ω * ·), mul_right_injective₀ hω0⟩
  refine ⟨{1, ω, ω ^ 2, 2}, ({1, ω, ω ^ 2, 2} : Finset ℂ).map emb, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
  · exact (prodMultiset_map_mul {1, ω, ω ^ 2, 2} ω 3 hω3 emb rfl).symm
  · -- A ≠ B : 2 ∈ A but 2 ∉ B
    intro hAB
    have h2A : (2 : ℂ) ∈ ({1, ω, ω ^ 2, 2} : Finset ℂ) := by simp
    rw [hAB, Finset.mem_map] at h2A
    obtain ⟨x, hxA, hx2⟩ := h2A
    simp only [emb, Function.Embedding.coeFn_mk] at hx2
    -- hx2 : ω * x = 2, with x ∈ {1, ω, ω², 2}
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxA
    rcases hxA with rfl | rfl | rfl | rfl
    · -- x = 1 : ω = 2 → ω³ = 8 ≠ 1
      rw [mul_one] at hx2; rw [hx2] at hω3; norm_num at hω3
    · -- x = ω : ω² = 2 → ω⁶ = 8 = (ω³)² = 1
      have : ω ^ 6 = 2 ^ 3 := by rw [show ω ^ 6 = (ω * ω) ^ 3 by ring, hx2]
      rw [show ω ^ 6 = (ω ^ 3) ^ 2 by ring, hω3] at this; norm_num at this
    · -- x = ω² : ω³ = 2 → 1 = 2
      rw [show ω * ω ^ 2 = ω ^ 3 by ring, hω3] at hx2; norm_num at hx2
    · -- x = 2 : 2ω = 2 → ω = 1
      apply hω1
      have : ω * 2 = 1 * 2 := by rw [hx2]; ring
      exact mul_right_cancel₀ (by norm_num) this

end Erdos494
