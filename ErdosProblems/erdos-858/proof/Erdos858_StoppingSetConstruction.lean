/-
Erdős Problem #858 — exchange-free stopping-set construction (replaces Lemma 3.3).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Lemma 3.3.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 2eaa4b8e-f9cf-472c-8da3-0beb67a17b64,
problem_version_id 24eee3ac-c938-483b-8301-351121e2d2c4.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 2b03da27…

Lemma 3.3 (paper): every maximum-weight antichain can be taken of the form ∂D
for a continuation set D — proved there by iteratively adding leaves. This is a
DIRECT, non-iterative construction of that D: for any ⪯-antichain B ⊆ [1,N] with
1 ∉ B, the set D_B := {a ∈ [1,N] : no ⪯-ancestor z of a lies in B} is a
continuation set (1 ∈ D_B, downward-closed under π, ⊆ [1,N]) with B ⊆ ∂(D_B).

Proof: D_B is downward-closed because ancestors of π(a) are ancestors of a
(transitivity); 1 ∈ D_B since z ⪯ 1 forces z = 1 ∉ B; for b ∈ B (so b ≥ 2 as
1 ∉ B), b ∉ D_B (b ⪯ b, b ∈ B) and π(b) ∈ D_B (any z ⪯ π(b) ⪯ b lying in B would
equal b by the antichain property, but z ≤ π(b) < b), hence b ∈ ∂(D_B).

Combined with the verified Proposition 3.4 (Σ_{∂D} 1/n = 1 + Σ_{a∈D} q_N) and the
optimization inequality (Σ_{a∈D} q_N ≤ Σ_{a≤K} q_N under the sign condition),
this gives the ≤ direction of the max-closure duality M(N) = 1 + max_D Σ_D q_N
(Corollary 3.5) with NO iterative exchange argument. The hypotheses are the
verified §1–§2 facts (⪯ transitive/reflexive/refines-≤; π an ancestor with
parent bounds), taken abstractly.

Lean note: because the goal `b ∈ ∂(D_B)` has nested `Finset.filter` memberships
(∂D_B's predicate mentions D_B), use `rw [Finset.mem_filter]` (rewrites the
outermost membership only), NOT `simp only [Finset.mem_filter]` (which
over-expands the inner D_B memberships).
-/
import Mathlib

namespace Erdos858

/-- Exchange-free stopping-set construction. For a `⪯`-antichain `B ⊆ [1,N]` with
`1 ∉ B`, there is a continuation set `D` (with `1 ∈ D`, `π`-downward-closed,
`⊆ [1,N]`) such that `B ⊆ ∂D`. -/
theorem stopping_set_construction :
    ∀ (π : ℕ → ℕ) (N : ℕ) (B : Finset ℕ), 1 ≤ N →
      (∀ a b c : ℕ, (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
        (∃ t : ℕ, c = b * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → b < p) →
        (∃ t : ℕ, c = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p)) →
      (∀ a : ℕ, ∃ t : ℕ, a = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
      (∀ w : ℕ, 2 ≤ w → ∃ t : ℕ, w = π w * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → π w < p) →
      (∀ w : ℕ, 2 ≤ w → w ≤ N → 1 ≤ π w ∧ π w < w) →
      (∀ z a : ℕ, (∃ t : ℕ, a = z * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → z < p) → 0 < a → z ≤ a) →
      (∀ x y : ℕ, x ∈ B → y ∈ B → (∃ t : ℕ, y = x * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → x < p) → x = y) →
      1 ∉ B → B ⊆ Finset.Icc 1 N →
      ∃ D : Finset ℕ, 1 ∈ D ∧ (∀ a ∈ D, 2 ≤ a → π a ∈ D) ∧ D ⊆ Finset.Icc 1 N ∧
        B ⊆ (Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D) := by
  intro π N B hN htrans hrefl hpi_anc hpi hpre_le hB_ac h1notB hBsub
  classical
  refine ⟨(Finset.Icc 1 N).filter (fun a => ∀ z : ℕ, (∃ t : ℕ, a = z * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → z < p) → z ∉ B), ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_refl 1, hN⟩, ?_⟩
    intro z hz
    obtain ⟨t, ht, _⟩ := hz
    have hz1 : z = 1 := Nat.dvd_one.mp ⟨t, ht⟩
    rw [hz1]; exact h1notB
  · intro a haD ha2
    simp only [Finset.mem_filter, Finset.mem_Icc] at haD ⊢
    obtain ⟨⟨ha1, haN⟩, haclosed⟩ := haD
    obtain ⟨hpi1, hpilt⟩ := hpi a ha2 haN
    refine ⟨⟨hpi1, by omega⟩, ?_⟩
    intro z hz
    have hpianc := hpi_anc a ha2
    exact haclosed z (htrans z (π a) a hz hpianc)
  · exact Finset.filter_subset _ _
  · intro b hb
    have hbIcc := hBsub hb
    simp only [Finset.mem_Icc] at hbIcc
    obtain ⟨hb1, hbN⟩ := hbIcc
    have hb2 : 2 ≤ b := by
      rcases Nat.lt_or_ge b 2 with h | h
      · exfalso
        have hbeq : b = 1 := by omega
        rw [hbeq] at hb
        exact h1notB hb
      · exact h
    obtain ⟨hpi1, hpilt⟩ := hpi b hb2 hbN
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨hb1, hbN⟩, ?_, ?_⟩
    · intro hbD
      rw [Finset.mem_filter] at hbD
      exact hbD.2 b (hrefl b) hb
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨hpi1, by omega⟩, ?_⟩
      intro z hz hzB
      have hpianc := hpi_anc b hb2
      have hzb := htrans z (π b) b hz hpianc
      have hzeqb : z = b := hB_ac z b hzB hb hzb
      have hzle : z ≤ π b := hpre_le z (π b) hz (by omega)
      rw [hzeqb] at hzle
      omega

end Erdos858
