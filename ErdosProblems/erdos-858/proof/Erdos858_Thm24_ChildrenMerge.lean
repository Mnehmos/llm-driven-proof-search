/-
Erdős Problem #858 — Theorem 2.4 (subtree recursion), the "continue" branch
(child-subtree merge). Companion to the root-dichotomy core.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Theorem 2.4.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 78200cfa-a248-49b6-b58a-24946a4909bc,
problem_version_id 1142674b-fc92-4091-b8c4-e28e797e2865.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c6e782e7…

Theorem 2.4's proof: an antichain B ⊆ T_N(a) that avoids the root a "splits
uniquely as the disjoint union of antichains inside the child subtrees T_N(b),
b ∈ ch_N(a). Different child subtrees are pairwise incomparable, so the optimal
contributions add." This theorem formalizes that merge (the inductive core; the
full k-fold union follows by iterating this two-set version), where
    a ⪯ b  :=  ∃ t, b = a·t ∧ (∀ prime p, p ∣ t → a < p).

Given two ⪯-antichains B, C that are DISJOINT and pairwise ⪯-INCOMPARABLE (no
element of B precedes an element of C, and none of C precedes one of B — the
defining property of distinct child subtrees), the union B ∪ C is again a
⪯-antichain and the reciprocal weight is additive:
    Σ_{n∈B∪C} 1/n = Σ_{n∈B} 1/n + Σ_{n∈C} 1/n.

Combined with the root dichotomy (Erdos858_Thm24_RootDichotomy: any antichain in
a subtree is {a} or avoids a), this is the FULL combinatorial content of Theorem
2.4's proof — the "stop at a" (weight 1/a) versus "continue into pairwise-
incomparable children, contributions add" case split that yields
    F_N(a) = max(1/a, Σ_{b∈ch_N(a)} F_N(b)).
The value-function maximum itself reuses the M(N)-as-max-over-antichains layer
already verified for Corollary 3.5 (Erdos858_Cor35_MaxEq). Note this subtree DP
is an alternative to the (verified) frontier route M(N) = S_N(K).

Lean note: the antichain conclusion is a 4-way `rcases` on `Finset.mem_union`;
the two cross cases close by `absurd` against the incomparability hypotheses, and
the weight identity is exactly `Finset.sum_union` on the disjointness hypothesis.
-/
import Mathlib

namespace Erdos858

/-- Theorem 2.4 continue-branch: the union of two disjoint, pairwise-`⪯`-incomparable
`⪯`-antichains is a `⪯`-antichain with additive reciprocal weight. This is the paper's
"different child subtrees are pairwise incomparable, so the optimal contributions add." -/
theorem erdos858_thm24_children_merge :
    ∀ (B C : Finset ℕ),
      (∀ x ∈ B, ∀ y ∈ B, (∃ t, y = x * t ∧ ∀ p, Nat.Prime p → p ∣ t → x < p) → x = y) →
      (∀ x ∈ C, ∀ y ∈ C, (∃ t, y = x * t ∧ ∀ p, Nat.Prime p → p ∣ t → x < p) → x = y) →
      Disjoint B C →
      (∀ x ∈ B, ∀ y ∈ C, ¬ (∃ t, y = x * t ∧ ∀ p, Nat.Prime p → p ∣ t → x < p)) →
      (∀ x ∈ B, ∀ y ∈ C, ¬ (∃ t, x = y * t ∧ ∀ p, Nat.Prime p → p ∣ t → y < p)) →
      ((∀ x ∈ B ∪ C, ∀ y ∈ B ∪ C, (∃ t, y = x * t ∧ ∀ p, Nat.Prime p → p ∣ t → x < p) → x = y) ∧
        (∑ n ∈ B ∪ C, (1 : ℚ) / n) = (∑ n ∈ B, (1 : ℚ) / n) + (∑ n ∈ C, (1 : ℚ) / n)) := by
  intro B C hB hC hdisj hnoBC hnoCB
  refine ⟨?_, Finset.sum_union hdisj⟩
  intro x hx y hy hxy
  rw [Finset.mem_union] at hx hy
  rcases hx with hxB | hxC
  · rcases hy with hyB | hyC
    · exact hB x hxB y hyB hxy
    · exact absurd hxy (hnoBC x hxB y hyC)
  · rcases hy with hyB | hyC
    · exact absurd hxy (hnoCB y hyB x hxC)
    · exact hC x hxC y hyC hxy

end Erdos858
