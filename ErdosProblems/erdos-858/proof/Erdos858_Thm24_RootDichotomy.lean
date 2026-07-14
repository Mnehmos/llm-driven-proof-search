/-
Erdős Problem #858 — Theorem 2.4 (subtree recursion), combinatorial root-dichotomy core.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Theorem 2.4.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 22e685e6-7848-4d08-aaa9-fca499c835af,
problem_version_id 736ebc6b-1541-4ae3-8232-6702951f4073.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash b2c7f7d6…

For a ∈ ℕ let T_N(a) := {n ≤ N : a ⪯ n} be the subtree rooted at a, and
F_N(a) := max over ⪯-antichains B ⊆ T_N(a) of Σ_{n∈B} 1/n. Theorem 2.4 states
    F_N(a) = max(1/a, Σ_{b∈ch_N(a)} F_N(b)).
Its proof rests on the case split: "Any antichain B ⊆ T_N(a) either contains a —
in which case it contributes exactly 1/a — or else it avoids a and splits over
the child subtrees."

This theorem formalizes that root dichotomy IN FULL, on an abstract finite subtree
`T : Finset ℕ` whose root `a` is `⪯`-below every element (`a ⪯ n` for all n ∈ T —
the defining property of a subtree root), where
    a ⪯ b  :=  ∃ t, b = a·t ∧ (∀ prime p, p ∣ t → a < p).
It proves the two facts the paper's Theorem 2.4 proof uses:
  • {a} is itself a ⪯-antichain contained in T — the "stop at a" antichain that
    achieves weight 1/a;
  • every ⪯-antichain B ⊆ T is EITHER exactly {a} OR avoids a (a ∉ B).
The first branch is the root-collapse: if a ∈ B and a ⪯ x for every x ∈ T ⊇ B,
then antichain-ness forces a = x for all x ∈ B, so B = {a}.

Remaining half (deferred): the complementary additive decomposition of the
a-avoiding antichains over the child subtrees (T_N(a) = ⋃_{b∈ch_N(a)} T_N(b) with
pairwise-⪯-incomparable children, so the optimal contributions add to
Σ_{b} F_N(b)). That requires the parent/children tree structure (Lemma 2.3 π),
which the campaign has verified separately (concrete π); wiring it into the value
recursion is the follow-up to reach the full F_N(a) = max(1/a, Σ_b F_N(b)).
Note also that this DP route is an ALTERNATIVE to the (already kernel-verified)
frontier route: M(N) = F_N(1) = S_N(K) (Corollary 3.5).
-/
import Mathlib

namespace Erdos858

/-- Theorem 2.4 root dichotomy: on a finite subtree `T` with root `a` `⪯`-below
every element, `{a}` is a `⪯`-antichain in `T`, and every `⪯`-antichain `B ⊆ T`
is either exactly `{a}` (the weight-`1/a` "stop" antichain) or avoids `a`. This is
the case split at the heart of the subtree recursion `F_N(a) = max(1/a, Σ_b F_N(b))`. -/
theorem erdos858_thm24_root_dichotomy :
    ∀ (T : Finset ℕ) (a : ℕ),
      a ∈ T →
      (∀ n ∈ T, ∃ t, n = a * t ∧ ∀ p, Nat.Prime p → p ∣ t → a < p) →
      (({a} ⊆ T ∧
          (∀ x ∈ ({a} : Finset ℕ), ∀ y ∈ ({a} : Finset ℕ),
            (∃ t, y = x * t ∧ ∀ p, Nat.Prime p → p ∣ t → x < p) → x = y)) ∧
        (∀ B : Finset ℕ, B ⊆ T →
          (∀ x ∈ B, ∀ y ∈ B,
            (∃ t, y = x * t ∧ ∀ p, Nat.Prime p → p ∣ t → x < p) → x = y) →
          (B = {a} ∨ a ∉ B))) := by
  intro T a haT hmin
  refine ⟨⟨Finset.singleton_subset_iff.mpr haT, ?_⟩, ?_⟩
  · intro x hx y hy _
    rw [Finset.mem_singleton] at hx hy
    rw [hx, hy]
  · intro B hBT hanti
    by_cases haB : a ∈ B
    · left
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨haB, ?_⟩
      intro x hxB
      exact (hanti a haB x hxB (hmin x (hBT hxB))).symm
    · right
      exact haB

end Erdos858
