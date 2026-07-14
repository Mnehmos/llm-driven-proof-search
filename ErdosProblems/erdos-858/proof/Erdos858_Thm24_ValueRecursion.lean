/-
Erdős Problem #858 — Theorem 2.4 (subtree value recursion), max-split characterization.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Theorem 2.4.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 48bc8447-3df0-402c-9d53-6dfd2d54d08e,
problem_version_id b347c67d-e1f7-4c9e-977c-2f946f4ced56.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 563f3f7e0dc5dce4b0cc996be32b11ab3cc8beec1097941828968930be22a953.

For a ∈ ℕ let T_N(a) := {n ≤ N : a ⪯ n} be the subtree rooted at a under
    a ⪯ b := ∃ t, b = a·t ∧ (∀ prime p ∣ t, a < p),
and F_N(a) := max over ⪯-antichains B ⊆ T_N(a) of Σ_{n∈B} 1/n. Theorem 2.4:
    F_N(a) = max(1/a, Σ_{b∈ch_N(a)} F_N(b)).
Its proof rests on the root dichotomy — every ⪯-antichain of the subtree is
either {a} (contributing exactly 1/a) or avoids a (splitting over the pairwise-
⪯-incomparable child subtrees, whose contributions add).

This theorem expresses F_N(a) as `Finset.max'` of the achievable-weight set
    S := (T.powerset.filter Anti).image (fun B => Σ_{n∈B} 1/n)
of admissible ⪯-antichains of the subtree T, and proves the max-split
characterization F_N(a) = max(1/a, C), taken ABSTRACTLY over the structural facts
(mirroring the campaign's Corollary 3.5 technique, `cor35_max_eq`):
  • (i)   hi   — 1/a is achievable (the "stop at a" antichain {a}): (1/a) ∈ S;
  • (iii) hiii — the best a-avoiding weight C is achievable: C ∈ S;
  • (ii)  hii  — every achievable weight is bounded: ∀ x ∈ S, x ≤ max(1/a, C).
Then S.max' hne = max(1/a, C). The two combinatorial halves feeding (i)–(iii) are
already kernel-verified in this campaign: the root dichotomy that any ⪯-antichain
of the subtree rooted at a is {a} or a-avoiding (Erdos858_Thm24_RootDichotomy),
and additivity of disjoint pairwise-⪯-incomparable antichain unions
(Erdos858_Thm24_ChildrenMerge). Note this DP route is an ALTERNATIVE to the
(verified) frontier route M(N) = F_N(1) = S_N(K) (Erdos858_Cor35_MaxEq).

Proof: `le_antisymm`. The upper bound `S.max' hne ≤ max(1/a, C)` is `Finset.max'_le`
fed by (ii). For the lower bound, `max(1/a, C) ∈ S` by a `le_total` case split —
`max_eq_right`/`max_eq_left` land the max on C or 1/a, discharged by (iii)/(i) —
whence `Finset.le_max'` gives `max(1/a, C) ≤ S.max' hne` (the nonemptiness witness
aligns with `hne` by proof irrelevance). The defining hypothesis `_hS` pinning S to
the achievable-weight set is carried for faithfulness and unused by the argument.

Lean note: the image binder domain is annotated `fun (B : Finset ℕ) => …`; without
it the inlined `(n:ℚ)` coercion lets the elaborator infer `B : Finset ℚ`, clashing
with the `Finset (Finset ℕ)` source of `T.powerset.filter`.
-/
import Mathlib

namespace Erdos858

/-- Theorem 2.4 value recursion `F_N(a) = max(1/a, C)` as a `Finset.max'`
characterization of the achievable-weight set `S` of admissible `⪯`-antichains of
the subtree `T`: given `1/a` achievable (`hi`), the best a-avoiding weight `C`
achievable (`hiii`), and `max(1/a, C)` an upper bound (`hii`), the maximum of the
achievable-weight set equals `max(1/a, C)`. -/
theorem erdos858_thm24_value_recursion :
    ∀ (T : Finset ℕ) (a : ℕ) (C : ℚ) (Anti : Finset ℕ → Prop) (S : Finset ℚ),
      S = (@Finset.filter (Finset ℕ) (fun B => Anti B) (Classical.decPred _) T.powerset).image (fun (B : Finset ℕ) => ∑ n ∈ B, (1:ℚ)/(n:ℚ)) →
      ((1:ℚ)/(a:ℚ)) ∈ S →
      C ∈ S →
      (∀ x ∈ S, x ≤ max ((1:ℚ)/(a:ℚ)) C) →
      ∀ (hne : S.Nonempty), S.max' hne = max ((1:ℚ)/(a:ℚ)) C := by
  intro T a C Anti S _hS hi hiii hii hne
  have hmem : max ((1:ℚ)/(a:ℚ)) C ∈ S := by
    rcases le_total ((1:ℚ)/(a:ℚ)) C with h | h
    · rw [max_eq_right h]; exact hiii
    · rw [max_eq_left h]; exact hi
  exact le_antisymm (Finset.max'_le S hne (max ((1:ℚ)/(a:ℚ)) C) hii) (Finset.le_max' S (max ((1:ℚ)/(a:ℚ)) C) hmem)

end Erdos858
