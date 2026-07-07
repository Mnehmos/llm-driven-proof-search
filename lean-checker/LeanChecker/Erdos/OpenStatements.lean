import Mathlib

/-!
# Erdős corpus — faithful statements of OPEN problems

Formalizing (statement only) a few **open** problems from the Erdős corpus,
in the pinned toolchain. These are `sorry` — the point is a faithful, typechecking
Lean statement of the frontier, not a proof. Each elaborates under
lean4:v4.32.0-rc1 + mathlib@360da6fa.

Companion to `CorpusValidation.lean` (solved, kernel-verified). Verify these
typecheck with `lake env lean LeanChecker/Erdos/OpenStatements.lean` — the only
warnings are the intended `sorry`s.

Numbering follows erdosproblems.com where stable; the phrasing mirrors the
google-deepmind/formal-conjectures conventions (an `answer(sorry) ↔ …` shape
would be used there for unknown-answer problems; here we state the conjectured
form directly and leave the proof open).
-/

namespace LeanChecker.Erdos.OpenStatements

/-! ## Erdős–Straus conjecture (open)

For every integer `n ≥ 2`, the fraction `4/n` is a sum of three positive unit
fractions `1/a + 1/b + 1/c`. Verified for enormous ranges of `n`; open in
general. -/
theorem erdos_straus : ∀ n : ℕ, 2 ≤ n →
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ (4 : ℚ) / n = 1 / a + 1 / b + 1 / c := by
  sorry

/-! ## Erdős problem 1 — distinct subset sums (open)

If `A ⊆ {1, …, N}` has all subset sums distinct, must `N ≫ 2^{|A|}`? The
powers of two `{1, 2, 4, …}` show `2^{|A|}` is the right order; the conjecture
is a matching lower bound `N ≥ c · 2^{|A|}`. Only the weaker `N ≫ 2^n / n`
(and refinements) is known. -/
theorem erdos_1_distinct_subset_sums :
    ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      (fun S : A.powerset => (S.1.sum id)).Injective →
      N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

/-! ## Erdős–Turán conjecture on additive bases (open)

If `A ⊆ ℕ` is an additive basis of order 2 — every `n` is a sum of two
elements of `A` — then the representation function `n ↦ #{(a,b) : a,b ∈ A,
a+b = n}` is unbounded. One of the most famous open problems in additive
combinatorics. -/
theorem erdos_turan_additive_basis (A : Set ℕ)
    (hbasis : ∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ A, a + b = n) :
    ∀ C : ℕ, ∃ n : ℕ,
      C < Nat.card {p : ℕ × ℕ // p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} := by
  sorry

end LeanChecker.Erdos.OpenStatements
