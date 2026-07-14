/-
Erdős Problem #858 — the boundary ∂D of a continuation set is a ⪯-antichain.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §3, consequence of Proposition 3.4.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 96b1ceb3-2ae1-496f-a3fb-d1ef5cf3341a,
problem_version_id 887fea14-f2f4-4e47-8bf8-566ce45336e1.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 1a720a67…

For a ⪯-downward-closed continuation set D, its boundary ∂D = {n ≤ N : n ∉ D ∧
π n ∈ D} is a ⪯-antichain: for x, y ∈ ∂D with x < y, x ⋠ y. Proof: x ⪯ y with
x < y implies x ⪯ π(y) (hypothesis hchain — the ⪯-maximality of π from
Corollary 2.2: every proper ⪯-ancestor of y ⪯-precedes π(y)); since y ∈ ∂D,
π(y) ∈ D; and D is ⪯-downward-closed (hDclosed: z ⪯ w ∈ D ⇒ z ∈ D), so
x ⪯ π(y) ∈ D gives x ∈ D — contradicting x ∈ ∂D (x ∉ D). This makes every
continuation set's boundary a genuine admissible antichain (the objects M(N)
maximizes over), so Proposition 3.4's identity Σ_{∂D} 1/n = 1 + Σ_{a∈D} q_N(a)
bounds M(N) from below by 1 + Σ_{a∈D} q_N(a) for each D.
-/
import Mathlib

namespace Erdos858

/-- The boundary `∂D` of a `⪯`-downward-closed continuation set is a
`⪯`-antichain. `x ⪯ y := ∃ t, y = x*t ∧ ∀ prime p ∣ t, x < p`. -/
theorem boundary_antichain :
    ∀ (π : ℕ → ℕ) (N : ℕ) (D : Finset ℕ) (x y : ℕ),
      (∀ z w : ℕ, z < w → (∃ t : ℕ, w = z * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → z < p) →
        (∃ s : ℕ, π w = z * s ∧ ∀ p : ℕ, Nat.Prime p → p ∣ s → z < p)) →
      (∀ w : ℕ, w ∈ D → ∀ z : ℕ, (∃ s : ℕ, w = z * s ∧ ∀ p : ℕ, Nat.Prime p → p ∣ s → z < p) → z ∈ D) →
      x ∈ (Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D) →
      y ∈ (Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D) →
      x < y →
      ¬ (∃ t : ℕ, y = x * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → x < p) := by
  intro π N D x y hchain hDclosed hx hy hxy hxprey
  simp only [Finset.mem_filter] at hx hy
  have hxpiy := hchain x y hxy hxprey
  have hxD : x ∈ D := hDclosed (π y) hy.2.2 x hxpiy
  exact hx.2.1 hxD

end Erdos858
