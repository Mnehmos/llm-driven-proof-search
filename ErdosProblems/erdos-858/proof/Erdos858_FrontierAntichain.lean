/-
Erdős Problem #858 — Lemma 3.1 (the frontier is an antichain).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Lemma 3.1.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode b89eb944-9f1f-419b-ab63-5f66512c8fe8,
problem_version_id de5b09fd-6784-4364-9f51-9be70b696a54.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 1cfe83b0…

The frontier A_N(K) = {n ≤ N : π(n) ≤ K < n} is a ⪯-antichain: if x, y ∈ A_N(K)
with x < y then x ⋠ y (x ⪯ y := ∃ t, y = x·t ∧ ∀ prime p ∣ t, x < p). Proof:
x ⪯ y with x < y makes x a proper ancestor of y, so by π-maximality (the
Corollary 2.2 property that every proper ⪯-ancestor z of m satisfies z ≤ π m)
x ≤ π y ≤ K; but x ∈ A_N(K) gives K < x, a contradiction.

Proved by an ultracode subagent; verified first submission.
-/
import Mathlib

namespace Erdos858

/-- Lemma 3.1. Under π-maximality (`z ⪯ m` proper `⇒ z ≤ π m`), two distinct
frontier vertices `x < y` are `⪯`-incomparable: `x ⋠ y`. -/
theorem frontier_antichain :
    ∀ (π : ℕ → ℕ) (N K x y : ℕ),
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → z < p) → z ≤ π m) →
      x ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n) →
      y ∈ (Finset.Icc 1 N).filter (fun n => π n ≤ K ∧ K < n) →
      x < y →
      ¬ (∃ t : ℕ, y = x * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → x < p) := by
  intro π N K x y hmax hx hy hxy hpre
  simp only [Finset.mem_filter] at hx hy
  obtain ⟨-, -, hx2⟩ := hx
  obtain ⟨-, hy1, -⟩ := hy
  have h1 : x ≤ π y := hmax x y hxy hpre
  omega

end Erdos858
