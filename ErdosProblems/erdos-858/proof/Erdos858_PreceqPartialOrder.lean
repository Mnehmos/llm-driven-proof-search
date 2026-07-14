/-
Erdős Problem #858 — the divisibility relation ⪯ is a partial order.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Introduction §1.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 147d5209-8be4-4e51-97ac-6ff2c023b439,
problem_version_id c2c1c39e-da39-4221-baa4-6dc68e718534.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
(env 9e26d28e…, import manifest aaf21893…). root_statement_hash 6a0381c5…

The paper defines, for positive integers,
    a ⪯ b  ⟺  b = a·t for some t with P⁻(t) > a
(P⁻ = least prime factor; the t = 1 case is b = a). Admissibility of a set A
for Erdős #858 is exactly "A is a ⪯-antichain". The paper asserts ⪯ is a
partial order. Here P⁻(t) > a is rendered faithfully as "every prime factor of
t exceeds a" (vacuous at t = 1). This theorem is the order-theoretic backbone
on which the paper's rooted tree, parent map π, and frontier/max-closure
machinery are built.
-/
import Mathlib

namespace Erdos858

/-- `⪯` is a partial order on the positive integers: reflexive, antisymmetric,
and transitive, with `a ⪯ b := ∃ t, b = a*t ∧ ∀ prime p ∣ t, a < p`. -/
theorem preceq_partial_order :
    (∀ a : ℕ, 1 ≤ a → ∃ t : ℕ, a = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) ∧
    (∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
        (∃ t : ℕ, a = b * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → b < p) → a = b) ∧
    (∀ a b c : ℕ, 1 ≤ b →
        (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
        (∃ t : ℕ, c = b * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → b < p) →
        ∃ t : ℕ, c = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact ⟨1, (mul_one a).symm, fun p hp hpd => absurd (Nat.dvd_one.mp hpd) hp.ne_one⟩
  · intro a b ha hb hab hba
    obtain ⟨u, hbeq, _⟩ := hab
    obtain ⟨s, haeq, _⟩ := hba
    exact Nat.dvd_antisymm ⟨u, hbeq⟩ ⟨s, haeq⟩
  · intro a b c hb hab hbc
    obtain ⟨u, hbeq, hu⟩ := hab
    obtain ⟨v, hceq, hv⟩ := hbc
    refine ⟨u * v, ?_, ?_⟩
    · rw [hceq, hbeq]; ring
    · intro p hp hpuv
      rcases (Nat.Prime.dvd_mul hp).mp hpuv with h | h
      · exact hu p hp h
      · exact lt_of_le_of_lt (Nat.le_of_dvd hb ⟨u, hbeq⟩) (hv p hp h)

end Erdos858
