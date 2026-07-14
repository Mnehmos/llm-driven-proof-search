/-
Erdős problem #858 — Chojecki 2026.
Paper ref: "a ⪯-antichain containing 1 is the singleton {1}".

atom:                 antichain_one_singleton
problem_version_id:   11ef8f61-cad5-4c60-9e6d-66d287a38858
episode_id:           4bcb8610-aa2c-4314-9d4d-76cea9b11f1b
outcome:              kernel_verified
toolchain:            leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
root_statement_hash:  711a54ecffc3fcdcaadbe6d12afbaf10328c2caa9a71f4e3400c0bf98c5a026c

Math: Define the divisibility-style preorder x ⪯ y := ∃ t, y = x * t ∧
(∀ prime p ∣ t, x < p). For any b we have 1 ⪯ b via the witness t = b:
indeed b = 1 * b (one_mul), and every prime p has 1 < p (Nat.Prime.one_lt),
so in particular every prime factor of t = b exceeds 1. Hence if a ⪯-antichain
B contains both 1 and b, the antichain condition applied to (1, b) forces 1 = b;
symmetry gives b = 1. So the only admissible antichain containing 1 is the
singleton {1} (weight 1), settling the 1 ∈ B edge case in the ≤ direction of the
max-closure duality (Corollary 3.5).
-/
import Mathlib

namespace Erdos858

theorem antichain_one_singleton :
    ∀ (B : Finset ℕ),
      (∀ x y : ℕ, x ∈ B → y ∈ B →
        (∃ t : ℕ, y = x * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → x < p) → x = y) →
      1 ∈ B → ∀ b : ℕ, b ∈ B → b = 1 := by
  intro B hAnti h1 b hb
  exact (hAnti 1 b h1 hb ⟨b, (one_mul b).symm, fun p hp _ => hp.one_lt⟩).symm

end Erdos858
