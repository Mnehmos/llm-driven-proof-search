/-
  Erdős problem #858 — cofactor large prime factor
  Paper ref: Chojecki 2026, §1–§2 (cofactor large prime factor).

  Every proper element above `a` in the relation
    x ⪯ y := ∃ t, y = x·t ∧ (∀ prime q ∣ t, x < q)
  is divisible by a prime exceeding `a`. Concretely: if a < b and a ⪯ b,
  then b has a prime factor p with a < p. (The cofactor t = b/a is ≥ 2,
  so it has a prime factor, and every prime factor of t exceeds a and
  divides b.) This is the mechanism behind admissibility of the top block
  and the prime–semiprime child structure.

  problem_version_id: 83089544-a3af-47bd-9ba6-8dd0306e2977
  episode_id:         de684f18-00f0-44e9-878e-4fc79c9e8af1
  outcome:            kernel_verified
  toolchain:          leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: c6083f605b1f0f3a4183a37dc7a9311e27c600b278c6e04e797e3aadef1bd736
-/
import Mathlib

namespace Erdos858

theorem cofactor_large_prime_factor :
    ∀ a b : ℕ, a < b → (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) → ∃ p : ℕ, Nat.Prime p ∧ a < p ∧ p ∣ b := by
  intro a b hab hex
  obtain ⟨t, hbt, ht⟩ := hex
  have ht1 : t ≠ 1 := by rintro rfl; rw [mul_one] at hbt; omega
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht1
  have hpb : p ∣ b := hpt.trans ⟨a, by rw [hbt]; ring⟩
  exact ⟨p, hp, ht p hp hpt, hpb⟩

end Erdos858
