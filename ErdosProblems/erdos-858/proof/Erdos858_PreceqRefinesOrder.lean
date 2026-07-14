/-
Erdős problem #858 — Chojecki 2026, §1–§2 order compatibility.

Basic order facts for the relation  x ⪯ y := ∃ t, y = x·t ∧ (∀ prime p ∣ t, x < p):
  (i)   ⪯ refines divisibility:  a ⪯ b ⇒ a ∣ b.
  (ii)  ⪯ refines ≤:            a ⪯ b with b > 0 ⇒ a ≤ b.
  (iii) a proper ⪯-step doubles: a ⪯ b with 1 ≤ a and a < b ⇒ 2a ≤ b (cofactor t ≥ 2).

problem_version_id: 21e5ccab-0cf4-4f6d-b44b-5ea28a465975
episode_id:         9f15836c-4bfc-42b8-a900-4abaa44eea18
outcome:            kernel_verified
toolchain:          leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
root_statement_hash: cf1a49e0c6c0542afddf70cd308f6556b2c0a1ebb22c336b45d24a9f1e9383ac
-/
import Mathlib

namespace Erdos858

theorem preceq_refines_order :
    (∀ a b : ℕ, (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) → a ∣ b) ∧ (∀ a b : ℕ, 0 < b → (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) → a ≤ b) ∧ (∀ a b : ℕ, 1 ≤ a → a < b → (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) → 2 * a ≤ b) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a b ⟨t, hbt, -⟩
    exact ⟨t, hbt⟩
  · rintro a b hb ⟨t, hbt, -⟩
    exact Nat.le_of_dvd hb ⟨t, hbt⟩
  · rintro a b ha hab ⟨t, hbt, ht⟩
    have hb : 0 < b := by omega
    have ht1 : t ≠ 1 := by rintro rfl; rw [mul_one] at hbt; omega
    have ht0 : t ≠ 0 := by rintro rfl; rw [mul_zero] at hbt; omega
    have ht2 : 2 ≤ t := by omega
    calc 2 * a = a * 2 := by ring
      _ ≤ a * t := Nat.mul_le_mul (le_refl a) ht2
      _ = b := hbt.symm

end Erdos858
