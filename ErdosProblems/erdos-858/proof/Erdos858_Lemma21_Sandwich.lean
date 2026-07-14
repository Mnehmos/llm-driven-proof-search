/-
Erdős Problem #858 — Lemma 2.1 (the sandwich / linear-order lemma).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Lemma 2.1.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 2bf55db5-d2d8-405f-869a-a104a658e3f3,
problem_version_id 8d44c450-6c16-4b61-99e6-35150c9cd833.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash d211f115…

Paper statement: if a ⪯ n and b ⪯ n with a < b < n, then a ⪯ b. This forces
the proper ancestors of any n to be linearly ordered (Corollary 2.2), which is
exactly what makes the parent map π(n) := max proper ancestor well-defined and
turns {1,…,N} into a rooted tree — the foundation of the entire frontier /
max-closure argument.

Lean route (avoids the paper's per-prime valuation bookkeeping): a ∣ b follows
from coprimality — every prime dividing both a and v would be ≤ a and > b, a
contradiction, so `Nat.Coprime a v`, and then a ∣ n = b·v gives a ∣ b. Writing
b = a·t and cancelling a in a·u = b·v = a·(t·v) yields u = t·v, so every prime
factor of t divides u and hence (by hypothesis on u) exceeds a.
-/
import Mathlib

namespace Erdos858

/-- Lemma 2.1. With `x ⪯ y := ∃ t, y = x*t ∧ ∀ prime p ∣ t, x < p`:
if `a ⪯ n`, `b ⪯ n` and `a < b < n`, then `a ⪯ b`. -/
theorem lemma21_sandwich :
    ∀ a b n : ℕ, a < b → b < n →
      (∃ u : ℕ, n = a * u ∧ ∀ p : ℕ, Nat.Prime p → p ∣ u → a < p) →
      (∃ v : ℕ, n = b * v ∧ ∀ p : ℕ, Nat.Prime p → p ∣ v → b < p) →
      ∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p := by
  intro a b n hab hbn hu_ex hv_ex
  obtain ⟨u, hn_au, hu⟩ := hu_ex
  obtain ⟨v, hn_bv, hv⟩ := hv_ex
  have hn_pos : 0 < n := by omega
  have ha_pos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with ha0 | h
    · rw [ha0, Nat.zero_mul] at hn_au; omega
    · exact h
  have hcop : Nat.Coprime a v := Nat.coprime_of_dvd (fun p hp hpa hpv => by
    have h1 : p ≤ a := Nat.le_of_dvd ha_pos hpa
    have h2 : b < p := hv p hp hpv
    omega)
  have hadvd_n : a ∣ n := ⟨u, hn_au⟩
  have hadvd_bv : a ∣ b * v := by rw [← hn_bv]; exact hadvd_n
  have hab_dvd : a ∣ b := hcop.dvd_of_dvd_mul_right hadvd_bv
  obtain ⟨t, ht⟩ := hab_dvd
  refine ⟨t, ht, ?_⟩
  have h1 : a * u = a * (t * v) := by rw [← hn_au, hn_bv, ht]; ring
  have hutv : u = t * v := Nat.eq_of_mul_eq_mul_left ha_pos h1
  intro p hp hpt
  have hpu : p ∣ u := by rw [hutv]; exact hpt.mul_right v
  exact hu p hp hpu

end Erdos858
