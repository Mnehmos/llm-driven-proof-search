/-
Erdős Problem #858 — Lemma 2.7 (prime child lemma), uniqueness core.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Lemma 2.7.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 861f5190-4a19-4286-b39e-3fc76bb3d3e9,
problem_version_id 246cfc11-2a7c-4df8-b3e1-1a01a0c0a353.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 840d98a3…

Paper statement: for a ≥ 1 and a prime p > a with a·p ≤ N, π(a·p) = a — that
is, a is the maximal proper ancestor of a·p; equivalently no ancestor lies
strictly between a and a·p. This is the divisibility heart of Lemma 2.7 (it
makes a·p a fresh child of a) and underlies the prime-child count
    C_N(a) ≥ (1/a) · Σ_{a<p≤N/a} 1/p
used throughout §4.

Here the uniqueness core is formalized without defining π: if a ⪯ b and
b ⪯ a·p then b = a or b = a·p. Proof: from a·p = b·w = a·s·w cancel a to get
p = s·w; primality of p forces s = 1 (⇒ b = a) or s = p (⇒ b = a·p).
-/
import Mathlib

namespace Erdos858

/-- Lemma 2.7 core. With `x ⪯ y := ∃ t, y = x*t ∧ ∀ prime q ∣ t, x < q`:
for `a ≥ 1` and a prime `p > a`, any `b` with `a ⪯ b ⪯ a*p` equals `a` or `a*p`.
So `a` has no proper ancestor strictly between it and `a*p` — i.e. `π(a*p) = a`. -/
theorem lemma27_prime_child_core :
    ∀ a p b : ℕ, 1 ≤ a → Nat.Prime p → a < p →
      (∃ s : ℕ, b = a * s ∧ ∀ q : ℕ, Nat.Prime q → q ∣ s → a < q) →
      (∃ w : ℕ, a * p = b * w ∧ ∀ q : ℕ, Nat.Prime q → q ∣ w → b < q) →
      b = a ∨ b = a * p := by
  intro a p b ha hp hap hb_ex hbap_ex
  obtain ⟨s, hbs, hs⟩ := hb_ex
  obtain ⟨w, hapbw, hw⟩ := hbap_ex
  have h1 : a * p = a * (s * w) := by rw [hapbw, hbs]; ring
  have hsw : p = s * w := Nat.eq_of_mul_eq_mul_left ha h1
  rcases hp.eq_one_or_self_of_dvd s ⟨w, hsw⟩ with hs1 | hsp
  · left; rw [hbs, hs1, Nat.mul_one]
  · right; rw [hbs, hsp]

end Erdos858
