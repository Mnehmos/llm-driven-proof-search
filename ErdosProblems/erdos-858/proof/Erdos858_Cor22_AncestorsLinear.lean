/-
Erdős Problem #858 — Corollary 2.2 (proper ancestors are linearly ordered).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Corollary 2.2.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 3975fa6a-43cf-4c5b-9fd7-bb541a4c6c14,
problem_version_id 6eecf4dd-9ed8-43f8-b17b-819f2cbe123a.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f960fc2c…

Paper statement: for any two proper ancestors a, b of n (a ⪯ n, b ⪯ n, both
< n), one has a ⪯ b or b ⪯ a. Hence the ancestors of any n form a chain, so
`π(n)` (the maximal proper ancestor) is well-defined and joining each n to
`π(n)` makes {1,…,N} a rooted tree with root 1 — the tree on which the whole
frontier / max-closure argument runs.

Proof: `lt_trichotomy` on a, b; whichever is smaller, apply Lemma 2.1 (proved
inline as the local `have sandwich`) to the sandwiched pair; the a = b case is
reflexivity of ⪯.
-/
import Mathlib

namespace Erdos858

/-- Corollary 2.2. With `x ⪯ y := ∃ t, y = x*t ∧ ∀ prime p ∣ t, x < p`:
any two proper ancestors of `n` are `⪯`-comparable. -/
theorem cor22_ancestors_linear :
    ∀ a b n : ℕ, a < n → b < n →
      (∃ u : ℕ, n = a * u ∧ ∀ p : ℕ, Nat.Prime p → p ∣ u → a < p) →
      (∃ v : ℕ, n = b * v ∧ ∀ p : ℕ, Nat.Prime p → p ∣ v → b < p) →
      (∃ t : ℕ, b = a * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) ∨
      (∃ t : ℕ, a = b * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → b < p) := by
  -- local copy of Lemma 2.1 (the sandwich lemma)
  have sandwich : ∀ a b n : ℕ, a < b → b < n →
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
  intro a b n han hbn hea heb
  rcases lt_trichotomy a b with hab | hab | hab
  · exact Or.inl (sandwich a b n hab hbn hea heb)
  · exact Or.inl ⟨1, (by rw [mul_one, hab]), fun p hp hpd => absurd (Nat.dvd_one.mp hpd) hp.ne_one⟩
  · exact Or.inr (sandwich b a n hab han heb hea)

end Erdos858
