/-
Erdős problem #858 — Chojecki 2026, Lemma 2.7 (prime child lemma), full π(a·p)=a.

For a ≥ 1 and prime p > a: a·p is a child of a (a ⪯ a·p, existence) AND the only
ancestors b with a ⪯ b ⪯ a·p are a and a·p (uniqueness), so π(a·p) = a.
Relation encoding: x ⪯ y := ∃ t, y = x·t ∧ (∀ prime r ∣ t, x < r).

  problem_version_id: 6b1c8420-abd6-49b0-9b97-805885a829e4
  episode_id:         33d2a806-acb9-495b-b143-aa300bc2e330
  outcome:            kernel_verified
  toolchain:          leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 22cf9b67b8e9f1097dcca1e82d6e2b6c6639b8d422ca182dfb76eeb9337ae596
-/
import Mathlib

namespace Erdos858

theorem lemma27_pi_ap_full : ∀ a p : ℕ, 1 ≤ a → Nat.Prime p → a < p → (∃ t : ℕ, a * p = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r) ∧ (∀ b : ℕ, (∃ s : ℕ, b = a * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a < r) → (∃ w : ℕ, a * p = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a ∨ b = a * p) := by
  intro a p ha hp hap
  constructor
  · refine ⟨p, rfl, ?_⟩
    intro r hr hrp
    rcases hp.eq_one_or_self_of_dvd r hrp with h | h
    · exact absurd h hr.ne_one
    · omega
  · intro b hb_ex hbap_ex
    obtain ⟨s, hbs, hs⟩ := hb_ex
    obtain ⟨w, hapbw, hw⟩ := hbap_ex
    have h1 : a * p = a * (s * w) := by rw [hapbw, hbs]; ring
    have hsw : p = s * w := Nat.eq_of_mul_eq_mul_left ha h1
    rcases hp.eq_one_or_self_of_dvd s ⟨w, hsw⟩ with hs1 | hsp
    · left; rw [hbs, hs1, Nat.mul_one]
    · right; rw [hbs, hsp]

end Erdos858
