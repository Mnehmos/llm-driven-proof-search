/-
Erdős Problem #858 — Theorem 1.2 assembly, FULLY-ASSEMBLED literal π(a·p)=a (Chojecki 2026).

Reduces `literal_pi_value_ap` (`Erdos858_LiteralPiValueAp.lean`) to
genuinely primitive π-structure axioms (range, maximality, soundness) plus
the standalone `lemma27_pi_ap_full` theorem (existence+uniqueness for
`a·p`, needing only `1≤a,Prime p,a<p` — no `N`-dependency, no gap-bounds
needed since there is only one prime factor) plus `lemma21_sandwich` —
taken as opaque hypotheses. Companion to
`literal_pi_value_apq_fully_assembled`
(`Erdos858_LiteralPiValueApqFullyAssembled.lean`).

Proof: identical maximality→sandwich→uniqueness case-split logic, simpler
since `lemma27_pi_ap_full` directly supplies BOTH existence and uniqueness
in one call (no B1/B2/subfact needed).

Kernel-verified via the proofsearch MCP:
  episode 514da5c4-1fd6-4d77-88cc-e8a49b00685c,
  problem_version_id 3f0a8ee2-12a0-459c-a98b-87b21213d6e8.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7643147be4c727d99bbd0ec390d46186403173f8b97b90ebcb945f54e237b4c1.
-/
import Mathlib

namespace Erdos858

/-- Fully-assembled literal `π(a·p)=a`: needs only the range axiom,
maximality, soundness, plus `lemma21_sandwich` and `lemma27_pi_ap_full`
(opaque). -/
theorem literal_pi_value_ap_fully_assembled :
    ∀ (π : ℕ → ℕ) (N a p : ℕ), 1 ≤ a → Nat.Prime p → a < p → a * p ≤ N →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
      (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π n < r) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a' < r) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) →
      (∀ a' p' : ℕ, 1 ≤ a' → Nat.Prime p' → a' < p' →
        (∃ t : ℕ, a' * p' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) ∧
          (∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
            (∃ w : ℕ, a' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a' ∨ b = a' * p')) →
      π (a * p) = a := by
  intro π N a p ha hp hap hapN hax hmax hsound hsandwich hlemma27
  obtain ⟨hex, huniq⟩ := hlemma27 a p ha hp hap
  have hn2 : 2 ≤ a*p := (by nlinarith [hp.two_le, ha])
  have hrangeap : π (a*p) < a*p := (hax (a*p) hn2 hapN).2
  have han : a < a*p := (by nlinarith [hp.two_le, ha])
  have hale : a ≤ π (a*p) := hmax a (a*p) han hex
  rcases hale.lt_or_eq with hlt | heq
  · have hasand := hsandwich a (π (a*p)) (a*p) hlt hrangeap hex (hsound (a*p) hn2)
    rcases huniq (π (a*p)) hasand (hsound (a*p) hn2) with h1 | h1
    · exact h1
    · exfalso
      omega
  · exact heq.symm

end Erdos858
