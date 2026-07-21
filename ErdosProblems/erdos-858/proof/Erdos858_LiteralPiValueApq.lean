/-
Erdős Problem #858 — literal π-value at `a·p·q` (Chojecki 2026).

Specializes `pi_value_bridge` (`Erdos858_PiValueBridge.lean`) to `n:=a·p·q`,
giving the literal `π(a·p·q)=a` from `lemma45_pi_apq_full`'s existence+
uniqueness conjunction plus soundness/range/maximality/sandwich. Companion
to `literal_pi_value_ap` (`Erdos858_LiteralPiValueAp.lean`), needed for the
`C_N(a)=R_N(a)/a` Finset-bijection's Stage A.

Proof: identical to `pi_value_bridge`'s tactic sequence, specialized at the
fixed instantiation `n:=a·p·q`.

Kernel-verified via the proofsearch MCP:
  episode 2ea24d57-2004-4a1b-bc9b-951bee81c925,
  problem_version_id 8cbb484b-3e19-436c-a524-3e326fbb359a.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 9954e4c545a46ee7e47e7218af5d290009b87c5b57509d97233142f4a9ccac33.
-/
import Mathlib

namespace Erdos858

/-- Literal π-value at `a·p·q`: `π(a·p·q)=a`, specializing `pi_value_bridge`. -/
theorem literal_pi_value_apq :
    ∀ (π : ℕ → ℕ) (a p q : ℕ), a < a * p * q →
      (∃ t : ℕ, a * p * q = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r) →
      (∀ b : ℕ, (∃ t : ℕ, b = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r) →
        (∃ t : ℕ, a * p * q = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r) → b = a ∨ b = a * p * q) →
      (∃ t : ℕ, a * p * q = π (a * p * q) * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π (a * p * q) < r) →
      π (a * p * q) < a * p * q →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a' < r) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) →
      π (a * p * q) = a := by
  intro π a p q han hex huniq hsound hrange hmax hsandwich
  have hale : a ≤ π (a*p*q) := hmax a (a*p*q) han hex
  rcases hale.lt_or_eq with hlt | heq
  · have hasand : ∃ t : ℕ, π (a*p*q) = a*t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r := hsandwich a (π (a*p*q)) (a*p*q) hlt hrange hex hsound
    rcases huniq (π (a*p*q)) hasand hsound with h1 | h1
    · exact h1
    · exfalso
      omega
  · exact heq.symm

end Erdos858
