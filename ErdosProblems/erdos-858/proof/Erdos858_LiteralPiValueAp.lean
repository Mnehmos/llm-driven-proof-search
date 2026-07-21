/-
Erdős Problem #858 — literal π-value at `a·p` (Chojecki 2026).

Specializes `pi_value_bridge` (`Erdos858_PiValueBridge.lean`) to `n:=a·p`,
giving the literal `π(a·p)=a` from `lemma27_pi_ap_full`'s existence+
uniqueness conjunction plus soundness/range/maximality/sandwich. Needed for
the `C_N(a)=R_N(a)/a` Finset-bijection's Stage A (characterizing the filter
set `{n:π n=a}` as a union of images).

Proof: identical to `pi_value_bridge`'s tactic sequence, specialized at the
fixed instantiation `n:=a·p` (can't cross-reference the standalone theorem
across problem_versions).

Kernel-verified via the proofsearch MCP:
  episode ada2c6f4-394b-46e8-9da4-26cb0f51ef7e,
  problem_version_id 845f0189-eb32-441f-8ed5-751e6cce1d4e.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 3fdf31580af18f48f484da3ae7375246b3961eb7191d4b4452ec366e5fa11bf8.
-/
import Mathlib

namespace Erdos858

/-- Literal π-value at `a·p`: `π(a·p)=a`, specializing `pi_value_bridge`. -/
theorem literal_pi_value_ap :
    ∀ (π : ℕ → ℕ) (a p : ℕ), a < a * p →
      (∃ t : ℕ, a * p = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r) →
      (∀ b : ℕ, (∃ t : ℕ, b = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r) →
        (∃ t : ℕ, a * p = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r) → b = a ∨ b = a * p) →
      (∃ t : ℕ, a * p = π (a * p) * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π (a * p) < r) →
      π (a * p) < a * p →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a' < r) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) →
      π (a * p) = a := by
  intro π a p han hex huniq hsound hrange hmax hsandwich
  have hale : a ≤ π (a*p) := hmax a (a*p) han hex
  rcases hale.lt_or_eq with hlt | heq
  · have hasand : ∃ t : ℕ, π (a*p) = a*t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r := hsandwich a (π (a*p)) (a*p) hlt hrange hex hsound
    rcases huniq (π (a*p)) hasand hsound with h1 | h1
    · exact h1
    · exfalso
      omega
  · exact heq.symm

end Erdos858
