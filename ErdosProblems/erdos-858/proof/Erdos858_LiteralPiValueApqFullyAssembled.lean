/-
Erdős Problem #858 — Theorem 1.2 assembly, FULLY-ASSEMBLED literal π(a·p·q)=a (Chojecki 2026).

Reduces `literal_pi_value_apq` (`Erdos858_LiteralPiValueApq.lean`) to
genuinely primitive π-structure axioms (the range axiom `hax`, maximality
`hmax`, soundness `hsound`) plus standalone number-theory theorems
(`lemma21_sandwich`, the gap-bounds B1/B2, `lemma45_pi_apq_subfact`,
`lemma45_apq_uniqueness`) — taken as opaque hypotheses representing their
FULL theorems — rather than needing the pre-derived existence+uniqueness
conjunction or the gap-bound CONCLUSIONS (`q<a·p`, `p<a·q`) supplied
externally. Uses `hax` (N-bounded range) INSTEAD of a free-floating
`hrange`, since `N` is already available for B1/B2.

Proof: derives existence inline (`lemma45_apq_existence`'s exact body),
calls `huniqapq` (the opaque `lemma45_apq_uniqueness`) with B1/B2's
freshly-computed conclusions, then runs `pi_value_bridge`'s maximality→
sandwich→uniqueness case-split logic inline (adapted from
`Erdos858_PiValueBridge.lean`). Splices FIVE previously-separate proof
bodies into one; verified on the FIRST submission.

Kernel-verified via the proofsearch MCP:
  episode 4a5fcc01-4cd4-45f3-a0b3-47142e825801,
  problem_version_id 3167ef61-7531-4a5b-a835-3ec45dc04a93.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 509f1cd446e320a6d432d1bda27a451462a71b21a29176b12e458c4212934784.
-/
import Mathlib

namespace Erdos858

/-- Fully-assembled literal `π(a·p·q)=a`: needs only the range axiom,
maximality, soundness, plus the standalone sandwich/gap-bound/subfact/
uniqueness theorems (opaque) — not the pre-derived existence+uniqueness
conjunction or gap-bound conclusions. -/
theorem literal_pi_value_apq_fully_assembled :
    ∀ (π : ℕ → ℕ) (N a p q : ℕ), 1 ≤ a → Nat.Prime p → Nat.Prime q → a < p → p ≤ q → a * p * q ≤ N → N < a ^ 4 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
      (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π n < r) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a' < r) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → a' * p' * q' ≤ N' → N' < a' ^ 4 → q' < a' * p') →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → p' ≤ q' → a' * p' * q' ≤ N' → N' < a' ^ 4 → p' < a' * q') →
      (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
      (∀ a' p' q' : ℕ, 1 ≤ a' → Nat.Prime p' → Nat.Prime q' → a' < p' → p' ≤ q' →
        q' < a' * p' → p' < a' * q' →
        (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        ∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
          (∃ w : ℕ, a' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
          b = a' ∨ b = a' * p' * q') →
      π (a * p * q) = a := by
  intro π N a p q ha hp hq hap hpq hapqN hN4 hax hmax hsound hsandwich hB1 hB2 hsubfact huniqapq
  have haq : a < q := by omega
  have hB1' : q < a*p := hB1 a p q N ha hap hapqN hN4
  have hB2' : p < a*q := hB2 a p q N ha hap hpq hapqN hN4
  have hex : ∃ t : ℕ, a * p * q = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r := ⟨p*q, (by ring), fun r hr hrpq => ((Nat.Prime.dvd_mul hr).mp hrpq).elim (fun hrp => by rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp hrp]; exact hap) (fun hrq => by rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp hrq]; exact haq)⟩
  have huniq := huniqapq a p q ha hp hq hap hpq hB1' hB2' hsubfact
  have hn2 : 2 ≤ a*p*q := (by nlinarith [hp.two_le, hq.two_le, ha])
  have hrangeapq : π (a*p*q) < a*p*q := (hax (a*p*q) hn2 hapqN).2
  have han : a < a*p*q := (by nlinarith [hp.two_le, hq.two_le, ha])
  have hale : a ≤ π (a*p*q) := hmax a (a*p*q) han hex
  rcases hale.lt_or_eq with hlt | heq
  · have hasand : ∃ t : ℕ, π (a*p*q) = a*t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r := hsandwich a (π (a*p*q)) (a*p*q) hlt hrangeapq hex (hsound (a*p*q) hn2)
    rcases huniq (π (a*p*q)) hasand (hsound (a*p*q) hn2) with h1 | h1
    · exact h1
    · exfalso
      omega
  · exact heq.symm

end Erdos858
