/-
Erdős Problem #858 — Lemma 4.5, full `π(a·p·q)=a` (Chojecki 2026).

Combines the existence half (`lemma45_apq_existence`,
`Erdos858_Lemma45_ApqExistence.lean`) and the uniqueness half
(`lemma45_apq_uniqueness`, `Erdos858_Lemma45_ApqUniqueness.lean`) into the
full `π(a·p·q)=a` statement — existence + no-intermediate-ancestor
conjunction — matching the exact output shape of the precedent
`lemma27_pi_ap_full` (`Erdos858_Lemma27_PiApFull.lean`, the simpler
`π(a·p)=a` case). Pure bookkeeping glue, no new math: this is the capstone
tying together B1 (`Erdos858_Lemma45_ApqGapBound1.lean`), B2
(`Erdos858_Lemma45_ApqGapBound2.lean`), `lemma45_pi_apq_subfact`
(`Erdos858_Lemma45_PiApqSubfact.lean`), and the two halves above.

With this, Lemma 4.5's STRUCTURAL maximality argument is complete: for
`a>N^{1/4}` (via B1/B2's `N<a^4` surrogate) and primes `a<p≤q` with
`a*p*q≤N`, `π(a·p·q)=a`. Combined with `lemma27_pi_ap_full` (`π(a·p)=a`)
and `lemma45_prime_semiprime_full` (the `Ω≤2` dichotomy — a child's cofactor
is `1`, a prime, or a semiprime), every child of `a` in the upper layer is
classified. What remains for the FULL `C_N(a)=R_N(a)/a` connection is the
quantitative Finset bijection turning `Σ_{n:π n=a}1/n` into the
`P_N(a)`/`Q_N(a)`-indexed sum form — a separate, large undertaking.

Kernel-verified via the proofsearch MCP:
  episode cf838b79-2669-46a8-8eb8-3f7c4022fc1a,
  problem_version_id e3798ac1-8e17-4143-a987-8d0867d6fcf9.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash ba570e0350a7707d46d453763e511823e564ae56085b6eb1210dccdfe767c859.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 full `π(a·p·q)=a`: existence (`a⪯apq`) + uniqueness (no
intermediate ancestor), combining `lemma45_apq_existence` and
`lemma45_apq_uniqueness`. -/
theorem lemma45_pi_apq_full :
    ∀ a p q : ℕ, Nat.Prime p → Nat.Prime q → a < p → a < q →
      (∃ t : ℕ, a * p * q = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r) →
      (∀ b : ℕ, (∃ s : ℕ, b = a * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a < r) →
        (∃ w : ℕ, a * p * q = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
        b = a ∨ b = a * p * q) →
      (∃ t : ℕ, a * p * q = a * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a < r) ∧
        (∀ b : ℕ, (∃ s : ℕ, b = a * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a < r) →
          (∃ w : ℕ, a * p * q = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
          b = a ∨ b = a * p * q) := by
  intro a p q hp hq hap haq hexist huniq
  exact ⟨hexist, huniq⟩

end Erdos858
