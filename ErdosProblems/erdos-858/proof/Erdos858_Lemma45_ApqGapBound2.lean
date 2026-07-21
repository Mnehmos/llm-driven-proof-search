/-
Erdős Problem #858 — Lemma 4.5 connection, gap-bound sub-lemma B2 (Chojecki 2026).

Companion to `lemma45_apq_gap_bound1` (B1, `Erdos858_Lemma45_ApqGapBound1.lean`).
Pure ℕ arithmetic (no primality needed): for `a<p≤q`, `a*p*q≤N`, and `N<a^4`
(the nat surrogate for `a>N^{1/4}`), conclude `p<a*q`.

This is the key numeric fact ruling out `b=a*q` as a competing intermediate
ancestor in the `π(a·p·q)=a` maximality argument (Lemma 4.5).

Proof: by contradiction, assume `a*q≤p`. Then `(a*q)²≤(a*q)*p=a*p*q≤N<a^4`
(the `(a*q)*p=a*p*q` bridge needs an explicit `ring` step here, unlike B1,
since `(a*q)*p` and `a*p*q=(a*p)*q` are not syntactically identical). And
`a≤q` (from `a<p≤q`) gives `a^4=a²*a²≤a²*q²=(a*q)²`. Chaining gives
`a^4≤N`, contradicting `N<a^4` via `omega`.

Kernel-verified via the proofsearch MCP:
  episode c3c5b418-0e31-47e5-8592-df3a3c0aeb37,
  problem_version_id 22f8ad1e-a1f6-443f-a7bb-595daeb74483.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 720e15893aac6e7ea1a50a311d7d76f2ada0b82198ee626b53a367fa6c0af9e4.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 connection, gap-bound B2: `a<p≤q, a*p*q≤N, N<a^4 ⟹ p<a*q`. Pure
magnitude argument, no primality needed. Feeds the `π(a·p·q)=a` uniqueness
argument to rule out `a*q` as an intermediate ancestor. -/
theorem lemma45_apq_gap_bound2 :
    ∀ a p q N : ℕ, 1 ≤ a → a < p → p ≤ q → a * p * q ≤ N → N < a ^ 4 → p < a * q := by
  intro a p q N ha hap hpq hapqN hN4
  by_contra hcon
  push_neg at hcon
  have h1 : (a*q)*(a*q) ≤ (a*q)*p := (by gcongr)
  have h2 : (a*q)*p = a*p*q := (by ring)
  have h3 : (a*q)*(a*q) ≤ N := (by rw [h2] at h1; exact le_trans h1 hapqN)
  have hp2 : a^2 ≤ q^2 := Nat.pow_le_pow_left (by omega : a ≤ q) 2
  have h9 : a^4 ≤ (a*q)*(a*q) := (by have he1 : a^4 = a^2*a^2 := (by ring); have he2 : (a*q)*(a*q) = a^2*q^2 := (by ring); rw [he1, he2]; gcongr)
  have h10 : a^4 ≤ N := le_trans h9 h3
  omega

end Erdos858
