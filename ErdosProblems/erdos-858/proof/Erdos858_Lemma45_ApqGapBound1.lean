/-
Erdős Problem #858 — Lemma 4.5 connection, gap-bound sub-lemma B1 (Chojecki 2026).

Pure ℕ arithmetic (no primality needed): for `a<p`, `a*p*q≤N`, and `N<a^4`
(the nat surrogate for `a>N^{1/4}`, matching the convention of
`Erdos858_Lemma45_CofactorPrimeSemiprime.lean`), conclude `q<a*p`.

This is the key numeric fact ruling out `b=a*p` as a competing intermediate
ancestor in the `π(a·p·q)=a` maximality argument (Lemma 4.5): it lets
`lemma45_pi_apq_subfact` (`Erdos858_Lemma45_PiApqSubfact.lean`, already
verified — no `t` with `(a*p)*q'=(a*p)*t` and every prime factor of `t`
exceeding `a*p`, given `q'<a*p`) apply directly at `b:=a*p`, `q':=q`.

Proof: by contradiction, assume `a*p≤q`. Then `(a*p)²≤(a*p)*q=a*p*q≤N<a^4`.
But `a≤p` (from `a<p`) gives `a²≤p²` (`Nat.pow_le_pow_left`), hence
`a^4=a²*a²≤a²*p²=(a*p)²`. Chaining: `a^4≤(a*p)²≤N`, contradicting `N<a^4`
via `omega` (treating `a^4` as a matching opaque atom in both hypotheses).
No primality of `p`,`q` is used — the bound is a pure magnitude argument.

Kernel-verified via the proofsearch MCP:
  episode 81156e5e-5604-4c24-a645-d0ee8b3f1855,
  problem_version_id 6fe4b7ed-dc12-4918-b59b-5c1e2311c9e8.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 045df5d024106f747dd58704b4de43d81d258cb494bd5e1cb5c1756dc3c1fbb3.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 connection, gap-bound B1: `a<p, a*p*q≤N, N<a^4 ⟹ q<a*p`. Pure
magnitude argument, no primality needed. Feeds `lemma45_pi_apq_subfact` at
`b:=a*p` to rule out `a*p` as an intermediate ancestor of `a*p*q`. -/
theorem lemma45_apq_gap_bound1 :
    ∀ a p q N : ℕ, 1 ≤ a → a < p → a * p * q ≤ N → N < a ^ 4 → q < a * p := by
  intro a p q N ha hap hapqN hN4
  by_contra hcon
  push_neg at hcon
  have h1 : (a*p)*(a*p) ≤ (a*p)*q := (by gcongr)
  have h3 : (a*p)*(a*p) ≤ N := le_trans h1 hapqN
  have hap' : a ≤ p := le_of_lt hap
  have hp2 : a^2 ≤ p^2 := Nat.pow_le_pow_left hap' 2
  have h9 : a^4 ≤ (a*p)*(a*p) := (by have he1 : a^4 = a^2*a^2 := (by ring); have he2 : (a*p)*(a*p) = a^2*p^2 := (by ring); rw [he1, he2]; gcongr)
  have h10 : a^4 ≤ N := le_trans h9 h3
  omega

end Erdos858
