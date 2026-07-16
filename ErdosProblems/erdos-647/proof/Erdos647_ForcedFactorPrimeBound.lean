import Mathlib

/-!
# Erdős #647 — forced factor + primality bounds the parameter (Engine A, layer 1)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-16.

  problem_version_id  d6abd6d9-6408-40ab-8f61-7a43d8ded5c7
  episode_id          92b32ec3-18e7-4807-91a1-71a47c10e9fb
  root_statement_hash 6f05c1d58ae39a6762606ba29443231d4e91605f67b4cfe18c1704babfa7a23c
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     9962b6c3-5450-44c5-8cc7-5d2aceec5bf9 (kernel_pass)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the elimination mechanism for nonzero-determinant pair
interactions. If one terminal leaf forces `p ∣ L(N)` for an affine form
`L(N)=a·N+b` while a shape demand forces `L(N)` prime, then `L(N)=p`
exactly and the candidate parameter is bounded, `N ≤ p`:

  `1 ≤ a → 1 < p → p ∣ a·N+b → Prime(a·N+b) → a·N+b = p ∧ N ≤ p`

Combined with `erdos647_affine_determinant_interaction`, this converts
every nonzero-determinant leaf-pair collision into a FINITE equation:
a shared prime `p` must divide the fixed determinant `Δ`, the primality
shape then forces `L(N) = p ≤ |Δ|`, hence `N ≤ |Δ|` — excluded for all
large parameters, certifiable by a single computation per pair.

This is the branch-closing engine the compatibility-graph program uses
to draw its incompatibility edges.
-/

theorem erdos647_forced_factor_prime_bound :
    ∀ (a b N p : ℕ), 1 ≤ a → 1 < p → p ∣ a * N + b →
      Nat.Prime (a * N + b) → a * N + b = p ∧ N ≤ p := by
  intro a b N p ha hp hdvd hprime
  have heq : a * N + b = p := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h1 | h2
    · omega
    · omega
  refine ⟨heq, ?_⟩
  have : a * N ≤ p := by omega
  have : 1 * N ≤ a * N := Nat.mul_le_mul_right N ha
  omega
