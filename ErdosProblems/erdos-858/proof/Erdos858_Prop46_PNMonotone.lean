/-
Erdős problem #858 — Chojecki 2026, Proposition 4.6 (upper-layer monotonicity),
prime-sum part.

Atom: prop46_PN_monotone
Campaign: erdos-858

Statement formalized: for `0 < a ≤ b`, the reciprocal-prime-sum
  P_N(a) := Σ_{p ∈ (a, N], a·p ≤ N} 1/p
is nonincreasing in `a`, i.e. `P_N(a) ≥ P_N(b)`.

This is exactly the P_N half of the paper's `R_N(a) = P_N(a) + Q_N(a)`
upper-layer monotonicity claim (Prop 4.6); the domain avoids division by
using the equivalent integer condition `a * p ≤ N` in place of `p ≤ N / a`.

Proof idea: for `a ≤ b`, the b-filtered domain
  { p ∈ Icc (b+1) N | Prime p ∧ b * p ≤ N }
is a subset of the a-filtered domain
  { p ∈ Icc (a+1) N | Prime p ∧ a * p ≤ N },
since `b < p` and `a ≤ b` give `a < p`, and `a * p ≤ b * p ≤ N`. All summands
`1/p` are nonnegative, so the sum over the smaller (b-)domain is bounded above
by the sum over the larger (a-)domain, i.e. `P_N(a) ≥ P_N(b)`.

Provenance:
  problem_version_id : a8c19f95-14f8-460e-b6cf-7b09b3f9e0d0
  root_statement_hash : b519e0ad5f46183b28896119e47ed57a2d6878f845dea44460dccf07ddd0ec7f
  episode_id          : df3913fc-746e-44c6-b82b-9efde1a7d348
  outcome             : kernel_verified (termination_reason = root_proved, 1 submission)
  toolchain           : leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  fidelity_status     : attested (unsafe_dev_attestation=true — not a certified review)
-/
import Mathlib

namespace Erdos858

theorem prop46_PN_monotone :
    ∀ N a b : ℕ, 0 < a → a ≤ b →
      (∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℚ)/(p:ℚ)) ≥
      (∑ p ∈ (Finset.Icc (b+1) N).filter (fun p => Nat.Prime p ∧ b * p ≤ N), (1:ℚ)/(p:ℚ)) := by
  intro N a b ha hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨h1, h2⟩, hprime, hle⟩ := hp
    refine ⟨⟨by omega, h2⟩, hprime, ?_⟩
    calc a * p ≤ b * p := by gcongr
      _ ≤ N := hle
  · intro p _ _
    positivity

end Erdos858
