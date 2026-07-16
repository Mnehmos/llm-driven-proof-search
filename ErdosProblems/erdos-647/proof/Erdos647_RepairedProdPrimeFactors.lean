import Mathlib

/-!
# Erdős #647 — prime factors of the repaired active modulus

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  dd157db4-78e2-4285-8069-b6ce4ee14526
  episode_id          f307bb4a-7536-4cd5-aa06-4a570ed341f0
  root_statement_hash efe8ee4f7a731426d19c8df450b119aa2f170e57ba8c8d91489f3d854361750d
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    a655bad2-5fcb-4788-919a-468552c5491a (kernel_pass)
  result_artifact_hash e1b5f5f132c4a054642fa3d7ab91a413f3da5015f3ecef2b8fd0adc74731f076

This exact field alignment lets the generic Euler-product and logarithmic
denominator bounds consume the repaired active-prime sum directly.
-/

theorem erdos647_repaired_prod_primeFactors :
    ∀ z : ℕ,
      Nat.primeFactors
        (∏ p ∈ (Finset.range (z+1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p) =
        (Finset.range (z+1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7) := by
  intro z
  apply Nat.primeFactors_prod
  intro p hp
  exact (Finset.mem_filter.mp hp).2.1
