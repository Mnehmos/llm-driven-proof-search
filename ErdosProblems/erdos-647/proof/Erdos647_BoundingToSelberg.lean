import Mathlib

/-!
# Erdős #647 — `BoundingSieve` to `SelbergSieve` adapter

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  a1095c68-7d6f-4e6a-91ad-894d73d35863
  episode_id          e993eb52-c42d-43ba-88d9-f7a147ec2b6f
  root_statement_hash fcaef0ed5c3c0fe5416bcb3fe4291a300d525c6d116727ed1825badc22c6c6f5
  outcome             kernel_verified (root_proved), second tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    4a86bbf8-af0d-49fc-83af-f0a7fd91bd09 (kernel_pass)
  result_artifact_hash 6eadfff85bc6507c9bd194ba913c27991a06187c788fb63f50bd6029a929ca6d

Mathlib's `SelbergSieve` adds only a positive level to a `BoundingSieve`.
This adapter promotes the parity-repaired concrete instance to the analytic
API while preserving the complete underlying sieve definitionally.
-/

theorem erdos647_boundingSieve_to_selbergSieve :
    ∀ (s : BoundingSieve) (R : ℕ), 1 ≤ R →
      ∃ t : SelbergSieve, t.toBoundingSieve = s ∧ t.level = R := by
  intro s R hR
  have hRreal : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast hR
  exact ⟨{
    toBoundingSieve := s
    level := R
    one_le_level := hRreal
  }, rfl, rfl⟩
