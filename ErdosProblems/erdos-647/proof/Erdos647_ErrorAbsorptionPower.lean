import Mathlib

/-!
# Erdős #647 — exact fifth-power form of X^(4/5) error absorption

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  3544e7da-c8a9-4feb-844f-91be241dee92
  episode_id          88f161ad-0233-4381-aded-09f76a861a90
  root_statement_hash c02c2ab4543b320aef6f95f8b09474b90c684f139b2bad3fe5bd1f7fbc4f07e0
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

An independent asynchronous verification job also returned `kernel_pass`:
  job_id              8b5327c5-9a74-4c6b-992e-5a3c34ae13c3
  result_artifact_hash ef957e8b3c3e96a093277e6f028e760ab2a7d4c1c8c75b6e6522a6ce1c84f667

The fifth-power inequality is an exact integer encoding of
E≤2^328·X^(4/5), avoiding fractional powers in the parameter assembly.
-/

theorem erdos647_error_absorption_power :
    ∀ E z X : ℕ,
      E ≤ 2^328 * z^320 →
      z^400 ≤ X →
      E^5 ≤ 2^1640 * X^4 := by
  intro E z X hE hz
  have hzpow : z^1600 ≤ X^4 := by
    calc
      z^1600 = (z^400)^4 := by rw [← pow_mul]
      _ ≤ X^4 := by gcongr
  calc
    E^5 ≤ (2^328 * z^320)^5 := by gcongr
    _ = (2^328)^5 * (z^320)^5 := by rw [mul_pow]
    _ = 2^1640 * z^1600 := by rw [← pow_mul, ← pow_mul]
    _ ≤ 2^1640 * X^4 := Nat.mul_le_mul_left _ hzpow
