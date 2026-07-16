import Mathlib

/-!
# Erdős #647 — explicit polynomial error for R=(2z)^20

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  c64e7c8d-088b-4dc2-814f-a98bebd7dd7c
  episode_id          668f3e3f-190e-4b7d-9e23-c111482e2534
  root_statement_hash 1f78e550b89c6a39a159f2c6900d34e701ec2f34dbdd88fcb9eea4fcd4920bb7
  outcome             kernel_verified (root_proved), 3 tracked attempts
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

An independent asynchronous verification job also returned `kernel_pass`:
  job_id              2b19e092-2c5f-44de-a39f-5322b14e10ff
  result_artifact_hash da07dbfeae196fc1c2fe7c8c95fa68b031ca667f24a76514179007c846dfc70f

This is the explicit natural-number form of `(R²+1)^8=O(z^320)` for
R=(2z)^20, with the concrete constant 2^328.
-/

theorem erdos647_parameter_error_polynomial :
    ∀ z : ℕ, 1 ≤ z →
      ((((2*z)^20)^2 + 1)^8) ≤ 2^328 * z^320 := by
  intro z hz
  have hzbase : 1 ≤ 2*z := by omega
  have hzpow : 1 ≤ (2*z)^40 :=
    Nat.one_le_pow 40 (2*z) (by omega)
  have hsq : ((2*z)^20)^2 = (2*z)^40 := by
    rw [← pow_mul]
  have hbase : ((2*z)^20)^2 + 1 ≤ 2 * (2*z)^40 := by
    rw [hsq]
    omega
  calc
    ((((2*z)^20)^2 + 1)^8) ≤ (2 * (2*z)^40)^8 := by gcongr
    _ = 2^8 * ((2*z)^40)^8 := by rw [mul_pow]
    _ = 2^8 * (2*z)^320 := by rw [← pow_mul]
    _ = 2^8 * (2^320 * z^320) := by rw [mul_pow]
    _ = (2^8 * 2^320) * z^320 := by ac_rfl
    _ = 2^328 * z^320 := by rw [← pow_add]
