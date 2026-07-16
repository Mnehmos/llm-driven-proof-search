import Mathlib

/-!
# Erdős #647 — certification of the R=(2z)^20 log-moment choice

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  d6c321da-fb33-46c9-b1eb-114a339d01b8
  episode_id          c7a9a71b-13be-4c5a-ab86-953c8d7e76c1
  root_statement_hash 7ed86d0c64adc313bc2f30c519577cf093fb1ec96ee833250cbd76a7475b7612
  outcome             kernel_verified (root_proved), 3 tracked attempts
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

An independent asynchronous verification job also returned `kernel_pass`:
  job_id              da465938-a7fa-4843-b7ff-f55eb30e94bd
  result_artifact_hash f1be3a159f0c7c805cb7c67cf6c06e48efac24aed2bf6767d6197c8f65c0ddf4

This certifies the exact numerical slack behind the deliberately loose
choice R=(2z)^20: for z≥2, the seven-form prime log-moment upper bound is
at most log(R)/2.
-/

theorem erdos647_parameter_R20_moment :
    ∀ z : ℝ, 2 ≤ z →
      7 * Real.log 4 * (1 + Real.log (z / 2)) ≤
        Real.log ((2*z)^20) / 2 := by
  intro z hz
  have hzdivpos : 0 < z / 2 := by positivity
  have hzdivone : 1 ≤ z / 2 := by linarith
  have hy : 0 ≤ Real.log (z / 2) := Real.log_nonneg hzdivone
  have ha : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2:ℝ)^2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlog4lt : Real.log 4 < 10 / 7 := by
    rw [hlog4]
    nlinarith [Real.log_two_lt_d9]
  have hcoef : 0 ≤ 10 - 7 * Real.log 4 := by linarith
  have hnonneg : 0 ≤ Real.log (z / 2) * (10 - 7 * Real.log 4) :=
    mul_nonneg hy hcoef
  have hmul : Real.log (2*z) = Real.log 4 + Real.log (z/2) := by
    have heq : (2:ℝ)*z = 4*(z/2) := by ring
    rw [heq, Real.log_mul (by norm_num) (ne_of_gt hzdivpos)]
  have hrhs : Real.log ((2*z)^20) / 2 =
      10 * (Real.log 4 + Real.log (z/2)) := by
    rw [Real.log_pow, hmul]
    ring
  rw [hrhs]
  nlinarith [hnonneg]
