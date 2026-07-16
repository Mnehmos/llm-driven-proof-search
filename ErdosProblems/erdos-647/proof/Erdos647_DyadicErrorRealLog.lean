import Mathlib

/-!
# Erdős #647 — real-log form of dyadic error absorption

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  23d21971-6676-40d0-99cb-556e22be189b
  episode_id          a4646056-f6af-462c-be5f-1fee2bd03727
  root_statement_hash 1d46a1c91a58507998f972e21cb91ba9e851a1a5a91546556d6da7a211140420
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

An independent asynchronous verification job also returned `kernel_pass`:
  job_id              c22fe351-17d9-4436-99d6-30ba2cf08782
  result_artifact_hash 182ee9ed5fdb1a6a46ad4615a24b39c872b22fb5bcdee714d917c18e87420620

This is the direct real-analytic form of the dyadic natural inequality,
using the exact identity log(2^k)=k·log 2.
-/

theorem erdos647_dyadic_error_real_log :
    ∀ k X E : ℕ, 0 < k →
      E * k^7 ≤ 2^328 * X →
      (E:ℝ) ≤
        ((2:ℝ)^328 * (Real.log 2)^7 * (X:ℝ)) /
          (Real.log (((2^k : ℕ):ℝ)))^7 := by
  intro k X E hk h
  have hR : (E:ℝ) * (k:ℝ)^7 ≤ (2:ℝ)^328 * (X:ℝ) := by
    exact_mod_cast h
  have hcast : (((2^k : ℕ):ℝ)) = (2:ℝ)^k := by norm_cast
  have hlog : Real.log (((2^k : ℕ):ℝ)) = (k:ℝ) * Real.log 2 := by
    rw [hcast, Real.log_pow]
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < (Real.log (((2^k : ℕ):ℝ)))^7 := by
    rw [hlog]
    positivity
  apply (le_div_iff₀ hden).2
  rw [hlog]
  calc
    (E:ℝ) * ((k:ℝ) * Real.log 2)^7 =
        ((E:ℝ) * (k:ℝ)^7) * (Real.log 2)^7 := by ring
    _ ≤ ((2:ℝ)^328 * (X:ℝ)) * (Real.log 2)^7 :=
      mul_le_mul_of_nonneg_right hR (pow_nonneg (le_of_lt hlog2) 7)
    _ = (2:ℝ)^328 * (Real.log 2)^7 * (X:ℝ) := by ring
