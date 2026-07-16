import Mathlib

/-!
# Erdős #647 — dyadic error absorption at logarithmic scale

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  e74ace30-3fd0-4192-aea1-1f0f348f6e9b
  episode_id          52f39da0-0c91-4381-ba6b-6763044014e1
  root_statement_hash 7a3904890bde66411c6d2808eb1d5a8b1f7f81c0d5d6f9cc3f61061586d62a1e
  outcome             kernel_verified (root_proved), 2 tracked attempts
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

An independent asynchronous verification job also returned `kernel_pass`:
  job_id              73c7aabd-3e2a-46ba-a658-44967a15248f
  result_artifact_hash c88f46e45db7e0e2ffbcb80cc5e74dd6b1a61f257c637c95cdc410b431666ab4

For z=2^k this proves the error is already bounded at the exact
X/k^7 scale; the gap 400-(320+7)=73 absorbs the logarithmic factor.
-/

theorem erdos647_dyadic_error_log_scale :
    ∀ k X E : ℕ,
      (2^k)^400 ≤ X →
      E ≤ 2^328 * (2^k)^320 →
      E * k^7 ≤ 2^328 * X := by
  intro k X E hX hE
  have hk : k ≤ 2^k := by
    clear hX hE X E
    induction k with
    | zero => norm_num
    | succ k ih =>
        have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by norm_num)
        calc
          k+1 ≤ 2^k+1 := Nat.add_le_add_right ih 1
          _ ≤ 2^k+2^k := Nat.add_le_add_left hp _
          _ = 2^(k+1) := by rw [pow_succ, Nat.mul_two]
  have hk7 : k^7 ≤ (2^k)^7 := by gcongr
  have hexp : (2^k)^327 ≤ (2^k)^400 := by
    exact pow_le_pow_right' (Nat.one_le_pow k 2 (by norm_num)) (by norm_num)
  calc
    E * k^7 ≤ (2^328 * (2^k)^320) * k^7 := Nat.mul_le_mul_right _ hE
    _ ≤ (2^328 * (2^k)^320) * (2^k)^7 := Nat.mul_le_mul_left _ hk7
    _ = 2^328 * (2^k)^327 := by rw [mul_assoc, ← pow_add]
    _ ≤ 2^328 * (2^k)^400 := Nat.mul_le_mul_left _ hexp
    _ ≤ 2^328 * X := Nat.mul_le_mul_left _ hX
