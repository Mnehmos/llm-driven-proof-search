import Mathlib

/-!
# Erdős #647 — dyadic integer parameter bracket

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  9f1f4f3c-7665-4fc6-8d71-0a6120ae145e
  episode_id          cd7d60ab-82d3-4288-9b58-da5f3553a257
  root_statement_hash cfe2b3be87e35a6e6a6c88137f2282074d5b894fead1755dbfd4eaba758986c9
  outcome             kernel_verified (root_proved), 2 tracked attempts
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

An independent asynchronous verification job also returned `kernel_pass`:
  job_id              ad704f93-6a45-43e8-b095-8af494763dcc
  result_artifact_hash 3cbd7c971b8e820fd385f708aa0c1b890bc05035af0fd24db4bfbb2219376263

The witness is k=Nat.log (2^400) X. Thus z=2^k obeys the exact bracket
z^400≤X<(2z)^400, avoiding real roots and floors entirely.
-/

theorem erdos647_dyadic_parameter_bracket :
    ∀ X : ℕ, X ≠ 0 →
      ∃ k : ℕ, (2^k)^400 ≤ X ∧ X < (2*(2^k))^400 := by
  intro X hX
  let B : ℕ := 2^400
  let k : ℕ := Nat.log B X
  have hB : 1 < B := by
    dsimp [B]
    norm_num
  refine ⟨k, ?_, ?_⟩
  · calc
      (2^k)^400 = 2^(k*400) := by rw [pow_mul]
      _ = 2^(400*k) := by rw [Nat.mul_comm]
      _ = (2^400)^k := by rw [pow_mul]
      _ = B^k := by rfl
      _ ≤ X := by
        dsimp [k]
        exact Nat.pow_log_le_self B hX
  · have hu : X < B^k.succ := by
      simpa [k] using Nat.lt_pow_succ_log_self hB X
    calc
      X < B^k.succ := hu
      _ = (2^400)^k.succ := by rfl
      _ = 2^(400*k.succ) := by rw [pow_mul]
      _ = 2^(k.succ*400) := by rw [Nat.mul_comm]
      _ = (2^k.succ)^400 := by rw [pow_mul]
      _ = (2*(2^k))^400 := by
        have hpow : 2^k.succ = 2*(2^k) := by
          rw [pow_succ]
          exact Nat.mul_comm _ _
        rw [hpow]
