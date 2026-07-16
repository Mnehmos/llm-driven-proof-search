import Mathlib

/-!
# Erdős #647 — shift classifications to the seven-form bundle

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  e84e00c6-17b8-43e4-a832-b40909cb576a
  episode_id          6dd68116-dbbc-45e8-871a-9b3ab8edab75
  root_statement_hash 2fbfb68c85117c41163b2c1acd682a353ea5cf1bac0e879976136c68b69f44c8
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    d133d0d1-397c-42f4-8437-07732df2296b (kernel_pass)
  result_artifact_hash 21565d7a79f59395e96d85a5e661e47ed7baed49c5880af5a1b5872213ee6496

This is the exact algebraic adapter from the campaign's verified shift
classifications at `1,2,3,4,6,8,12` to the seven-form hypotheses consumed by
the repaired-modulus candidate theorem.
-/

theorem erdos647_shift_outputs_to_seven_forms :
    ∀ (n N : ℕ), 1 ≤ N → n = 2520*N →
      ((n-12)/12).Prime →
      (((n-8)/8).Prime ∨ ∃ q : ℕ, q.Prime ∧ (n-8)/8 = 2*q) →
      ((n-6)/6).Prime →
      ((n-4)/4).Prime →
      ((n-3)/3).Prime →
      ((n-2)/2).Prime →
      (n-1).Prime →
      (210*N-1).Prime ∧
      ((315*N-1).Prime ∨ ∃ q : ℕ, q.Prime ∧ 315*N-1 = 2*q) ∧
      (420*N-1).Prime ∧
      (630*N-1).Prime ∧
      (840*N-1).Prime ∧
      (1260*N-1).Prime ∧
      (2520*N-1).Prime := by
  intro n N hN hn hp12 hp8 hp6 hp4 hp3 hp2 hp1
  have h12 : (n-12)/12 = 210*N-1 := by omega
  have h8 : (n-8)/8 = 315*N-1 := by omega
  have h6 : (n-6)/6 = 420*N-1 := by omega
  have h4 : (n-4)/4 = 630*N-1 := by omega
  have h3 : (n-3)/3 = 840*N-1 := by omega
  have h2 : (n-2)/2 = 1260*N-1 := by omega
  have h1 : n-1 = 2520*N-1 := by omega
  rw [h12] at hp12
  rw [h8] at hp8
  rw [h6] at hp6
  rw [h4] at hp4
  rw [h3] at hp3
  rw [h2] at hp2
  rw [h1] at hp1
  exact ⟨hp12, hp8, hp6, hp4, hp3, hp2, hp1⟩
