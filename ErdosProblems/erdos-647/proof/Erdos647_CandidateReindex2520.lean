import Mathlib

/-!
# Erdős #647 — exact `n = 2520N` candidate reindexing

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  74892f8f-6612-4031-a686-23ba5be359dd
  episode_id          a7c81412-3be2-44f5-99d4-abbbaec604a3
  root_statement_hash 106d8dda7d5bd58ed14213ed8ac6ae176ccb35b0a1d10812950acd46d36b2a2a
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    69d29e28-ce31-4e86-8a78-2504d497faff (kernel_pass)
  result_artifact_hash a401feb39bf4a4c75b0e7baa704826291ca2397936582208de6267049144b899

This exact finite-set bijection moves the original counting variable `n` to
the seven-form parameter `N`.  It is predicate-generic, so the final theorem
can instantiate `P` with the Erdős #647 candidate condition without changing
the counting argument or losing a constant.
-/

theorem erdos647_candidate_reindex_2520 :
    ∀ (x : ℕ) (P : ℕ → Prop) [DecidablePred P],
      ((Finset.Icc 1 x).filter (fun n => 2520 ∣ n ∧ P n)).card =
        ((Finset.Icc 1 (x / 2520)).filter
          (fun N => P (2520 * N))).card := by
  intro x P inst
  apply Finset.card_bij (fun n _ => n / 2520)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    rcases hn with ⟨⟨hn1, hnx⟩, hdvd, hPn⟩
    obtain ⟨N, rfl⟩ := hdvd
    have hN1 : 1 ≤ N := by omega
    have hNx : N ≤ x / 2520 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2520)).2
      simpa [Nat.mul_comm] using hnx
    simpa using ⟨⟨hN1, hNx⟩, hPn⟩
  · intro n1 hn1 n2 hn2 heq
    simp only [Finset.mem_filter] at hn1 hn2
    rcases hn1.2.1 with ⟨a, rfl⟩
    rcases hn2.2.1 with ⟨b, rfl⟩
    simpa using heq
  · intro N hN
    simp only [Finset.mem_filter, Finset.mem_Icc] at hN
    rcases hN with ⟨⟨hN1, hNx⟩, hPN⟩
    have hle : 2520 * N ≤ x := by
      have hh :=
        (Nat.le_div_iff_mul_le (by norm_num : 0 < 2520)).1 hNx
      simpa [Nat.mul_comm] using hh
    refine ⟨2520 * N, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hle⟩, ⟨by simp, hPN⟩⟩
    · simp
