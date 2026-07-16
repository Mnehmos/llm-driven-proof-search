import Mathlib

/-!
# Erdős #647 — finite-prime correction for the repaired denominator

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  35439d12-2f15-43bd-81ce-2eabea637710
  episode_id          34fa55fc-ad48-4028-9a47-adc93bd12f1f
  root_statement_hash 7a62fdd6409e716383ae7beb65058b57665b8dbca26d8f1878a126db3088b1fc
  outcome             kernel_verified (root_proved), second tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    2b29d700-166d-4f96-9718-a2143828bab7 (kernel_pass)
  result_artifact_hash 948b3b148884eb263671453e55e433764d3af3e0eb2243026cac34d38247dff5

For a function with the concrete seven-form density values at `2,3,5,7`,
the repaired active-prime sum is exactly the all-prime sum minus `1/2`.
This is the finite correction needed to reuse the verified logarithmic
denominator-growth theorem after deleting `2` from the modulus.
-/

theorem erdos647_prime_sum_exclude_small :
    ∀ (z : ℕ) (f : ℕ → ℝ), 7 ≤ z →
      f 2 = 1/2 → f 3 = 0 → f 5 = 0 → f 7 = 0 →
      (∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, f p) =
        (∑ p ∈ (Finset.range (z+1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), f p) + 1/2 := by
  intro z f hz hf2 hf3 hf5 hf7
  set S := (Finset.Icc 1 z).filter Nat.Prime with hS
  set A := (Finset.range (z+1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7) with hA
  set Q : ℕ → Prop := fun p => p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7 with hQ
  have hactive : S.filter Q = A := by
    ext p
    simp only [S, A, Q, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_range]
    constructor
    · intro hp
      exact ⟨by omega, hp.1.2, hp.2.1, hp.2.2.1,
        hp.2.2.2.1, hp.2.2.2.2⟩
    · intro hp
      have hp2 : 2 ≤ p := hp.2.1.two_le
      have hp1 : 1 ≤ p := by omega
      exact ⟨⟨⟨hp1, by omega⟩, hp.2.1⟩,
        hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  have hdeleted : S.filter (fun p => ¬ Q p) = {2,3,5,7} := by
    ext p
    simp only [S, Q, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hp
      have hne := hp.2
      simpa only [not_and_or, not_ne_iff] using hne
    · intro hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨⟨⟨by norm_num, by omega⟩, by norm_num⟩, by simp⟩
      · exact ⟨⟨⟨by norm_num, by omega⟩, by norm_num⟩, by simp⟩
      · exact ⟨⟨⟨by norm_num, by omega⟩, by norm_num⟩, by simp⟩
      · exact ⟨⟨⟨by norm_num, by omega⟩, by norm_num⟩, by simp⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not S Q f
  rw [hactive, hdeleted] at hsplit
  have hsmall : (∑ p ∈ ({2,3,5,7} : Finset ℕ), f p) = 1/2 := by
    norm_num [Finset.sum_insert, hf2, hf3, hf5, hf7]
  rw [hsmall] at hsplit
  linarith
