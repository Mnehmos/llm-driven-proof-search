import Mathlib

/-!
# Erdős #647 — logarithmic denominator bound after deleting 2

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  ce61fdf7-5644-428c-a1ac-f3c7b3b9a5e1
  episode_id          6be4d210-d956-481a-893c-9999bdcac1a1
  root_statement_hash 090c8da35d45ab27dc6f7ee42c12b2e2048edb54cf8a916be4b420106502378f
  outcome             kernel_verified (root_proved), second tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    783b4ca8-79ba-4499-96ce-b54561f2a28f (kernel_pass)
  result_artifact_hash 7ab1f1a699ca0625457df3a17534847039aa8734a4c0f12928adde6f92e7fcda

Any lower bound `B` for the original all-prime `nu` sum transfers to the
repaired Euler product with the exact fixed loss `1/2`.  Thus deleting `2`
does not change the seven-dimensional logarithmic exponent.
-/

theorem erdos647_repaired_logL_lower :
    ∀ (s : BoundingSieve) (z : ℕ) (B : ℝ), 7 ≤ z →
      s.prodPrimes =
        ∏ p ∈ (Finset.range (z+1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p →
      s.nu 2 = 1/2 → s.nu 3 = 0 → s.nu 5 = 0 → s.nu 7 = 0 →
      B ≤ ∑ p ∈ (Finset.Icc 1 z).filter Nat.Prime, s.nu p →
      B - 1/2 ≤
        Real.log (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹) := by
  intro s z B hz hprod hnu2 hnu3 hnu5 hnu7 hB
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
  have hsplit := Finset.sum_filter_add_sum_filter_not S Q s.nu
  rw [hactive, hdeleted] at hsplit
  have hsmall : (∑ p ∈ ({2,3,5,7} : Finset ℕ), s.nu p) = 1/2 := by
    norm_num [Finset.sum_insert, hnu2, hnu3, hnu5, hnu7]
  rw [hsmall] at hsplit
  have hBactive : B - 1/2 ≤ ∑ p ∈ A, s.nu p := by
    change B ≤ ∑ p ∈ S, s.nu p at hB
    linarith
  have hpf : s.prodPrimes.primeFactors = A := by
    rw [hprod]
    apply Nat.primeFactors_prod
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hlog : ∑ p ∈ s.prodPrimes.primeFactors, s.nu p ≤
      Real.log (∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹) := by
    rw [Real.log_prod]
    · apply Finset.sum_le_sum
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
      have hnu_pos : 0 < s.nu p := s.nu_pos_of_prime p hp_prime hp_dvd
      have hnu_lt1 : s.nu p < 1 := s.nu_lt_one_of_prime p hp_prime hp_dvd
      rw [Real.log_inv]
      have h1mx_pos : 0 < 1 - s.nu p := by linarith
      have hh := Real.log_le_sub_one_of_pos h1mx_pos
      linarith
    · intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp
      have hnu_lt1 : s.nu p < 1 := s.nu_lt_one_of_prime p hp_prime hp_dvd
      have h1mx_pos : 0 < 1 - s.nu p := by linarith
      exact inv_ne_zero h1mx_pos.ne'
  rw [hpf] at hlog
  rw [hpf]
  linarith
