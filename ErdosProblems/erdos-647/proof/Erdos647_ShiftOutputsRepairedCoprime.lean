import Mathlib

/-!
# Erdős #647 — shift outputs to repaired-modulus coprimality

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  5570a9ac-16d7-42ad-9c06-7a2a16e5d30d
  episode_id          4cae8930-9352-4158-8873-6caeff3939ce
  root_statement_hash 243afd8aa13511b4a00d551e016769fe46ae52da8e73e0a1a0de0978596ec8fa
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    9111417d-0b5b-4645-bfce-9980eb16f780 (kernel_pass)
  result_artifact_hash 3026b113e9c8c8e0ba6d7f2575fafed972857878e2482bbcbbd12ff87378e88b

This closes the concrete candidate-side seam.  The seven shift outputs under
`n = 2520N` imply coprimality of the seven-form product with the repaired
active-prime modulus.  The shift-8 `2 * prime` branch needs no separate
family argument because active prime `2` has been removed.
-/

theorem erdos647_shift_outputs_repaired_coprime :
    ∀ (n N z : ℕ), 1 ≤ N → n = 2520 * N → z < 157 * N →
      ((n - 12) / 12).Prime →
      (((n - 8) / 8).Prime ∨
        ∃ q : ℕ, q.Prime ∧ (n - 8) / 8 = 2 * q) →
      ((n - 6) / 6).Prime →
      ((n - 4) / 4).Prime →
      ((n - 3) / 3).Prime →
      ((n - 2) / 2).Prime →
      (n - 1).Prime →
      Nat.Coprime
        (∏ p ∈ (Finset.range (z + 1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
        ((210 * N - 1) * (315 * N - 1) * (420 * N - 1) *
          (630 * N - 1) * (840 * N - 1) * (1260 * N - 1) *
          (2520 * N - 1)) := by
  intro n N z hN hn hz hp12 hp8 hp6 hp4 hp3 hp2 hp1
  have h12 : (n - 12) / 12 = 210 * N - 1 := by omega
  have h8 : (n - 8) / 8 = 315 * N - 1 := by omega
  have h6 : (n - 6) / 6 = 420 * N - 1 := by omega
  have h4 : (n - 4) / 4 = 630 * N - 1 := by omega
  have h3 : (n - 3) / 3 = 840 * N - 1 := by omega
  have h2 : (n - 2) / 2 = 1260 * N - 1 := by omega
  have h1 : n - 1 = 2520 * N - 1 := by omega
  rw [h12] at hp12
  rw [h8] at hp8
  rw [h6] at hp6
  rw [h4] at hp4
  rw [h3] at hp3
  rw [h2] at hp2
  rw [h1] at hp1
  apply Nat.coprime_of_dvd
  intro p hp hpmod
  simp only [hp.prime.dvd_finsetProd_iff, Finset.mem_filter,
    Finset.mem_range] at hpmod
  obtain ⟨q, hqmem, hpq⟩ := hpmod
  have hpqeq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp hqmem.2.1).mp hpq
  subst q
  have hpz : p ≤ z := by omega
  have hpne2 : p ≠ 2 := hqmem.2.2.1
  have noPrime : ∀ r : ℕ, r.Prime → z < r → ¬ p ∣ r := by
    intro r hr hzr hdvd
    have heq : p = r :=
      (Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd
    omega
  have hn210 : ¬ p ∣ 210 * N - 1 :=
    noPrime _ hp12 (by omega)
  have hn420 : ¬ p ∣ 420 * N - 1 :=
    noPrime _ hp6 (by omega)
  have hn630 : ¬ p ∣ 630 * N - 1 :=
    noPrime _ hp4 (by omega)
  have hn840 : ¬ p ∣ 840 * N - 1 :=
    noPrime _ hp3 (by omega)
  have hn1260 : ¬ p ∣ 1260 * N - 1 :=
    noPrime _ hp2 (by omega)
  have hn2520 : ¬ p ∣ 2520 * N - 1 :=
    noPrime _ hp1 (by omega)
  have hn315 : ¬ p ∣ 315 * N - 1 := by
    rcases hp8 with hp315 | ⟨r, hr, heq⟩
    · exact noPrime _ hp315 (by omega)
    · intro hdvd
      rw [heq] at hdvd
      rcases (hp.dvd_mul).mp hdvd with hp2' | hpr
      · have heq2 : p = 2 :=
          (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2'
        exact hpne2 heq2
      · have heqpr : p = r :=
          (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
        have hzr : z < r := by omega
        omega
  intro hforms
  simp only [hp.dvd_mul] at hforms
  tauto
