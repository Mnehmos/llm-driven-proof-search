import Mathlib

/-!
# Erdős #647 — candidate coprimality for the repaired modulus

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  d1d08312-eea8-443a-9ff2-78f6c63d0014
  episode_id          4c2d4160-9914-4d83-b649-6bc22d1f04d6
  root_statement_hash 3d8f14ca5dc6466efd34a526dba274fac3350e2647b16166b40599632f232726
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    11714104-9a12-4b96-b7e1-3cb13121f040 (kernel_pass)
  result_artifact_hash c6e26154efc6cac2b8e8c98bf6fc43f06e35c2612062f7131fcdd3e21a812b14

The hypotheses match the campaign's shift classifications: six forms are
prime, while `315N-1` is prime or twice a prime.  Excluding `2` from the
active product lets one argument cover both prime-chain families.  The range
condition `z < 157N` also puts the prime cofactor of `315N-1 = 2q` above `z`.
-/

theorem erdos647_repaired_modulus_candidate_coprime :
    ∀ (N z : ℕ), 1 ≤ N → z < 157*N →
      (210*N-1).Prime →
      ((315*N-1).Prime ∨ ∃ q : ℕ, q.Prime ∧ 315*N-1 = 2*q) →
      (420*N-1).Prime →
      (630*N-1).Prime →
      (840*N-1).Prime →
      (1260*N-1).Prime →
      (2520*N-1).Prime →
      Nat.Coprime
        (∏ p ∈ (Finset.range (z+1)).filter
          (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
        ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1)) := by
  intro N z hN hz h210 h315 h420 h630 h840 h1260 h2520
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
  have hn210 : ¬ p ∣ 210*N-1 :=
    noPrime _ h210 (by omega)
  have hn420 : ¬ p ∣ 420*N-1 :=
    noPrime _ h420 (by omega)
  have hn630 : ¬ p ∣ 630*N-1 :=
    noPrime _ h630 (by omega)
  have hn840 : ¬ p ∣ 840*N-1 :=
    noPrime _ h840 (by omega)
  have hn1260 : ¬ p ∣ 1260*N-1 :=
    noPrime _ h1260 (by omega)
  have hn2520 : ¬ p ∣ 2520*N-1 :=
    noPrime _ h2520 (by omega)
  have hn315 : ¬ p ∣ 315*N-1 := by
    rcases h315 with h315prime | ⟨r, hr, heq⟩
    · exact noPrime _ h315prime (by omega)
    · intro hdvd
      rw [heq] at hdvd
      rcases (hp.dvd_mul).mp hdvd with hp2 | hpr
      · have heq2 : p = 2 :=
          (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
        exact hpne2 heq2
      · have heqpr : p = r :=
          (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
        have hzr : z < r := by omega
        omega
  intro hforms
  simp only [hp.dvd_mul] at hforms
  tauto
