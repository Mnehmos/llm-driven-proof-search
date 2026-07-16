import Mathlib

/-!
# Erdős #647 — active-prime parity obstruction

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  8057d050-084d-49ef-8be3-91be624a6e36
  episode_id          346e79fe-6366-49e3-b67d-0335655ca461
  root_statement_hash 318baf888e5c5753c02203ffe166b64f7da332a27e075d11bafe055527c7cca4
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    52a5d50a-6d71-4322-b730-7f995c89bab5 (kernel_pass)
  result_artifact_hash 8fd885bb7a177bf61fc730132d1376e2f4efc4f596cf75859300620f79bb68d0

For `z ≥ 2`, the original concrete active-prime product contains `2`.
Every odd parameter makes `315N-1` even, so the seven-form product is not
coprime to that modulus.  Thus this instance cannot count the odd-parameter
Family B branch until `2` is removed from the active-prime set.
-/

theorem erdos647_odd_parameter_rejected_by_two :
    ∀ (N z : ℕ), 2 ≤ z → Odd N →
      ¬ Nat.Coprime
        (∏ p ∈ (Finset.range (z+1)).filter
          (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
        ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
          (840*N-1)*(1260*N-1)*(2520*N-1)) := by
  intro N z hz hN
  have h2mem : 2 ∈ (Finset.range (z+1)).filter
      (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two, by norm_num, by norm_num, by norm_num⟩
  have hprod : 2 ∣ ∏ p ∈ (Finset.range (z+1)).filter
      (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p := by
    exact Finset.dvd_prod_of_mem (fun p : ℕ => p) h2mem
  rcases hN with ⟨k, hk⟩
  have h315 : 2 ∣ 315*N-1 := by
    refine ⟨315*k+157, ?_⟩
    omega
  have h12 : 2 ∣ (210*N-1)*(315*N-1) :=
    dvd_mul_of_dvd_right h315 _
  have h123 : 2 ∣ (210*N-1)*(315*N-1)*(420*N-1) :=
    dvd_mul_of_dvd_left h12 _
  have h1234 : 2 ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1) :=
    dvd_mul_of_dvd_left h123 _
  have h12345 : 2 ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
      (840*N-1) := dvd_mul_of_dvd_left h1234 _
  have h123456 : 2 ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
      (840*N-1)*(1260*N-1) := dvd_mul_of_dvd_left h12345 _
  have hforms : 2 ∣ (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
      (840*N-1)*(1260*N-1)*(2520*N-1) :=
    dvd_mul_of_dvd_left h123456 _
  intro hcop
  have hgcd : 2 ∣ Nat.gcd
      (∏ p ∈ (Finset.range (z+1)).filter
        (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
      ((210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
        (840*N-1)*(1260*N-1)*(2520*N-1)) :=
    Nat.dvd_gcd hprod hforms
  rw [hcop.gcd_eq_one] at hgcd
  norm_num at hgcd
