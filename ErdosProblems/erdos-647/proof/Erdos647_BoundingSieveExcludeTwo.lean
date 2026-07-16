import Mathlib

/-!
# Erdős #647 — finite-prime repair of the concrete BoundingSieve

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  96815907-c5f3-4be5-9e6b-15b1812c118d
  episode_id          5a05324a-c61b-4ae6-be26-5cc09c2e0d08
  root_statement_hash 0dd01bfe773a2a937b524312f3b7c61334442a224ec14f0c6eb0cabfd315a90c
  outcome             kernel_verified (root_proved), first tracked attempt
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  verification_job    dfdf65aa-da3c-4cb1-860c-1ad718e93ca8 (kernel_pass)
  result_artifact_hash 14a36723721e1b952a1bda1244e66383408d6845544df41e03f9d65a5bc3b88e

The candidate bridge must retain the odd-parameter Family B branch, for
which `315N-1` is twice a prime.  This theorem removes `2` from the active
prime product while preserving the seven-form support, unit weights, total
mass, and multiplicative density.  The `nu` axioms transfer from the old
instance because the repaired prime product is a subproduct of the old one.
-/

theorem erdos647_boundingSieve_exclude_two :
    ∀ (s : BoundingSieve) (X z : ℕ),
      s.prodPrimes =
        ∏ p ∈ (Finset.range (z+1)).filter
          (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p →
      s.nu = ArithmeticFunction.prodPrimeFactors
        (fun q : ℕ => (((Finset.range q).filter (fun r =>
          (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨
          (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨
          (2520*r)%q=1)).card : ℝ) / q) →
      ∃ s' : BoundingSieve,
        s'.support = (Finset.Icc 1 X).image
          (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
            (840*N-1)*(1260*N-1)*(2520*N-1)) ∧
        s'.prodPrimes =
          ∏ p ∈ (Finset.range (z+1)).filter
            (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p ∧
        s'.weights = (fun _ : ℕ => (1:ℝ)) ∧
        s'.totalMass = X ∧
        s'.nu = ArithmeticFunction.prodPrimeFactors
          (fun q : ℕ => (((Finset.range q).filter (fun r =>
            (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨
            (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨
            (2520*r)%q=1)).card : ℝ) / q) := by
  intro s X z hprod hnu
  have htoold : ∀ p : ℕ, p.Prime →
      p ∣ (∏ q ∈ (Finset.range (z+1)).filter
        (fun q => q.Prime ∧ q ≠ 2 ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7), q) →
      p ∣ (∏ q ∈ (Finset.range (z+1)).filter
        (fun q => q.Prime ∧ q ≠ 3 ∧ q ≠ 5 ∧ q ≠ 7), q) := by
    intro p hp hdvd
    simp only [hp.prime.dvd_finsetProd_iff, Finset.mem_filter,
      Finset.mem_range] at hdvd
    obtain ⟨q, hqmem, hqdvd⟩ := hdvd
    have heq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hqmem.2.1).mp hqdvd
    rw [heq]
    apply Finset.dvd_prod_of_mem (fun q : ℕ => q)
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hqmem.1, hqmem.2.1, hqmem.2.2.2.1,
      hqmem.2.2.2.2.1, hqmem.2.2.2.2.2⟩
  refine ⟨{
    support := (Finset.Icc 1 X).image
      (fun N => (210*N-1)*(315*N-1)*(420*N-1)*(630*N-1)*
        (840*N-1)*(1260*N-1)*(2520*N-1))
    prodPrimes := ∏ p ∈ (Finset.range (z+1)).filter
      (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p
    prodPrimes_squarefree := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        have hp' := Finset.mem_filter.mp hp
        have hq' := Finset.mem_filter.mp hq
        show IsRelPrime p q
        rw [← Nat.coprime_iff_isRelPrime]
        exact (Nat.coprime_primes hp'.2.1 hq'.2.1).mpr hpq
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        exact hp'.2.1.squarefree
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := X
    nu := ArithmeticFunction.prodPrimeFactors
      (fun q : ℕ => (((Finset.range q).filter (fun r =>
        (210*r)%q=1 ∨ (315*r)%q=1 ∨ (420*r)%q=1 ∨
        (630*r)%q=1 ∨ (840*r)%q=1 ∨ (1260*r)%q=1 ∨
        (2520*r)%q=1)).card : ℝ) / q)
    nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
    nu_pos_of_prime := by
      intro p hp hdvd
      have hold : p ∣ s.prodPrimes := by
        rw [hprod]
        exact htoold p hp hdvd
      have hh := s.nu_pos_of_prime p hp hold
      rw [hnu] at hh
      exact hh
    nu_lt_one_of_prime := by
      intro p hp hdvd
      have hold : p ∣ s.prodPrimes := by
        rw [hprod]
        exact htoold p hp hdvd
      have hh := s.nu_lt_one_of_prime p hp hold
      rw [hnu] at hh
      exact hh
  }, rfl, rfl, rfl, rfl, rfl⟩
