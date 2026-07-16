import Erdos647_ParameterR20Moment
import Erdos647_PrimeLogDivUpper
import Erdos647_SevenTupleAdmissibility

/-!
# Erdős #647 — concrete repaired-sieve logarithmic moment

This is the field adapter from the exposed seven-form density to the generic
half-denominator theorem.  It proves the actual active-prime moment is bounded
by the explicit prime harmonic estimate, and then certifies the choice
`R = (2z)^20`.
-/

theorem erdos647_concrete_log_moment_upper
    (s : SelbergSieve) (z : ℕ) (hz : 2 ≤ z)
    (hprod : s.prodPrimes =
      ∏ p ∈ (Finset.range (z + 1)).filter
        (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
    (hnu : s.nu = ArithmeticFunction.prodPrimeFactors
      (fun q : ℕ => (((Finset.range q).filter (fun r =>
        (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
        (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
        (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
        (2520 * r) % q = 1)).card : ℝ) / q)) :
    (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) ≤
      7 * Real.log 4 * (1 + Real.log ((z : ℝ) / 2)) := by
  let A := (Finset.range (z + 1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7)
  let S := (Finset.Icc 1 z).filter Nat.Prime
  have hpf : s.prodPrimes.primeFactors = A := by
    rw [hprod]
    apply Nat.primeFactors_prod
    intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  have hAS : A ⊆ S := by
    intro p hp
    simp only [A, S, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.2.1.one_le, by omega⟩, hp.2.1⟩
  have hterm : ∀ p ∈ A,
      s.nu p * Real.log p ≤ 7 * (Real.log p / (p : ℝ)) := by
    intro p hpA
    simp only [A, Finset.mem_filter, Finset.mem_range] at hpA
    rcases hpA with ⟨hpz, hpprime, hp2, hp3, hp5, hp7ne⟩
    have hp7 : 7 < p := by
      by_contra hnot
      have hle : p ≤ 7 := Nat.le_of_not_gt hnot
      have hpge2 := hpprime.two_le
      have hp_cases :
          p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
        omega
      rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hp2 rfl
      · exact hp3 rfl
      · norm_num at hpprime
      · exact hp5 rfl
      · norm_num at hpprime
      · exact hp7ne rfl
    have hcnt := (erdos647_seventuple_admissible_general p hpprime hp7).2
    have hnuval : s.nu p =
        (((Finset.range p).filter (fun r =>
          (210 * r) % p = 1 ∨ (315 * r) % p = 1 ∨
          (420 * r) % p = 1 ∨ (630 * r) % p = 1 ∨
          (840 * r) % p = 1 ∨ (1260 * r) % p = 1 ∨
          (2520 * r) % p = 1)).card : ℝ) / p := by
      rw [hnu, ArithmeticFunction.prodPrimeFactors_apply hpprime.ne_zero,
        hpprime.primeFactors, Finset.prod_singleton]
    rw [hnuval]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hcntR :
        (((Finset.range p).filter (fun r =>
          (210 * r) % p = 1 ∨ (315 * r) % p = 1 ∨
          (420 * r) % p = 1 ∨ (630 * r) % p = 1 ∨
          (840 * r) % p = 1 ∨ (1260 * r) % p = 1 ∨
          (2520 * r) % p = 1)).card : ℝ) ≤ 7 := by
      exact_mod_cast hcnt
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    calc
      _ ≤ (7 / (p : ℝ)) * Real.log p := by
        gcongr
      _ = 7 * (Real.log p / (p : ℝ)) := by ring
  have hsumAS :
      (∑ p ∈ A, Real.log p / (p : ℝ)) ≤
        ∑ p ∈ S, Real.log p / (p : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hAS
    intro p hpS hpA
    have hpprime : p.Prime := (Finset.mem_filter.mp hpS).2
    positivity
  have hprime := erdos647_prime_log_div_upper (z : ℝ) (by exact_mod_cast hz)
  have hprimeS :
      (∑ p ∈ S, Real.log p / (p : ℝ)) ≤
        Real.log 4 * (1 + Real.log ((z : ℝ) / 2)) := by
    simpa [S] using hprime
  rw [hpf]
  calc
    (∑ p ∈ A, s.nu p * Real.log p) ≤
        ∑ p ∈ A, 7 * (Real.log p / (p : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = 7 * ∑ p ∈ A, Real.log p / (p : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ 7 * ∑ p ∈ S, Real.log p / (p : ℝ) := by gcongr
    _ ≤ 7 * (Real.log 4 * (1 + Real.log ((z : ℝ) / 2))) := by gcongr
    _ = 7 * Real.log 4 * (1 + Real.log ((z : ℝ) / 2)) := by ring

theorem erdos647_concrete_log_moment_R20
    (s : SelbergSieve) (z : ℕ) (hz : 2 ≤ z)
    (hprod : s.prodPrimes =
      ∏ p ∈ (Finset.range (z + 1)).filter
        (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
    (hnu : s.nu = ArithmeticFunction.prodPrimeFactors
      (fun q : ℕ => (((Finset.range q).filter (fun r =>
        (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
        (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
        (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
        (2520 * r) % q = 1)).card : ℝ) / q)) :
    (∑ p ∈ s.prodPrimes.primeFactors, s.nu p * Real.log p) ≤
      Real.log ((((2 * z) ^ 20 : ℕ) : ℝ)) / 2 := by
  calc
    _ ≤ 7 * Real.log 4 * (1 + Real.log ((z : ℝ) / 2)) :=
      erdos647_concrete_log_moment_upper s z hz hprod hnu
    _ ≤ Real.log ((2 * (z : ℝ)) ^ 20) / 2 :=
      erdos647_parameter_R20_moment (z : ℝ) (by exact_mod_cast hz)
    _ = Real.log ((((2 * z) ^ 20 : ℕ) : ℝ)) / 2 := by norm_num
