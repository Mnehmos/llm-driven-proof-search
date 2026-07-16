import Erdos647_LEqProd
import Erdos647_NuEqSevenDivP
import Erdos647_PrimeEulerProductLower
import Erdos647_RepairedProdPrimeFactors

/-!
# Erdős #647 — concrete seventh-power Selberg denominator

The active Euler product omits only the five primes `2,3,5,7,11` from
the comparison product.  Their full Mertens factor is exactly `77/16`.
For every remaining active prime, Bernoulli's inequality gives

`(1 - 7/p)⁻¹ ≥ ((1 - 1/p)⁻¹)^7`.

Together with the finite Euler-product/harmonic lower bound this yields an
effective constant times `(log z)^7`, without invoking an asymptotic prime
number theorem.
-/

namespace Erdos647

theorem concrete_selberg_denominator_lower
    (t : SelbergSieve) (z : ℕ) (hz : 11 ≤ z)
    (hprod : t.prodPrimes =
      ∏ p ∈ (Finset.range (z + 1)).filter
        (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p)
    (hnu : t.nu = ArithmeticFunction.prodPrimeFactors
      (fun q : ℕ => (((Finset.range q).filter (fun r =>
        (210 * r) % q = 1 ∨ (315 * r) % q = 1 ∨
        (420 * r) % q = 1 ∨ (630 * r) % q = 1 ∨
        (840 * r) % q = 1 ∨ (1260 * r) % q = 1 ∨
        (2520 * r) % q = 1)).card : ℝ) / q)) :
    ((16 : ℝ) / 77) ^ 7 * (Real.log (z : ℝ)) ^ 7 ≤
      ∑ l ∈ t.prodPrimes.divisors, t.selbergTerms l := by
  let F := (Finset.range (z + 1)).filter Nat.Prime
  let S : Finset ℕ := {2, 3, 5, 7, 11}
  let A := (Finset.range (z + 1)).filter
    (fun p => p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7)
  let B := F \ S
  have hpf : t.prodPrimes.primeFactors = A := by
    rw [hprod]
    exact erdos647_repaired_prod_primeFactors z
  have hSF : S ⊆ F := by
    intro p hp
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        omega
      · norm_num
  have hsmall :
      (∏ p ∈ S, (1 - ((p : ℝ)⁻¹))⁻¹) = (77 : ℝ) / 16 := by
    norm_num [S]
  have hEuler := harmonic_sum_le_prime_euler_product z
  have hlogharm :
      Real.log ((z + 1 : ℕ) : ℝ) ≤
        ∑ n ∈ Finset.Icc 1 z, ((n : ℝ)⁻¹) := by
    simpa [harmonic_eq_sum_Icc] using log_add_one_le_harmonic z
  have hlogmono :
      Real.log (z : ℝ) ≤ Real.log ((z + 1 : ℕ) : ℝ) := by
    gcongr
    omega
  have hlogEuler :
      Real.log (z : ℝ) ≤
        ∏ p ∈ F, (1 - ((p : ℝ)⁻¹))⁻¹ := by
    exact hlogmono.trans (hlogharm.trans (by simpa [F] using hEuler))
  have hdecomp :
      (∏ p ∈ B, (1 - ((p : ℝ)⁻¹))⁻¹) * ((77 : ℝ) / 16) =
        ∏ p ∈ F, (1 - ((p : ℝ)⁻¹))⁻¹ := by
    rw [← hsmall]
    exact Finset.prod_sdiff hSF
  have hBLower :
      ((16 : ℝ) / 77) * Real.log (z : ℝ) ≤
        ∏ p ∈ B, (1 - ((p : ℝ)⁻¹))⁻¹ := by
    nlinarith [hlogEuler]
  have hBA : B ⊆ A := by
    intro p hp
    have hpF := (Finset.mem_sdiff.mp hp).1
    have hpS := (Finset.mem_sdiff.mp hp).2
    simp only [F, Finset.mem_filter, Finset.mem_range] at hpF
    simp only [S, Finset.mem_insert, Finset.mem_singleton, not_or] at hpS
    simp only [A, Finset.mem_filter, Finset.mem_range]
    exact ⟨hpF.1, hpF.2, hpS.1, hpS.2.1, hpS.2.2.1, hpS.2.2.2.1⟩
  have hfactor : ∀ p ∈ B,
      ((1 - ((p : ℝ)⁻¹))⁻¹) ^ 7 ≤ (1 - t.nu p)⁻¹ := by
    intro p hpB
    have hpF := (Finset.mem_sdiff.mp hpB).1
    have hpS := (Finset.mem_sdiff.mp hpB).2
    have hpPrime : p.Prime := (Finset.mem_filter.mp hpF).2
    have hp11 : p ≠ 11 := by
      intro heq
      apply hpS
      simp [S, heq]
    have hp7 : 7 < p := by
      by_contra hnot
      have hle : p ≤ 7 := Nat.le_of_not_gt hnot
      have hpge := hpPrime.two_le
      have hpCases : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
        omega
      rcases hpCases with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hpS (by simp [S])
      · exact hpS (by simp [S])
      · norm_num at hpPrime
      · exact hpS (by simp [S])
      · norm_num at hpPrime
      · exact hpS (by simp [S])
    have hpR : (7 : ℝ) < p := by exact_mod_cast hp7
    have hx0 : 0 ≤ ((p : ℝ)⁻¹) := by positivity
    have hxle : ((p : ℝ)⁻¹) ≤ 1 := by
      exact (inv_le_one₀ (by exact_mod_cast hpPrime.pos)).2
        (by exact_mod_cast hpPrime.one_le)
    have hbern :
        1 - 7 * ((p : ℝ)⁻¹) ≤ (1 - ((p : ℝ)⁻¹)) ^ 7 := by
      have h := one_add_mul_le_pow
        (a := -((p : ℝ)⁻¹)) (by linarith) 7
      norm_num at h ⊢
      linarith
    have hleft : 0 < 1 - 7 * ((p : ℝ)⁻¹) := by
      rw [sub_pos]
      rw [show 7 * ((p : ℝ)⁻¹) = 7 / (p : ℝ) by ring]
      exact (div_lt_one (by positivity)).mpr hpR
    have hInv :
        (((1 - ((p : ℝ)⁻¹)) ^ 7)⁻¹) ≤
          (1 - 7 * ((p : ℝ)⁻¹))⁻¹ :=
      inv_anti₀ hleft hbern
    rw [hnu, erdos647_nu_eq_seven_div_p p hpPrime hp7 hp11]
    calc
      ((1 - ((p : ℝ)⁻¹))⁻¹) ^ 7 =
          (((1 - ((p : ℝ)⁻¹)) ^ 7)⁻¹) := inv_pow _ _
      _ ≤ (1 - 7 * ((p : ℝ)⁻¹))⁻¹ := hInv
      _ = (1 - 7 / (p : ℝ))⁻¹ := by ring
  have hBigToL :
      (∏ p ∈ B, (1 - ((p : ℝ)⁻¹))⁻¹) ^ 7 ≤
        ∑ l ∈ t.prodPrimes.divisors, t.selbergTerms l := by
    calc
      (∏ p ∈ B, (1 - ((p : ℝ)⁻¹))⁻¹) ^ 7 =
          ∏ p ∈ B, ((1 - ((p : ℝ)⁻¹))⁻¹) ^ 7 := by
        rw [Finset.prod_pow]
      _ ≤ ∏ p ∈ B, (1 - t.nu p)⁻¹ := by
        apply Finset.prod_le_prod
        · intro p hp
          have hpF := (Finset.mem_sdiff.mp hp).1
          have hpPrime : p.Prime := (Finset.mem_filter.mp hpF).2
          have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
          have hbase : 0 < 1 - ((p : ℝ)⁻¹) :=
            sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR)
          positivity
        · exact hfactor
      _ ≤ ∏ p ∈ A, (1 - t.nu p)⁻¹ := by
        apply Finset.prod_le_prod_of_subset_of_one_le hBA
        · intro p hp
          have hpA : p ∈ t.prodPrimes.primeFactors := by
            rw [hpf]
            exact hBA hp
          have hpPrime := Nat.prime_of_mem_primeFactors hpA
          have hpdvd := Nat.dvd_of_mem_primeFactors hpA
          have hnult := t.nu_lt_one_of_prime p hpPrime hpdvd
          exact le_of_lt (inv_pos.mpr (by linarith))
        · intro p hpA hpB
          have hpPF : p ∈ t.prodPrimes.primeFactors := by
            rw [hpf]
            exact hpA
          have hpPrime := Nat.prime_of_mem_primeFactors hpPF
          have hpdvd := Nat.dvd_of_mem_primeFactors hpPF
          have hnupos := t.nu_pos_of_prime p hpPrime hpdvd
          have hnult := t.nu_lt_one_of_prime p hpPrime hpdvd
          exact (one_le_inv₀ (by linarith)).2 (by linarith)
      _ = ∑ l ∈ t.prodPrimes.divisors, t.selbergTerms l := by
        rw [← hpf]
        exact (erdos647_L_eq_prod t).symm
  have hlognonneg : 0 ≤ Real.log (z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ z by omega))
  have hpow := pow_le_pow_left₀
    (mul_nonneg (by norm_num) hlognonneg) hBLower 7
  calc
    ((16 : ℝ) / 77) ^ 7 * (Real.log (z : ℝ)) ^ 7 =
        (((16 : ℝ) / 77) * Real.log (z : ℝ)) ^ 7 := by ring
    _ ≤ (∏ p ∈ B, (1 - ((p : ℝ)⁻¹))⁻¹) ^ 7 := hpow
    _ ≤ ∑ l ∈ t.prodPrimes.divisors, t.selbergTerms l := hBigToL

end Erdos647
