import Mathlib

/-!
# A finite Euler-product lower bound

The proof is deliberately elementary.  Every `1 ≤ n ≤ z` divides `z!`,
the reciprocal divisor sum is multiplicative, and each finite local geometric
sum is bounded by its infinite geometric series.
-/

namespace Erdos647

private noncomputable def reciprocalNat : ArithmeticFunction ℝ :=
  ⟨fun n => ((n : ℝ)⁻¹), by simp⟩

private theorem reciprocalNat_isMultiplicative :
    reciprocalNat.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [reciprocalNat]
  · intro m n hm hn hcop
    simp [reciprocalNat, Nat.cast_mul]
    rw [mul_comm]

private noncomputable def reciprocalDivisorSum : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * reciprocalNat

private theorem reciprocalDivisorSum_isMultiplicative :
    reciprocalDivisorSum.IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    reciprocalNat_isMultiplicative

private theorem reciprocalDivisorSum_apply (n : ℕ) :
    reciprocalDivisorSum n = ∑ d ∈ n.divisors, ((d : ℝ)⁻¹) := by
  unfold reciprocalDivisorSum
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  rfl

private theorem reciprocalDivisorSum_prime_pow_le
    (p e : ℕ) (hp : p.Prime) :
    reciprocalDivisorSum (p ^ e) ≤ (1 - ((p : ℝ)⁻¹))⁻¹ := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hx0 : 0 ≤ ((p : ℝ)⁻¹) := by positivity
  have hx1 : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hpR
  rw [reciprocalDivisorSum_apply, Nat.divisors_prime_pow hp]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, Nat.cast_pow]
  simp_rw [← inv_pow]
  calc
    (∑ i ∈ Finset.range (e + 1), ((p : ℝ)⁻¹) ^ i) ≤
        ∑' i : ℕ, ((p : ℝ)⁻¹) ^ i :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity)
        (summable_geometric_of_lt_one hx0 hx1)
    _ = (1 - ((p : ℝ)⁻¹))⁻¹ :=
      tsum_geometric_of_lt_one hx0 hx1

private theorem primeFactors_factorial (z : ℕ) :
    (Nat.factorial z).primeFactors =
      (Finset.range (z + 1)).filter Nat.Prime := by
  ext p
  rw [Nat.mem_primeFactors]
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hpdvd, hfact⟩
    rw [Nat.factorial_eq_prod_range_add_one] at hpdvd
    obtain ⟨i, hi, hpi⟩ :=
      (hp.prime.dvd_finsetProd_iff (fun i => i + 1)).mp hpdvd
    have hi' : i < z := Finset.mem_range.mp hi
    have hple : p ≤ i + 1 := Nat.le_of_dvd (by omega) hpi
    exact ⟨by omega, hp⟩
  · rintro ⟨hpz, hp⟩
    exact ⟨hp, Nat.dvd_factorial hp.pos (by omega), Nat.factorial_ne_zero z⟩

theorem harmonic_sum_le_prime_euler_product (z : ℕ) :
    (∑ n ∈ Finset.Icc 1 z, ((n : ℝ)⁻¹)) ≤
      ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime,
        (1 - ((p : ℝ)⁻¹))⁻¹ := by
  have hsubset : Finset.Icc 1 z ⊆ (Nat.factorial z).divisors := by
    intro n hn
    have hn' : 1 ≤ n ∧ n ≤ z := Finset.mem_Icc.mp hn
    exact Nat.mem_divisors.mpr
      ⟨Nat.dvd_factorial (by omega) hn'.2, Nat.factorial_ne_zero z⟩
  have hsum :
      (∑ n ∈ Finset.Icc 1 z, ((n : ℝ)⁻¹)) ≤
        ∑ d ∈ (Nat.factorial z).divisors, ((d : ℝ)⁻¹) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro d hd hnot
    positivity
  have hfactorization : reciprocalDivisorSum (Nat.factorial z) =
      ∏ p ∈ (Nat.factorial z).primeFactors,
        reciprocalDivisorSum (p ^ (Nat.factorial z).factorization p) := by
    rw [reciprocalDivisorSum_isMultiplicative.multiplicative_factorization
      reciprocalDivisorSum (Nat.factorial_ne_zero z)]
    exact Nat.prod_factorization_eq_prod_primeFactors _
  calc
    (∑ n ∈ Finset.Icc 1 z, ((n : ℝ)⁻¹)) ≤
        ∑ d ∈ (Nat.factorial z).divisors, ((d : ℝ)⁻¹) := hsum
    _ = reciprocalDivisorSum (Nat.factorial z) :=
      (reciprocalDivisorSum_apply (Nat.factorial z)).symm
    _ = ∏ p ∈ (Nat.factorial z).primeFactors,
          reciprocalDivisorSum (p ^ (Nat.factorial z).factorization p) := hfactorization
    _ ≤ ∏ p ∈ (Nat.factorial z).primeFactors, (1 - ((p : ℝ)⁻¹))⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        rw [reciprocalDivisorSum_apply]
        positivity
      · intro p hp
        exact reciprocalDivisorSum_prime_pow_le p
          ((Nat.factorial z).factorization p) (Nat.prime_of_mem_primeFactors hp)
    _ = ∏ p ∈ (Finset.range (z + 1)).filter Nat.Prime,
          (1 - ((p : ℝ)⁻¹))⁻¹ := by
      rw [primeFactors_factorial]

end Erdos647
