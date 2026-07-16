import Mathlib

/-!
# Erdős #647 — smooth cofactor bounds

A positive `W`-smooth integer `q` is bounded by

`q ≤ W ^ (τ(q) - 1)`.

After the square-scale large-prime reduction supplies
`2 * τ(q) ≤ k + 2`, this sharpens to the explicit bound

`q ≤ W ^ (k / 2)`.

The combined theorem was independently tracked on 2026-07-16:

* problem version: `ed34492d-c07f-4b1d-9bd0-640da8313e75`
* episode: `b29f042a-6df4-45ce-b333-93f608c20664`
* root statement hash:
  `7567cb52a23081a9dfc7758f6209cfb4209f467118b2684fd18f2159e323a1e0`
* outcome: `kernel_verified`
-/

/-- The elementary inequality comparing the sum of exponents with the product
of one plus each exponent. -/
private theorem erdos647_one_add_sum_le_prod_succ :
    ∀ (s : Finset ℕ) (a : ℕ → ℕ),
      1 + s.sum a ≤ s.prod fun x => a x + 1 := by
  intro s a
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.prod_insert hx]
      have hprod : 1 ≤ s.prod (fun y => a y + 1) := by
        exact Finset.one_le_prod (fun y _ => by omega)
      have hmul : a x ≤ s.prod (fun y => a y + 1) * a x := by
        simpa [one_mul] using Nat.mul_le_mul_right (a x) hprod
      calc
        1 + (a x + s.sum a) = a x + (1 + s.sum a) := by omega
        _ ≤ a x + s.prod (fun y => a y + 1) := Nat.add_le_add_left ih _
        _ ≤ s.prod (fun y => a y + 1) * a x +
              s.prod (fun y => a y + 1) := Nat.add_le_add_right hmul _
        _ = (a x + 1) * s.prod (fun y => a y + 1) := by ring

/-- A positive integer all of whose prime divisors are at most `W` is bounded
by `W` to one less than its divisor count. -/
theorem erdos647_smooth_cofactor_bound :
    ∀ (q W : ℕ),
      0 < q →
      (∀ p : ℕ, Nat.Prime p → p ∣ q → p ≤ W) →
      q ≤ W ^ (ArithmeticFunction.sigma 0 q - 1) := by
  intro q W hq hsmooth
  by_cases hq1 : q = 1
  · subst q
    simp
  have hq0 : q ≠ 0 := by omega
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hq1
  have hW : 1 ≤ W := le_trans hpprime.one_lt.le (hsmooth p hpprime hpdvd)
  have hsigma : ArithmeticFunction.sigma 0 q =
      q.primeFactors.prod (fun p => q.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hq0]
    simp
  have hqprod : q.primeFactors.prod
      (fun p => p ^ q.factorization p) = q := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hq0
  have hsum : q.primeFactors.sum q.factorization ≤
      ArithmeticFunction.sigma 0 q - 1 := by
    have h := erdos647_one_add_sum_le_prod_succ
      q.primeFactors q.factorization
    rw [← hsigma] at h
    omega
  calc
    q = q.primeFactors.prod (fun p => p ^ q.factorization p) := hqprod.symm
    _ ≤ q.primeFactors.prod (fun p => W ^ q.factorization p) := by
      apply Finset.prod_le_prod'
      intro p hp
      exact Nat.pow_le_pow_left
        (hsmooth p (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)) _
    _ = W ^ q.primeFactors.sum q.factorization := by
      exact Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ W ^ (ArithmeticFunction.sigma 0 q - 1) :=
      pow_le_pow_right' hW hsum

/-- The explicit form used after removing a square-scale prime factor: a
doubled divisor budget cuts the smooth-cofactor exponent to `k / 2`. -/
theorem erdos647_smooth_cofactor_bound_of_doubled_budget :
    ∀ (q W k : ℕ),
      0 < q → 1 ≤ W →
      (∀ p : ℕ, Nat.Prime p → p ∣ q → p ≤ W) →
      2 * ArithmeticFunction.sigma 0 q ≤ k + 2 →
      q ≤ W ^ (k / 2) := by
  intro q W k hq hW hsmooth hbudget
  have hbase := erdos647_smooth_cofactor_bound q W hq hsmooth
  have hexp : ArithmeticFunction.sigma 0 q - 1 ≤ k / 2 := by
    omega
  exact hbase.trans (pow_le_pow_right' hW hexp)
