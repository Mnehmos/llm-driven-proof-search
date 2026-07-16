import Mathlib

/-!
# Erdos #647 - smooth-number size bound and large-prime extraction

This module isolates a generic alternative used by the negative-existence lane.
If every prime divisor of a positive integer `m` is at most `W`, then the
divisor budget bounds the total prime-factor multiplicity and hence bounds
`m` itself:

`m <= W ^ (sigma 0 m - 1)`.

Consequently, for `1 <= W`, if `sigma 0 m <= B` but `W ^ (B - 1) < m`, then
`m` has a prime divisor strictly larger than `W`.  The positivity condition on
`W` is necessary for the `m = 1` edge case.  The result is generic Mathlib
arithmetic; it does not itself close any original Formal Conjectures
declaration.

Two roots were independently kernel-verified through the tracked proof-search
pipeline on 2026-07-16:

* `erdos647_smooth_le_pow_divisor_count_sub_one`
  * problem `88d55eb1-a5b0-4085-ae11-572db6b43d71`
  * episode `7518e92a-0ba9-4cec-9136-0eca9ae697d2`
  * root hash `b9e534f31106d18d6ae8c486212e2dd871126ae3d25f523c5fa276c316ba8195`
* `erdos647_exists_large_prime_factor_of_pow_lt`
  * problem `d80aa6f4-d447-4b35-8a01-448bf767f73a`
  * episode `6299d4d7-d39a-44cc-97ca-40840e989e5c`
  * root hash `8d933db24b4c58eaea9e7db1dc73ec0fd9af07e01d14521aa853d859b53d153e`

Both tracked submissions were self-contained: the second rederived the smooth
bound locally rather than relying on cross-submission theorem references.
-/

/-- A finite product of successor factors dominates one plus their sum. -/
private lemma erdos647_one_add_sum_le_prod_succ
    (s : Finset Nat) (a : Nat -> Nat) :
    1 + s.sum a <= s.prod (fun x => a x + 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.prod_insert hx]
      have hprod : 1 <= s.prod (fun y => a y + 1) := by
        exact Finset.one_le_prod (fun y _ => by omega)
      have hmul : a x <= s.prod (fun y => a y + 1) * a x := by
        simpa [one_mul] using Nat.mul_le_mul_right (a x) hprod
      calc
        1 + (a x + s.sum a) = a x + (1 + s.sum a) := by omega
        _ <= a x + s.prod (fun y => a y + 1) := Nat.add_le_add_left ih _
        _ <= s.prod (fun y => a y + 1) * a x +
              s.prod (fun y => a y + 1) := Nat.add_le_add_right hmul _
        _ = (a x + 1) * s.prod (fun y => a y + 1) := by ring

/-- A positive `W`-smooth number is bounded by `W` to one less than its
divisor count. -/
theorem erdos647_smooth_le_pow_divisor_count_sub_one :
    forall (m W : Nat),
      0 < m ->
      (forall p : Nat, p.Prime -> p ∣ m -> p <= W) ->
      m <= W ^ (ArithmeticFunction.sigma 0 m - 1) := by
  intro m W hm hsmooth
  by_cases hm1 : m = 1
  · subst m
    simp
  have hm0 : m ≠ 0 := by omega
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hm1
  have hW : 1 <= W := le_trans hqprime.one_lt.le (hsmooth q hqprime hqdvd)
  have hsigma : ArithmeticFunction.sigma 0 m =
      m.primeFactors.prod (fun p => m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
    simp
  have hmprod : m.primeFactors.prod (fun p =>
      p ^ (m.factorization p)) = m := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hm0
  have hsum : m.primeFactors.sum m.factorization <=
      ArithmeticFunction.sigma 0 m - 1 := by
    have h := erdos647_one_add_sum_le_prod_succ m.primeFactors m.factorization
    rw [← hsigma] at h
    omega
  calc
    m = m.primeFactors.prod (fun p => p ^ (m.factorization p)) := hmprod.symm
    _ <= m.primeFactors.prod (fun p => W ^ (m.factorization p)) := by
      apply Finset.prod_le_prod'
      intro p hp
      exact Nat.pow_le_pow_left
        (hsmooth p (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)) _
    _ = W ^ m.primeFactors.sum m.factorization := by
      exact Finset.prod_pow_eq_pow_sum _ _ _
    _ <= W ^ (ArithmeticFunction.sigma 0 m - 1) :=
      pow_le_pow_right' hW hsum

/-- A divisor budget `B` turns smoothness into the explicit bound
`m <= W^(B-1)`. -/
theorem erdos647_smooth_le_pow_divisor_budget_sub_one :
    forall (m W B : Nat),
      0 < m ->
      1 <= W ->
      ArithmeticFunction.sigma 0 m <= B ->
      (forall p : Nat, p.Prime -> p ∣ m -> p <= W) ->
      m <= W ^ (B - 1) := by
  intro m W B hm hW hbudget hsmooth
  calc
    m <= W ^ (ArithmeticFunction.sigma 0 m - 1) :=
      erdos647_smooth_le_pow_divisor_count_sub_one m W hm hsmooth
    _ <= W ^ (B - 1) := pow_le_pow_right' hW (Nat.sub_le_sub_right hbudget 1)

/-- If `m` exceeds the largest size permitted by its divisor budget under
`W`-smoothness, then `m` has a prime divisor larger than `W`. -/
theorem erdos647_exists_large_prime_factor_of_pow_lt :
    forall (m W B : Nat),
      0 < m ->
      1 <= W ->
      ArithmeticFunction.sigma 0 m <= B ->
      W ^ (B - 1) < m ->
      exists p : Nat, p.Prime ∧ p ∣ m ∧ W < p := by
  intro m W B hm hW hbudget hlarge
  by_contra hnone
  push Not at hnone
  have hsmooth : forall p : Nat, p.Prime -> p ∣ m -> p <= W := by
    intro p hp hpdvd
    exact hnone p hp hpdvd
  have hbound := erdos647_smooth_le_pow_divisor_budget_sub_one
    m W B hm hW hbudget hsmooth
  omega

/-- Shift-ready form: a divisor budget `sigma 0 (n-k) <= k+2` forces a prime
factor above `W` whenever `n-k` exceeds `W^(k+1)`. -/
theorem erdos647_exists_large_prime_factor_of_shift_budget :
    forall (n k W : Nat),
      k < n ->
      1 <= W ->
      ArithmeticFunction.sigma 0 (n - k) <= k + 2 ->
      W ^ (k + 1) < n - k ->
      exists p : Nat, p.Prime ∧ p ∣ (n - k) ∧ W < p := by
  intro n k W hkn hW hbudget hlarge
  apply erdos647_exists_large_prime_factor_of_pow_lt (n - k) W (k + 2)
  · omega
  · exact hW
  · exact hbudget
  · have hexp : k + 2 - 1 = k + 1 := by omega
    rw [hexp]
    exact hlarge
