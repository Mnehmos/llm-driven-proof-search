import Mathlib

/-!
# Erdős #647 — generic local-factor bounds for arbitrary divisor powers

This module turns verified prime-power inequalities into global bounds for
`τ(m)^r`.  It has both natural-valued local constants and an exact integral
denominator/numerator form, so coefficients such as `8/5` and `8/7` can be
represented without introducing rational arithmetic.

All four theorem roots were independently kernel-verified through the tracked
proof-search pipeline on 2026-07-16:

* `erdos647_divisor_power_le_local_constants`
  * problem `ae91b365-010a-43a3-80e8-7f473e124f1c`
  * episode `9839cc5d-d4f7-4f35-bdc0-b6d18c4da0cc`
  * root hash `4533c10c66ae747241bc71a639a18f6596e50f2ac6cebea99a193c96c34a988f`
* `erdos647_divisor_power_le_finite_local_constants`
  * problem `826f66c3-0bed-4bfa-9f67-75292db3309d`
  * episode `c8c2d6e3-4ead-4931-a9fc-53b10ef5eddb`
  * root hash `54bb460e0ec9440c686c8675cd3aa0c777dd4bb08c756412e02d9e94ebe62eb5`
* `erdos647_divisor_power_le_local_ratios`
  * problem `a5450168-bfbd-4d08-b0cc-91ab3fb445a4`
  * episode `2a2dcc3b-783c-48d0-89fd-9b5bed501916`
  * root hash `91c7087690628181cb1729b22558b1dda3977bf40fee9277669900008262eba8`
* `erdos647_divisor_power_le_finite_local_ratios`
  * problem `0e1dd653-15d2-415b-9f74-6892c18911ab`
  * episode `11ce561a-d5ad-4225-ae5f-cb8b1f32afa6`
  * root hash `16cfd8f60386be597e3ff9db7367f6e3cfa75ccc6b378a8edaa062e2f17a520c`

For `S = {2,3,5,7}`, denominator factors `(1,1,5,7)`, numerator factors
`(8,3,8,8)`, and `r=3`, the final theorem exactly recovers the campaign's
class-sensitive coefficient multiplying `m` while placing `35·τ(m)^3` on the
left.  The theorem is generic and does not itself close an original Formal
Conjectures declaration.
-/

theorem erdos647_divisor_power_le_local_constants :
    ∀ (r m : ℕ) (c : ℕ → ℕ),
      0 < r →
      1 ≤ m →
      (∀ p ∈ m.primeFactors,
        (m.factorization p + 1) ^ r ≤ c p * p ^ (m.factorization p)) →
      (ArithmeticFunction.sigma 0 m) ^ r ≤
        (∏ p ∈ m.primeFactors, c p) * m := by
  intro r m c hr hm hlocal
  have hm0 : m ≠ 0 := by omega
  have hsigma : ArithmeticFunction.sigma 0 m =
      ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
    simp
  have hmprod : (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) = m := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hm0
  rw [hsigma, ← Finset.prod_pow]
  calc
    ∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ r
        ≤ ∏ p ∈ m.primeFactors, c p * p ^ (m.factorization p) := by
            exact Finset.prod_le_prod' hlocal
    _ = (∏ p ∈ m.primeFactors, c p) *
          (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
            rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ m.primeFactors, c p) * m := by rw [hmprod]

theorem erdos647_divisor_power_le_finite_local_constants :
    ∀ (r m : ℕ) (S : Finset ℕ) (c : ℕ → ℕ),
      0 < r →
      1 ≤ m →
      (∀ p ∈ S, 1 ≤ c p) →
      (∀ p ∈ S, p.Prime → p ∣ m → ∀ a : ℕ, 1 ≤ a →
        (a + 1) ^ r ≤ c p * p ^ a) →
      (∀ p : ℕ, p.Prime → p ∣ m → p ∉ S → 2 ^ r ≤ p) →
      (ArithmeticFunction.sigma 0 m) ^ r ≤ (∏ p ∈ S, c p) * m := by
  intro r m S c hr hm hc hsmall hrough
  have hm0 : m ≠ 0 := by omega
  have hbinary : ∀ b : ℕ, b + 1 ≤ 2 ^ b := by
    intro b
    induction b with
    | zero => simp
    | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hlocal : ∀ p ∈ m.primeFactors,
      (m.factorization p + 1) ^ r ≤
        (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    have hpa : 1 ≤ m.factorization p :=
      hpp.factorization_pos_of_dvd hm0 hpd
    by_cases hpS : p ∈ S
    · simp only [hpS, if_true]
      exact hsmall p hpS hpp hpd _ hpa
    · simp only [hpS, if_false, one_mul]
      calc
        (m.factorization p + 1) ^ r ≤ (2 ^ (m.factorization p)) ^ r :=
          Nat.pow_le_pow_left (hbinary _) r
        _ = (2 ^ r) ^ (m.factorization p) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p ^ (m.factorization p) :=
          Nat.pow_le_pow_left (hrough p hpp hpd hpS) _
  have hsigma : ArithmeticFunction.sigma 0 m =
      ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
    simp
  have hmprod : (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) = m := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hm0
  have hbase : (ArithmeticFunction.sigma 0 m) ^ r ≤
      (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by
    rw [hsigma, ← Finset.prod_pow]
    calc
      ∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ r
          ≤ ∏ p ∈ m.primeFactors,
              (if p ∈ S then c p else 1) * p ^ (m.factorization p) := by
                exact Finset.prod_le_prod' hlocal
      _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) *
            (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
              rw [Finset.prod_mul_distrib]
      _ = (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) * m := by
            rw [hmprod]
  have hprod_eq :
      (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) =
        ∏ p ∈ m.primeFactors.filter (fun p => p ∈ S), c p := by
    rw [Finset.prod_filter]
  have hsub : m.primeFactors.filter (fun p => p ∈ S) ⊆ S := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hprod_le :
      (∏ p ∈ m.primeFactors, if p ∈ S then c p else 1) ≤
        ∏ p ∈ S, c p := by
    rw [hprod_eq]
    exact Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun _ _ => Nat.zero_le _)
      (fun p hpS _ => hc p hpS)
  exact hbase.trans (Nat.mul_le_mul_right m hprod_le)

theorem erdos647_divisor_power_le_local_ratios :
    ∀ (r m : ℕ) (den num : ℕ → ℕ),
      1 ≤ m →
      (∀ p ∈ m.primeFactors,
        den p * (m.factorization p + 1) ^ r ≤
          num p * p ^ (m.factorization p)) →
      (∏ p ∈ m.primeFactors, den p) *
          (ArithmeticFunction.sigma 0 m) ^ r ≤
        (∏ p ∈ m.primeFactors, num p) * m := by
  intro r m den num hm hlocal
  have hm0 : m ≠ 0 := by omega
  have hsigma : ArithmeticFunction.sigma 0 m =
      ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
    simp
  have hmprod : (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) = m := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hm0
  rw [hsigma, ← Finset.prod_pow]
  calc
    (∏ p ∈ m.primeFactors, den p) *
          (∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ r) =
        ∏ p ∈ m.primeFactors,
          den p * (m.factorization p + 1) ^ r := by
            rw [Finset.prod_mul_distrib]
    _ ≤ ∏ p ∈ m.primeFactors,
          num p * p ^ (m.factorization p) :=
            Finset.prod_le_prod' hlocal
    _ = (∏ p ∈ m.primeFactors, num p) *
          (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
            rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ m.primeFactors, num p) * m := by rw [hmprod]

theorem erdos647_divisor_power_le_finite_local_ratios :
    ∀ (r m : ℕ) (S : Finset ℕ) (den num : ℕ → ℕ),
      0 < r →
      1 ≤ m →
      (∀ p ∈ S, p.Prime → p ∣ m → ∀ a : ℕ, 1 ≤ a →
        den p * (a + 1) ^ r ≤ num p * p ^ a) →
      (∀ p : ℕ, p.Prime → p ∣ m → p ∉ S → 2 ^ r ≤ p) →
      (∏ p ∈ S, den p) * (ArithmeticFunction.sigma 0 m) ^ r ≤
        (∏ p ∈ S, if p ∈ m.primeFactors then num p else den p) * m := by
  intro r m S den num hr hm hsmall hrough
  have hm0 : m ≠ 0 := by omega
  have hbinary : ∀ b : ℕ, b + 1 ≤ 2 ^ b := by
    intro b
    induction b with
    | zero => simp
    | succ k ih =>
      calc
        k + 1 + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hlocal : ∀ p ∈ m.primeFactors,
      (if p ∈ S then den p else 1) * (m.factorization p + 1) ^ r ≤
        (if p ∈ S then num p else 1) * p ^ (m.factorization p) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
    have hpa : 1 ≤ m.factorization p :=
      hpp.factorization_pos_of_dvd hm0 hpd
    by_cases hpS : p ∈ S
    · simp only [hpS, if_true]
      exact hsmall p hpS hpp hpd _ hpa
    · simp only [hpS, if_false, one_mul]
      calc
        (m.factorization p + 1) ^ r ≤ (2 ^ (m.factorization p)) ^ r :=
          Nat.pow_le_pow_left (hbinary _) r
        _ = (2 ^ r) ^ (m.factorization p) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ p ^ (m.factorization p) :=
          Nat.pow_le_pow_left (hrough p hpp hpd hpS) _
  have hsigma : ArithmeticFunction.sigma 0 m =
      ∏ p ∈ m.primeFactors, (m.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
    simp
  have hmprod : (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) = m := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hm0
  have hraw :
      (∏ p ∈ m.primeFactors, if p ∈ S then den p else 1) *
          (ArithmeticFunction.sigma 0 m) ^ r ≤
        (∏ p ∈ m.primeFactors, if p ∈ S then num p else 1) * m := by
    rw [hsigma, ← Finset.prod_pow]
    calc
      (∏ p ∈ m.primeFactors, if p ∈ S then den p else 1) *
            (∏ p ∈ m.primeFactors, (m.factorization p + 1) ^ r) =
          ∏ p ∈ m.primeFactors,
            (if p ∈ S then den p else 1) * (m.factorization p + 1) ^ r := by
              rw [Finset.prod_mul_distrib]
      _ ≤ ∏ p ∈ m.primeFactors,
            (if p ∈ S then num p else 1) * p ^ (m.factorization p) :=
              Finset.prod_le_prod' hlocal
      _ = (∏ p ∈ m.primeFactors, if p ∈ S then num p else 1) *
            (∏ p ∈ m.primeFactors, p ^ (m.factorization p)) := by
              rw [Finset.prod_mul_distrib]
      _ = (∏ p ∈ m.primeFactors, if p ∈ S then num p else 1) * m := by
            rw [hmprod]
  set T := S.filter (fun p => p ∈ m.primeFactors) with hT
  set U := S.filter (fun p => p ∉ m.primeFactors) with hU
  have hfilter : m.primeFactors.filter (fun p => p ∈ S) = T := by
    ext p
    simp [T, and_comm]
  have hinter : m.primeFactors ∩ S = T := by
    ext p
    simp [T, and_comm]
  have hraw' : (∏ p ∈ T, den p) * (ArithmeticFunction.sigma 0 m) ^ r ≤
      (∏ p ∈ T, num p) * m := by
    simpa [Finset.prod_ite, hfilter, hinter] using hraw
  have hden_split : (∏ p ∈ S, den p) =
      (∏ p ∈ T, den p) * (∏ p ∈ U, den p) := by
    simpa [T, U] using
      (Finset.prod_ite (s := S) (p := fun p => p ∈ m.primeFactors) den den)
  have hnum_split :
      (∏ p ∈ S, if p ∈ m.primeFactors then num p else den p) =
        (∏ p ∈ T, num p) * (∏ p ∈ U, den p) := by
    simpa [T, U] using
      (Finset.prod_ite (s := S) (p := fun p => p ∈ m.primeFactors) num den)
  calc
    (∏ p ∈ S, den p) * (ArithmeticFunction.sigma 0 m) ^ r =
        (∏ p ∈ U, den p) *
          ((∏ p ∈ T, den p) * (ArithmeticFunction.sigma 0 m) ^ r) := by
            rw [hden_split]
            ring
    _ ≤ (∏ p ∈ U, den p) * ((∏ p ∈ T, num p) * m) :=
      Nat.mul_le_mul_left _ hraw'
    _ = (∏ p ∈ S, if p ∈ m.primeFactors then num p else den p) * m := by
      rw [hnum_split]
      ring
