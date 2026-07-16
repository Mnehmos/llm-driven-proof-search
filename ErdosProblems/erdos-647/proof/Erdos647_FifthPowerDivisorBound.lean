import Mathlib

/-!
# Erdős #647 — explicit fifth-power divisor bound

For every positive natural number,

`(ArithmeticFunction.sigma 0 n)^5 ≤ 147700800 * n`.

The proof applies the generic finite-local-factor Euler-product argument with
the primes below `32 = 2^5`.  The verified integer local constants are

`263, 39, 10, 5, 3, 3, 2, 2, 2, 2, 2`

at `2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31`, respectively; their product is
`147700800`.  Every prime outside this list is at least `32`, so the
generic rough-prime branch applies.  Each local inequality is proved for all
prime-power exponents by finite base cases and a monotone-ratio induction.

Tracked proof-search provenance for
`erdos647_divisor_fifth_power_bound` (2026-07-16):

* preverification job: `22d1bb31-a7c2-4281-973e-5748f95156f5`
* problem version: `75cba88a-343d-419d-a34c-9de817763902`
* episode: `21024f54-e6bb-4e11-8912-e3d715cf9a8a`
* root statement hash:
  `c2617d32d6404cdd1524142a7fe123324a6e7eb9d80f430ac303b63b3666026d`
* outcome: `kernel_verified`

The exact Formal-Conjectures-shaped fifth-root prefix bridge
`erdos647_candidate_of_fifth_power_prefix` was independently checked with
the fifth-power proof inlined, rather than relying on a cross-submission name:

* preverification job: `1baf19c4-479c-434d-81b4-7c72673e7548`
* problem version: `3ab58c24-4c25-46ca-bf93-95732f1332a7`
* episode: `bf1de66d-1115-46c3-a902-c78596f8c984`
* root statement hash:
  `2b39dca84752b6d4151514b97ac29aa33e3f3d80ab4fff371c16c30b25cfaa7f`
* outcome: `kernel_verified`

This is a finite-prefix certification theorem, not a closure of an original
Formal Conjectures open declaration.
-/

theorem erdos647_divisor_fifth_power_bound :
    ∀ n : ℕ, 1 ≤ n →
      (ArithmeticFunction.sigma 0 n) ^ 5 ≤ 147700800 * n := by
  intro n hn
  have hgeneric :
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
  have L2 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 263 * 2 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 5
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 7 * (k + 2) ≤ 8 * (k + 1) := by omega
        have hpow : 16807 * (k + 2) ^ 5 ≤ 32768 * (k + 1) ^ 5 := by
          calc
            16807 * (k + 2) ^ 5 = (7 * (k + 2)) ^ 5 := by ring
            _ ≤ (8 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 32768 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 2 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 2 * (k + 1) ^ 5 := hratio
          _ ≤ 2 * (263 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
          _ = 263 * 2 ^ (k + 1) := by rw [pow_succ]; ring
  have L3 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 39 * 3 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 3
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 5 * (k + 2) ≤ 6 * (k + 1) := by omega
        have hpow : 3125 * (k + 2) ^ 5 ≤ 7776 * (k + 1) ^ 5 := by
          calc
            3125 * (k + 2) ^ 5 = (5 * (k + 2)) ^ 5 := by ring
            _ ≤ (6 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 7776 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 3 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 3 * (k + 1) ^ 5 := hratio
          _ ≤ 3 * (39 * 3 ^ k) := Nat.mul_le_mul_left 3 ih
          _ = 39 * 3 ^ (k + 1) := by rw [pow_succ]; ring
  have L5 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 10 * 5 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 1
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 3 * (k + 2) ≤ 4 * (k + 1) := by omega
        have hpow : 243 * (k + 2) ^ 5 ≤ 1024 * (k + 1) ^ 5 := by
          calc
            243 * (k + 2) ^ 5 = (3 * (k + 2)) ^ 5 := by ring
            _ ≤ (4 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 1024 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 5 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 5 * (k + 1) ^ 5 := hratio
          _ ≤ 5 * (10 * 5 ^ k) := Nat.mul_le_mul_left 5 ih
          _ = 10 * 5 ^ (k + 1) := by rw [pow_succ]; ring
  have L7 : ∀ a : ℕ, (a + 1) ^ 5 ≤ 5 * 7 ^ a := by
    intro a
    induction a with
    | zero => norm_num
    | succ k ih =>
      by_cases hk : k ≤ 1
      · interval_cases k <;> norm_num
      · push Not at hk
        have hlin : 3 * (k + 2) ≤ 4 * (k + 1) := by omega
        have hpow : 243 * (k + 2) ^ 5 ≤ 1024 * (k + 1) ^ 5 := by
          calc
            243 * (k + 2) ^ 5 = (3 * (k + 2)) ^ 5 := by ring
            _ ≤ (4 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 1024 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ 7 * (k + 1) ^ 5 := by omega
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ 7 * (k + 1) ^ 5 := hratio
          _ ≤ 7 * (5 * 7 ^ k) := Nat.mul_le_mul_left 7 ih
          _ = 5 * 7 ^ (k + 1) := by rw [pow_succ]; ring
  have Llarge : ∀ (p c : ℕ), 11 ≤ p → 32 ≤ c * p →
      ∀ a : ℕ, (a + 1) ^ 5 ≤ c * p ^ a := by
    intro p c hp hbase a
    have hc : 1 ≤ c := by
      by_contra hc0
      push Not at hc0
      have : c = 0 := by omega
      simp [this] at hbase
    induction a with
    | zero => simpa using hc
    | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simpa using hbase
      · have hk1 : 1 ≤ k := by omega
        have hlin : 2 * (k + 2) ≤ 3 * (k + 1) := by omega
        have hpow : 32 * (k + 2) ^ 5 ≤ 243 * (k + 1) ^ 5 := by
          calc
            32 * (k + 2) ^ 5 = (2 * (k + 2)) ^ 5 := by ring
            _ ≤ (3 * (k + 1)) ^ 5 := Nat.pow_le_pow_left hlin 5
            _ = 243 * (k + 1) ^ 5 := by ring
        have hratio : (k + 2) ^ 5 ≤ p * (k + 1) ^ 5 := by
          have hp32 : 243 ≤ 32 * p := by omega
          have hscaled : 32 * (k + 2) ^ 5 ≤
              32 * (p * (k + 1) ^ 5) := by
            calc
              32 * (k + 2) ^ 5 ≤ 243 * (k + 1) ^ 5 := hpow
              _ ≤ (32 * p) * (k + 1) ^ 5 :=
                Nat.mul_le_mul_right ((k + 1) ^ 5) hp32
              _ = 32 * (p * (k + 1) ^ 5) := by ring
          exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)
        calc
          (k + 1 + 1) ^ 5 = (k + 2) ^ 5 := by ring_nf
          _ ≤ p * (k + 1) ^ 5 := hratio
          _ ≤ p * (c * p ^ k) := Nat.mul_le_mul_left p ih
          _ = c * p ^ (k + 1) := by rw [pow_succ]; ring
  let S : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31}
  let c : ℕ → ℕ := fun p =>
    if p = 2 then 263 else if p = 3 then 39 else if p = 5 then 10 else
    if p = 7 then 5 else if p = 11 then 3 else if p = 13 then 3 else 2
  have hc : ∀ p ∈ S, 1 ≤ c p := by
    intro p hp
    simp [S] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num [c]
  have hsmall : ∀ p ∈ S, p.Prime → p ∣ n → ∀ a : ℕ, 1 ≤ a →
      (a + 1) ^ 5 ≤ c p * p ^ a := by
    intro p hp hpp hpd a ha
    simp [S] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [c] using L2 a
    · simpa [c] using L3 a
    · simpa [c] using L5 a
    · simpa [c] using L7 a
    · simpa [c] using Llarge 11 3 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 13 3 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 17 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 19 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 23 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 29 2 (by norm_num) (by norm_num) a
    · simpa [c] using Llarge 31 2 (by norm_num) (by norm_num) a
  have hrough : ∀ p : ℕ, p.Prime → p ∣ n → p ∉ S → 2 ^ 5 ≤ p := by
    intro p hpp hpd hpS
    have hp32 : 32 ≤ p := by
      by_contra hp
      push Not at hp
      interval_cases p <;> norm_num at hpp
      all_goals norm_num [S] at hpS
    norm_num
    exact hp32
  have h := hgeneric 5 n S c (by norm_num) hn hc hsmall hrough
  norm_num [S, c] at h ⊢
  exact h

theorem erdos647_candidate_of_fifth_power_prefix :
    ∀ n : ℕ,
      0 < n →
      (∀ k : ℕ, 0 < k → k < n →
        (k + 2) ^ 5 < 147700800 * (n - k) →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro n hn hprefix
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbudget : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases hk : (k + 2) ^ 5 < 147700800 * (n - k)
    · exact hprefix k hk0 hkn hk
    · push Not at hk
      have hmpos : 1 ≤ n - k := by omega
      have hbound := erdos647_divisor_fifth_power_bound (n - k) hmpos
      have hpows :
          (ArithmeticFunction.sigma 0 (n - k)) ^ 5 ≤ (k + 2) ^ 5 :=
        hbound.trans hk
      exact (Nat.pow_le_pow_iff_left (by norm_num : 5 ≠ 0)).mp hpows
  apply ciSup_le
  intro m
  rcases Nat.eq_zero_or_pos (m : ℕ) with hm0 | hmpos
  · rw [hm0]
    simp
  · have hmn : (m : ℕ) < n := m.isLt
    have hk0 : 0 < n - (m : ℕ) := by omega
    have hkn : n - (m : ℕ) < n := by omega
    have hb := hbudget (n - (m : ℕ)) hk0 hkn
    have hmk : n - (n - (m : ℕ)) = (m : ℕ) := by omega
    rw [hmk] at hb
    omega
