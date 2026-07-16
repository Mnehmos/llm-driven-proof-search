import Mathlib

/-!
# Erdős #647 — generic power-prefix bridges

An inequality `A * τ(m)^r ≤ C * m` reduces every shift budget of the
form `τ(n-k) ≤ B+k` to the prefix where
`A * (B+k)^r < C * (n-k)`.  The candidate bridge is the case `B = 2`.

All three declarations below were kernel-verified through tracked
proof-search episodes on 2026-07-16, each on its first tracked attempt:

* `erdos647_all_shift_budgets_of_power_prefix`
  * problem `426b9c04-44df-4dbb-b2b0-5be9d5985c65`
  * episode `a5663754-f659-425d-9ed2-797a14e6f45b`
  * statement hash `397f561238bb658ab3654db83f1f1571ed33a1b046365d8d1a6f63ed68734199`
  * preverification `5d17ca9d-6dc6-48db-bfac-382a916326d0` (`kernel_pass`)
* `erdos647_excess_shift_in_power_prefix`
  * problem `5a951bb5-aa70-435d-ab19-e09d9efc8af3`
  * episode `081bad92-4417-4ecc-ac20-b1163f8787c0`
  * statement hash `d787f7f71abaf04848971da9ca4386dd84542f428380dd2833cdcbc5052b1f75`
  * preverification `77ebff07-57cf-4737-8cd7-b5d4ac6b6ec2` (`kernel_pass`)
* `erdos647_candidate_of_power_prefix`
  * problem `729ddf23-c41f-4006-a3e9-a02ede66e7b0`
  * episode `fffbd7ef-df32-471c-b2c5-57246a86d0a2`
  * statement hash `80774e97d9da7ebb2fd2ea10374af7f73d9dce246b0ee0a79d77ea97b3261532`
  * preverification `ba53c5e6-cf67-471a-b37d-f755294895a7` (`kernel_pass`)
-/

theorem erdos647_all_shift_budgets_of_power_prefix :
    ∀ r A C B n : ℕ,
      0 < r →
      0 < A →
      (∀ m : ℕ, 1 ≤ m →
        A * (ArithmeticFunction.sigma 0 m) ^ r ≤ C * m) →
      (∀ k : ℕ, 0 < k → k < n →
        A * (B + k) ^ r < C * (n - k) →
        ArithmeticFunction.sigma 0 (n - k) ≤ B + k) →
      ∀ k : ℕ, 0 < k → k < n →
        ArithmeticFunction.sigma 0 (n - k) ≤ B + k := by
  intro r A C B n hr hA hdiv hprefix k hk0 hkn
  by_cases hk : A * (B + k) ^ r < C * (n - k)
  · exact hprefix k hk0 hkn hk
  · push Not at hk
    have hmpos : 1 ≤ n - k := by omega
    have hbound := hdiv (n - k) hmpos
    have hmul :
        A * (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤
          A * (B + k) ^ r := hbound.trans hk
    have hpows :
        (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤ (B + k) ^ r :=
      le_of_mul_le_mul_left hmul hA
    exact (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hr)).mp hpows

theorem erdos647_excess_shift_in_power_prefix :
    ∀ r A C B n k : ℕ,
      0 < r →
      0 < A →
      (∀ m : ℕ, 1 ≤ m →
        A * (ArithmeticFunction.sigma 0 m) ^ r ≤ C * m) →
      0 < k →
      k < n →
      B + k < ArithmeticFunction.sigma 0 (n - k) →
      A * (B + k) ^ r < C * (n - k) := by
  intro r A C B n k hr hA hdiv hk0 hkn hfail
  by_contra hprefix
  push Not at hprefix
  have hmpos : 1 ≤ n - k := by omega
  have hbound := hdiv (n - k) hmpos
  have hmul :
      A * (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤
        A * (B + k) ^ r := hbound.trans hprefix
  have hpows :
      (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤ (B + k) ^ r :=
    le_of_mul_le_mul_left hmul hA
  have hbudget : ArithmeticFunction.sigma 0 (n - k) ≤ B + k :=
    (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hr)).mp hpows
  omega

theorem erdos647_candidate_of_power_prefix :
    ∀ r A C n : ℕ,
      0 < r →
      0 < A →
      0 < n →
      (∀ m : ℕ, 1 ≤ m →
        A * (ArithmeticFunction.sigma 0 m) ^ r ≤ C * m) →
      (∀ k : ℕ, 0 < k → k < n →
        A * (k + 2) ^ r < C * (n - k) →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro r A C n hr hA hn hdiv hprefix
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbudget : ∀ k : ℕ, 0 < k → k < n →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
    intro k hk0 hkn
    by_cases hk : A * (k + 2) ^ r < C * (n - k)
    · exact hprefix k hk0 hkn hk
    · push Not at hk
      have hmpos : 1 ≤ n - k := by omega
      have hbound := hdiv (n - k) hmpos
      have hmul :
          A * (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤
            A * (k + 2) ^ r := hbound.trans hk
      have hpows :
          (ArithmeticFunction.sigma 0 (n - k)) ^ r ≤ (k + 2) ^ r :=
        le_of_mul_le_mul_left hmul hA
      exact (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hr)).mp hpows
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
