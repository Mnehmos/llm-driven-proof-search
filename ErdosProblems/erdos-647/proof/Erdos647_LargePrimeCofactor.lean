import Mathlib

/-!
# Erdős #647 — large-prime cofactor reduction

If a prime `p` divides a positive `m < p²`, the complementary factor
`q = m / p` is strictly smaller than `p` and is coprime to it.  Consequently
the divisor count splits as `τ(m) = 2 τ(q)`.  The final theorem transports this
factorization directly into a shifted candidate budget.

Tracked proof-search provenance (2026-07-16):

* general `p^t` cofactor theorem:
  problem `04c0d0c3-a94a-4fa6-b761-201b047c2fec`,
  episode `da4d5b5b-314f-4204-8dc6-b917fd969062`,
  root hash
  `d26a4107aea6d15b0f9a1776e90d23a63e233dfdfeecec5d3bbd099462d950d7`;
* shifted candidate-budget theorem (with the square-scale cofactor proof
  inlined): problem `3b815ec3-a985-4180-931f-f6ec9295855f`,
  episode `cf96c53e-9e2b-48d0-a5cf-cae17267c149`,
  root hash
  `0a47b168a3b92156cde20b891f1e717137a148401c37dc2c8a7adc462434ea89`.

Both tracked roots have outcome `kernel_verified`.
-/

/-- The exact factorization, size, coprimality, and divisor-count conclusions
for a prime divisor larger than the square-root scale. -/
theorem erdos647_large_prime_cofactor :
    ∀ {m p : ℕ},
      0 < m → Nat.Prime p → p ∣ m → m < p ^ 2 →
      let q := m / p
      m = p * q ∧
        q < p ∧
        Nat.Coprime p q ∧
        ArithmeticFunction.sigma 0 m =
          2 * ArithmeticFunction.sigma 0 q := by
  intro m p hm hp hpd hsq
  dsimp
  have hfac : p * (m / p) = m := Nat.mul_div_cancel' hpd
  have hq_lt : m / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]
    simpa [pow_two] using hsq
  have hp_le_m : p ≤ m := Nat.le_of_dvd hm hpd
  have hqpos : 0 < m / p := Nat.div_pos hp_le_m hp.pos
  have hcop : Nat.Coprime p (m / p) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hpq
    have hpleq : p ≤ m / p := Nat.le_of_dvd hqpos hpq
    omega
  have hsigp : ArithmeticFunction.sigma 0 p = 2 := by
    simpa using
      (ArithmeticFunction.sigma_zero_apply_prime_pow (p := p) (i := 1) hp)
  refine ⟨hfac.symm, hq_lt, hcop, ?_⟩
  calc
    ArithmeticFunction.sigma 0 m =
        ArithmeticFunction.sigma 0 (p * (m / p)) := by rw [hfac]
    _ = ArithmeticFunction.sigma 0 p *
        ArithmeticFunction.sigma 0 (m / p) :=
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
    _ = 2 * ArithmeticFunction.sigma 0 (m / p) := by rw [hsigp]

/-- General power-scale form: if `p ∣ m < p^t`, the exact `p`-adic exponent
of `m` lies in `[1,t)`, and removing that prime power splits the divisor count
by the factor `a + 1`. -/
theorem erdos647_large_prime_power_cofactor :
    ∀ {m p t : ℕ},
      0 < m → Nat.Prime p → p ∣ m → m < p ^ t →
      ∃ a q : ℕ,
        1 ≤ a ∧ a < t ∧ ¬ p ∣ q ∧
        m = p ^ a * q ∧
        Nat.Coprime (p ^ a) q ∧
        ArithmeticFunction.sigma 0 m =
          (a + 1) * ArithmeticFunction.sigma 0 q := by
  intro m p t hm hp hpd hlt
  obtain ⟨a, q, hpq, hfac⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (show m ≠ 0 by omega) p hp.ne_one
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq, mul_zero] at hfac
      omega
    · exact hq
  have ha1 : 1 ≤ a := by
    by_contra ha
    push Not at ha
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero, one_mul] at hfac
    rw [hfac] at hpd
    exact hpq hpd
  have hpow_le : p ^ a ≤ m := by
    calc
      p ^ a = p ^ a * 1 := by simp
      _ ≤ p ^ a * q := Nat.mul_le_mul_left _ hqpos
      _ = m := hfac.symm
  have hat : a < t := by
    by_contra hat
    push Not at hat
    have hpow_mono : p ^ t ≤ p ^ a := Nat.pow_le_pow_right hp.pos hat
    omega
  have hcop : Nat.Coprime (p ^ a) q :=
    (hp.coprime_iff_not_dvd.mpr hpq).pow_left a
  have hsigma : ArithmeticFunction.sigma 0 m =
      (a + 1) * ArithmeticFunction.sigma 0 q := by
    calc
      ArithmeticFunction.sigma 0 m =
          ArithmeticFunction.sigma 0 (p ^ a * q) := by rw [hfac]
      _ = ArithmeticFunction.sigma 0 (p ^ a) *
          ArithmeticFunction.sigma 0 q :=
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
      _ = (a + 1) * ArithmeticFunction.sigma 0 q := by
        rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  exact ⟨a, q, ha1, hat, hpq, hfac, hcop, hsigma⟩

/-- A shifted candidate budget inherits a factor `2` after removing a prime
divisor `p` at the square-root scale. -/
theorem erdos647_shift_large_prime_cofactor_budget :
    ∀ {n k p : ℕ},
      0 < k → k < n →
      Nat.Prime p → p ∣ n - k → n ≤ p ^ 2 →
      ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 →
      let q := (n - k) / p
      n - k = p * q ∧
        q < p ∧
        Nat.Coprime p q ∧
        2 * ArithmeticFunction.sigma 0 q ≤ k + 2 := by
  intro n k p hk hkn hp hpd hn_sq hbudget
  have hmpos : 0 < n - k := by omega
  have hm_sq : n - k < p ^ 2 := by omega
  have hcore := erdos647_large_prime_cofactor hmpos hp hpd hm_sq
  dsimp at hcore ⊢
  rcases hcore with ⟨hfac, hq_lt, hcop, hsigma⟩
  refine ⟨hfac, hq_lt, hcop, ?_⟩
  rw [← hsigma]
  exact hbudget
