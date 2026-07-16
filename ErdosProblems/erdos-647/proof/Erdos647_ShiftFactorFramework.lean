import Erdos647_Shift13Refined

/-!
Erdos 647 generic shift-factor peeling framework.

The shift-specific arguments all use the same mechanism. A candidate gives
`sigma0(n-k) <= k+2`; a known factorization with a coprime factor turns
multiplicativity into a divided divisor budget for the cofactor.

The prime-power peel and modular-lift cores were independently preverified by
proof-search jobs `94f97429-5c14-428b-befd-cb119da1b79b` and
`d2260d3c-2e67-4a3e-ac55-13782f89237f`, then tracked `kernel_verified` in
episodes `3e3ee8d9-a23b-4997-bb26-345cfe672337` and
`5ec047ae-3659-449e-8546-26ea9c941be0`.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- Peeling a known coprime factor divides the remaining divisor budget by
the divisor count of that factor. -/
theorem sigma_zero_coprime_factor_peel :
    ∀ c q B : ℕ, Nat.Coprime c q →
      0 < ArithmeticFunction.sigma 0 c →
      ArithmeticFunction.sigma 0 (c * q) ≤ B →
      ArithmeticFunction.sigma 0 q ≤
        B / ArithmeticFunction.sigma 0 c := by
  intro c q B hcop hcpos hbound
  have hmul : ArithmeticFunction.sigma 0 (c * q) =
      ArithmeticFunction.sigma 0 c * ArithmeticFunction.sigma 0 q :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hmul] at hbound
  apply (Nat.le_div_iff_mul_le hcpos).2
  simpa [Nat.mul_comm] using hbound

/-- Prime-power form of the arithmetic core, independent of any candidate. -/
theorem sigma_zero_prime_power_cofactor_peel :
    ∀ p e q B : ℕ, Nat.Prime p → Nat.Coprime p q →
      ArithmeticFunction.sigma 0 (p ^ e * q) ≤ B →
      ArithmeticFunction.sigma 0 q ≤ B / (e + 1) := by
  intro p e q B hp hcop hbound
  have hpos : 0 < ArithmeticFunction.sigma 0 (p ^ e) := by
    rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    omega
  have h := sigma_zero_coprime_factor_peel (p ^ e) q B
    (hcop.pow_left e) hpos hbound
  simpa [ArithmeticFunction.sigma_zero_apply_prime_pow hp] using h

/-- Candidate wrapper for the generic coprime-factor peel at any shift. -/
theorem candidate_shift_coprime_factor_peel :
    ∀ n k c q : ℕ,
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      0 < k → k < n → n - k = c * q → Nat.Coprime c q →
      0 < ArithmeticFunction.sigma 0 c →
      ArithmeticFunction.sigma 0 q ≤
        (k + 2) / ArithmeticFunction.sigma 0 c := by
  intro n k c q H hk0 hkn hfactor hcop hcpos
  have hbudget := full_max_implies_shift_budgets n H k hk0 hkn
  rw [hfactor] at hbudget
  exact sigma_zero_coprime_factor_peel c q (k + 2) hcop hcpos hbudget

/-- Prime-power specialization: peeling `p^e` divides the remaining budget
by exactly `e+1`. -/
theorem candidate_shift_prime_power_peel :
    ∀ n k p e q : ℕ,
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      0 < k → k < n → Nat.Prime p →
      n - k = p ^ e * q → Nat.Coprime (p ^ e) q →
      ArithmeticFunction.sigma 0 q ≤ (k + 2) / (e + 1) := by
  intro n k p e q H hk0 hkn hp hfactor hcop
  have hpos : 0 < ArithmeticFunction.sigma 0 (p ^ e) := by
    rw [ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    omega
  have h := candidate_shift_coprime_factor_peel n k (p ^ e) q H hk0 hkn
    hfactor hcop hpos
  simpa [ArithmeticFunction.sigma_zero_apply_prime_pow hp] using h

/-- If the divided budget is below the next power of two, the cofactor has at
most the corresponding number of distinct prime factors. -/
theorem candidate_shift_prime_power_omega_le :
    ∀ n k p e q r : ℕ,
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      0 < k → k < n → Nat.Prime p →
      n - k = p ^ e * q → Nat.Coprime (p ^ e) q → q ≠ 0 →
      (k + 2) / (e + 1) < 2 ^ (r + 1) →
      q.primeFactors.card ≤ r := by
  intro n k p e q r H hk0 hkn hp hfactor hcop hq0 hpow
  have hqbudget := candidate_shift_prime_power_peel n k p e q H hk0 hkn
    hp hfactor hcop
  exact primeFactors_card_le_of_sigma_zero_lt_two_pow q r hq0
    (lt_of_le_of_lt hqbudget hpow)

/-- After extracting `p^e`, failure of coprimality at the next step is
equivalent to one further `p`-adic divisibility layer. -/
theorem next_adic_lift_iff :
    ∀ x p e q : ℕ, Nat.Prime p → x = p ^ e * q →
      (p ∣ q ↔ p ^ (e + 1) ∣ x) := by
  intro x p e q hp hfactor
  rw [hfactor, show e + 1 = e.succ by omega, Nat.pow_succ]
  exact (mul_dvd_mul_iff_left (pow_ne_zero e hp.ne_zero)).symm

/-- For a linear cofactor, the next `p`-adic lift is exactly a modular
exceptional class. Concrete shifts only need to enumerate these classes. -/
theorem next_adic_lift_iff_modEq :
    ∀ p e q a b N : ℕ, Nat.Prime p → b ≤ a * N →
      a * N - b = p ^ e * q →
      (p ∣ q ↔ b ≡ a * N [MOD p ^ (e + 1)]) := by
  intro p e q a b N hp hba hfactor
  calc
    p ∣ q ↔ p ^ (e + 1) ∣ a * N - b :=
      next_adic_lift_iff (a * N - b) p e q hp hfactor
    _ ↔ b ≡ a * N [MOD p ^ (e + 1)] :=
      (Nat.modEq_iff_dvd' hba).symm

end Erdos647
