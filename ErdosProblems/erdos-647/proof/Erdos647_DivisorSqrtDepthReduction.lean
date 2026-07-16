import Mathlib

/-!
# Erdős #647 — universal square-root depth reduction

Every positive integer has at most twice its natural square root many divisors.
The proof injects each divisor into a number below `Nat.sqrt n` together with
one bit recording whether the divisor itself or its complementary divisor is
the small member of the pair.

Consequently, any failed Erdős #647 shift lies before `2 * Nat.sqrt n`.

Proof-search records (2026-07-16):

* divisor bound preverification:
  `df535df7-961a-4fa0-9738-4131052040a6`
* divisor bound problem:
  `5e4145ae-fcc6-4abf-a406-3799f26ca68f`
* divisor bound episode:
  `1ebc813e-b904-40a0-8d26-5b21210ed5ef`
* divisor bound root hash:
  `cfeb6fc408b21357235defeaead012f71bc6c3eef28c147cb9eb7df3bb48dd8f`
* failed-shift capstone preverification:
  `f3a975e1-72f0-4d2b-b38f-ab6debe7dcfe`
* failed-shift capstone problem:
  `626804ed-b23e-464b-9454-dce500bdfa70`
* failed-shift capstone episode:
  `fe3d50d3-e401-435b-8602-b0ea7d8ee69c`
* failed-shift capstone root hash:
  `0275492af54b6c4fed701a323f00a2193551a658e020cc8147e4e3b46687a237`
* constructive prefix preverification:
  `fed7b02a-fb35-4529-b39c-63ae46561a82`
* constructive prefix problem:
  `4915ccf2-8d6f-44cb-bf11-ea12139ea117`
* constructive prefix episode:
  `30b62a23-f200-4dea-b7a6-eb4d979cf4b4`
* constructive prefix root hash:
  `281b1b0ee4a973c3bb4ad99f74f5784bdbce518e08dbb41291bc17f260707b90`

All three tracked episodes ended `kernel_verified` / `root_proved`.
-/

namespace Erdos647

theorem card_divisors_le_two_mul_sqrt :
    ∀ n : ℕ, 0 < n → n.divisors.card ≤ 2 * Nat.sqrt n := by
  intro n hn
  let f : ℕ → ℕ × Bool := fun d =>
    if d ≤ Nat.sqrt n then (d - 1, false) else (n / d - 1, true)
  let target : Finset (ℕ × Bool) :=
    (Finset.range (Nat.sqrt n)).product (Finset.univ : Finset Bool)
  have hmaps : Set.MapsTo f (n.divisors : Set ℕ) (target : Set (ℕ × Bool)) := by
    intro d hd
    have hdmem : d ∈ n.divisors := hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hdmem
    have hddvd : d ∣ n := Nat.dvd_of_mem_divisors hdmem
    by_cases hsmall : d ≤ Nat.sqrt n
    · simp [f, target, hsmall]
      omega
    · have hmul : d * (n / d) = n := Nat.mul_div_cancel' hddvd
      have hpair := Nat.le_sqrt_of_eq_mul hmul.symm
      have hquot : n / d ≤ Nat.sqrt n := by
        rcases hpair with hd | hq
        · exact False.elim (hsmall hd)
        · exact hq
      have hqpos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd hn hddvd) hdpos
      simp [f, target, hsmall]
      omega
  have hinj : Set.InjOn f (n.divisors : Set ℕ) := by
    intro a ha b hb hab
    have hamem : a ∈ n.divisors := ha
    have hbmem : b ∈ n.divisors := hb
    have hapos : 0 < a := Nat.pos_of_mem_divisors hamem
    have hbpos : 0 < b := Nat.pos_of_mem_divisors hbmem
    have hadvd : a ∣ n := Nat.dvd_of_mem_divisors hamem
    have hbdvd : b ∣ n := Nat.dvd_of_mem_divisors hbmem
    by_cases haS : a ≤ Nat.sqrt n
    · by_cases hbS : b ≤ Nat.sqrt n
      · simp [f, haS, hbS] at hab
        omega
      · simp [f, haS, hbS] at hab
    · by_cases hbS : b ≤ Nat.sqrt n
      · simp [f, haS, hbS] at hab
      · have haqpos : 0 < n / a :=
          Nat.div_pos (Nat.le_of_dvd hn hadvd) hapos
        have hbqpos : 0 < n / b :=
          Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos
        have hq : n / a = n / b := by
          simp [f, haS, hbS] at hab
          omega
        have hmula : a * (n / a) = n := Nat.mul_div_cancel' hadvd
        have hmulb : b * (n / b) = n := Nat.mul_div_cancel' hbdvd
        have hmuleq : a * (n / a) = b * (n / a) := by
          rw [hmula, hq, hmulb]
        exact Nat.eq_of_mul_eq_mul_right haqpos hmuleq
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  dsimp [target] at hcard
  simpa [Finset.card_product, Nat.mul_comm] using hcard

theorem failed_shift_lt_two_mul_sqrt_remainder :
    ∀ n k : ℕ, 0 < k → k < n →
      k + 2 < ArithmeticFunction.sigma 0 (n - k) →
      k + 2 < 2 * Nat.sqrt (n - k) := by
  intro n k hk0 hkn hfail
  have hpos : 0 < n - k := by omega
  have hcard := card_divisors_le_two_mul_sqrt (n - k) hpos
  rw [ArithmeticFunction.sigma_zero_apply] at hfail
  exact lt_of_lt_of_le hfail hcard

theorem failed_shift_lt_two_mul_sqrt :
    ∀ n k : ℕ, 0 < k → k < n →
      k + 2 < ArithmeticFunction.sigma 0 (n - k) →
      k < 2 * Nat.sqrt n := by
  intro n k hk0 hkn hfail
  have hlocal :=
    failed_shift_lt_two_mul_sqrt_remainder n k hk0 hkn hfail
  have hsqrt : Nat.sqrt (n - k) ≤ Nat.sqrt n :=
    Nat.sqrt_le_sqrt (Nat.sub_le n k)
  omega

/-- To verify every shift budget for `n`, it is enough to verify the prefix
`k < 2 * Nat.sqrt n`; every later shift is automatically safe. -/
theorem all_shift_budgets_of_sqrt_prefix :
    ∀ n : ℕ,
      (∀ k : ℕ, 0 < k → k < n → k < 2 * Nat.sqrt n →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2) →
      ∀ k : ℕ, 0 < k → k < n →
        ArithmeticFunction.sigma 0 (n - k) ≤ k + 2 := by
  intro n hpref k hk0 hkn
  by_cases hk : k < 2 * Nat.sqrt n
  · exact hpref k hk0 hkn hk
  · have hpos : 0 < n - k := by omega
    have hcard := card_divisors_le_two_mul_sqrt (n - k) hpos
    have hsqrt : Nat.sqrt (n - k) ≤ Nat.sqrt n :=
      Nat.sqrt_le_sqrt (Nat.sub_le n k)
    rw [ArithmeticFunction.sigma_zero_apply]
    omega

end Erdos647
