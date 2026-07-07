import Mathlib

/-!
# Erdős Problem #399 — Cambie's mod-8 companion

Erdős #399 asks whether `n! = x^k ± y^k` has solutions with `xy > 1`, `k > 2`.
(The full answer is *no it's not solution-free* — Barfield's `10! = 48⁴ − 36⁴`.)

This file proves the **already-known companion** attributed to Cambie: there is
no solution to `n! = x⁴ + y⁴` with `gcd(x,y) = 1` and `xy > 1`. The corpus ships
`erdos_399.variants.cambie` as `sorry`; this is a self-contained, kernel-verified
proof, via the mod-8 argument the docstring points to.

## Proof

Fourth powers mod 8: `odd⁴ ≡ 1`, `even⁴ ≡ 0` (indeed `a⁴ ≡ a (mod 2)` as a
residue mod 8). If `gcd(x,y)=1` then `x,y` are not both even, so
`x⁴ + y⁴ ≡ 1 or 2 (mod 8)`, never `0`. For `n ≥ 4`, `8 ∣ n!`, so `n!` *is*
`≡ 0 (mod 8)` — contradiction. For `n ≤ 3`, `n! ≤ 6`, while `xy > 1` forces
`x⁴ + y⁴ ≥ 17`. Either way `n! ≠ x⁴ + y⁴`. ∎
-/

namespace Erdos399

open Nat

/-- Fourth powers mod 8 detect parity: `a⁴ % 8 = a % 2`. -/
lemma pow4_mod8 (a : ℕ) : a ^ 4 % 8 = a % 2 := by
  have h1 : a ^ 4 % 8 = (a % 8) ^ 4 % 8 := by rw [Nat.pow_mod]
  have h2 : a % 2 = (a % 8) % 2 := by omega
  rw [h1, h2]
  have : a % 8 < 8 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 8) <;> decide

/-- **Erdős #399, Cambie's companion.** No `n! = x⁴ + y⁴` with `gcd(x,y)=1`,
`xy > 1`. The corpus ships this as `sorry`. -/
theorem cambie {n x y : ℕ} (hxy : x.Coprime y) (h1 : 1 < x * y) :
    n ! ≠ x ^ 4 + y ^ 4 := by
  intro heq
  -- x, y are each ≥ 1 (else x*y = 0)
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · simp at h1
    · exact h
  have hy1 : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with rfl | h
    · simp at h1
    · exact h
  -- x, y are not both even (coprimality)
  have hpar : x % 2 = 1 ∨ y % 2 = 1 := by
    by_contra h
    simp only [not_or] at h
    obtain ⟨hx, hy⟩ := h
    have hgx : 2 ∣ x := by omega
    have hgy : 2 ∣ y := by omega
    have : (2 : ℕ) ∣ Nat.gcd x y := Nat.dvd_gcd hgx hgy
    rw [Nat.Coprime] at hxy
    omega
  -- residue of x⁴ + y⁴ mod 8 is 1 or 2, never 0
  have hmod : (x ^ 4 + y ^ 4) % 8 = (x % 2 + y % 2) % 8 := by
    rw [Nat.add_mod, pow4_mod8, pow4_mod8]
  have hx2 : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hy2 : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (Nat.lt_or_ge n 4).symm with hn | hn
  · -- n ≥ 4 ⟹ 8 ∣ n!, but 8 ∤ x⁴ + y⁴
    have hdvd4 : (8 : ℕ) ∣ 4 ! := by decide
    have h8 : (8 : ℕ) ∣ n ! := hdvd4.trans (Nat.factorial_dvd_factorial hn)
    rw [heq, Nat.dvd_iff_mod_eq_zero, hmod] at h8
    omega
  · -- n ≤ 3 ⟹ n! ≤ 6, but x⁴ + y⁴ ≥ 17
    have hnle : n ! ≤ 6 := by
      calc n ! ≤ 3 ! := Nat.factorial_le (by omega)
        _ = 6 := rfl
    have hbig : 17 ≤ x ^ 4 + y ^ 4 := by
      have hone : 2 ≤ x ∨ 2 ≤ y := by
        by_contra h
        simp only [not_or, not_le] at h
        obtain ⟨hx, hy⟩ := h
        have : x * y ≤ 1 * 1 := Nat.mul_le_mul (by omega) (by omega)
        omega
      rcases hone with h | h
      · have hxp : 2 ^ 4 ≤ x ^ 4 := Nat.pow_le_pow_left h 4
        have hyp : 1 ≤ y ^ 4 := Nat.one_le_pow _ _ hy1
        omega
      · have hyp : 2 ^ 4 ≤ y ^ 4 := Nat.pow_le_pow_left h 4
        have hxp : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ hx1
        omega
    omega

end Erdos399
