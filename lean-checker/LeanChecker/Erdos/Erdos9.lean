import Mathlib

/-!
# Erdős Problem #9 — infinitely many odd `n ≠ p + 2^k + 2^l` (Crocker 1971)

Target (corpus `research solved`, shipped `sorry`):
`erdos_9.variants.infinite : Erdos9A.Infinite`, where
`Erdos9A = {n | Odd n ∧ ¬ ∃ p k l, p.Prime ∧ n = p + 2^k + 2^l}`.

**Status: IN PROGRESS (large multi-part construction).** This file banks the
reusable arithmetic core; the full covering assembly is tracked in
`ErdosProblems/erdos-9/attack-plan.md`.

## Banked (kernel-verified)

The Fermat-number divisibility that powers the `a ≠ b` case of Crocker's covering:
if `b − a = 2^s · t` with `t` odd, then the Fermat number `F_s = 2^(2^s) + 1`
divides `2^a + 2^b`. Consequence: `n − 2^a − 2^b ≡ n (mod F_s)`, so choosing `n`
divisible by the relevant Fermat numbers forces the prime `p = n − 2^a − 2^b` to
be divisible by `F_s` (hence composite, barring `p = F_s`).
-/

namespace Erdos9

/-- `(a+1) ∣ (a^t + 1)` for odd `t` (since `a ≡ -1 mod (a+1)` and `(-1)^t = -1`). -/
theorem odd_add_one_dvd_pow_add_one (a t : ℕ) (ht : Odd t) : (a + 1) ∣ (a ^ t + 1) := by
  have hZ : ((a : ℤ) + 1) ∣ ((a : ℤ) ^ t + 1) := by
    have h1 : (a : ℤ) ≡ -1 [ZMOD ((a : ℤ) + 1)] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    have h2 : (a : ℤ) ^ t ≡ (-1) ^ t [ZMOD ((a : ℤ) + 1)] := h1.pow t
    rw [Odd.neg_one_pow ht] at h2
    have h3 : (a : ℤ) ^ t + 1 ≡ 0 [ZMOD ((a : ℤ) + 1)] := by
      have := h2.add_right 1; simpa using this
    exact (Int.modEq_zero_iff_dvd).mp h3
  rw [show ((a : ℤ) + 1) = ((a + 1 : ℕ) : ℤ) by push_cast; ring,
      show ((a : ℤ) ^ t + 1) = ((a ^ t + 1 : ℕ) : ℤ) by push_cast; ring] at hZ
  exact_mod_cast hZ

/-- **Fermat-number divisibility (Crocker's key lemma).** If `b − a = 2^s·t` with
`t` odd, then `2^(2^s) + 1 ∣ 2^a + 2^b`. Stated with `b = a + 2^s·t`. -/
theorem fermat_dvd_two_pow_add (s t a : ℕ) (ht : Odd t) :
    (2 ^ 2 ^ s + 1) ∣ (2 ^ a + 2 ^ (a + 2 ^ s * t)) := by
  have h1 : 2 ^ a + 2 ^ (a + 2 ^ s * t) = 2 ^ a * ((2 ^ 2 ^ s) ^ t + 1) := by
    rw [pow_add, ← pow_mul]; ring
  rw [h1]
  exact Dvd.dvd.mul_left (odd_add_one_dvd_pow_add_one (2 ^ 2 ^ s) t ht) _

end Erdos9
