-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ (R : Multiset ℕ) (m n : ℕ), 0 < R.prod → 1 < m → 1 < n → let g := Nat.gcd m n; let q := Nat.lcm m n / g; (g ::ₘ q ::ₘ R).prod < (m ::ₘ n ::ₘ R).prod ∨ ((g ::ₘ q ::ₘ R).prod = (m ::ₘ n ::ₘ R).prod ∧ ((g ::ₘ q ::ₘ R).filter (fun x => 1 < x)).card < ((m ::ₘ n ::ₘ R).filter (fun x => 1 < x)).card) := by
  intro R m n hR hm hn
  dsimp
  have hd : Nat.gcd m n ∣ Nat.lcm m n :=
    (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  have hpair :
      Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n :=
    Nat.mul_div_cancel' hd
  by_cases hg : Nat.gcd m n = 1
  · right
    have hlcm : Nat.lcm m n = m * n := by
      simpa [hg] using Nat.gcd_mul_lcm m n
    have hq : Nat.lcm m n / Nat.gcd m n = m * n := by
      simp [hg, hlcm]
    have hmn : 1 < m * n := by nlinarith
    have hlcmgt : 1 < Nat.lcm m n := by omega
    constructor
    · simp only [Multiset.prod_cons]
      rw [← Nat.mul_assoc, hpair, hlcm, ← Nat.mul_assoc]
    · simp [Multiset.filter_cons, hg, hlcmgt, hm, hn]
  · left
    have hgpos : 1 < Nat.gcd m n := by
      have : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n (by omega)
      omega
    have hlcmpos : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hlcm : Nat.lcm m n < m * n := by
      have hgl := Nat.gcd_mul_lcm m n
      nlinarith
    simp only [Multiset.prod_cons]
    rw [← Nat.mul_assoc, hpair, ← Nat.mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right hlcm hR

