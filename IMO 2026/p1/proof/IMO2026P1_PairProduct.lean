-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ m n : ℕ, 1 < m → 1 < n → Nat.gcd m n * (Nat.lcm m n / Nat.gcd m n) = Nat.lcm m n ∧ 1 < Nat.lcm m n := by
  intro m n hm hn
  have hgml : Nat.gcd m n ∣ Nat.lcm m n :=
    (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  constructor
  · exact Nat.mul_div_cancel' hgml
  · have hlcm : 0 < Nat.lcm m n := Nat.lcm_pos (by omega) (by omega)
    have hle : m ≤ Nat.lcm m n := Nat.le_of_dvd hlcm (Nat.dvd_lcm_left m n)
    omega

