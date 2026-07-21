-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ a b : ℕ, Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b := by
  intro a b
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, max_eq_right hab, Nat.gcd_sub_self_right hab]
  · simp [min_eq_right hba, max_eq_left hba, Nat.gcd_sub_self_right hba, Nat.gcd_comm]

