-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ (R : Multiset ℕ) (a b : ℕ), (min a b ::ₘ (max a b - min a b) ::ₘ R).gcd = (a ::ₘ b ::ₘ R).gcd := by
  intro R a b
  simp only [Multiset.gcd_cons]
  rw [← gcd_assoc, ← gcd_assoc]
  congr 1
  rcases le_total a b with hab | hba
  · simp only [min_eq_left hab, max_eq_right hab]
    change Nat.gcd a (b - a) = Nat.gcd a b
    simpa using Nat.gcd_sub_self_right hab
  · simp only [min_eq_right hba, max_eq_left hba]
    change Nat.gcd b (a - b) = Nat.gcd a b
    rw [Nat.gcd_sub_self_right hba, Nat.gcd_comm]

