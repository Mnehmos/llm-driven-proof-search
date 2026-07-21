-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ m n p : ℕ, m ≠ 0 → n ≠ 0 → Nat.Prime p → (Nat.gcd m n).factorization p = min (m.factorization p) (n.factorization p) ∧ (Nat.lcm m n / Nat.gcd m n).factorization p = max (m.factorization p) (n.factorization p) - min (m.factorization p) (n.factorization p) := by
  intro m n p hm hn hp
  have hd : Nat.gcd m n ∣ Nat.lcm m n :=
    (Nat.gcd_dvd_left m n).trans (Nat.dvd_lcm_left m n)
  constructor
  · rw [Nat.factorization_gcd hm hn]
    rfl
  · rw [Nat.factorization_div hd, Nat.factorization_lcm hm hn,
      Nat.factorization_gcd hm hn]
    rfl

