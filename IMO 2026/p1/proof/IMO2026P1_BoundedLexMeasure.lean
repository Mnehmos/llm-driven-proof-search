-- proof_body_redacted: false
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib

theorem root_theorem : ∀ P P' k k' : ℕ, k ≤ 2026 → k' ≤ 2026 → (P' < P ∨ (P' = P ∧ k' < k)) → P' * 2027 + k' < P * 2027 + k := by
  intro P P' k k' hk hk' h; omega

