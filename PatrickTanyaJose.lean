/-
  Patrick / Tanya / José park problem.

  Let `p` = Patrick's speed (mph), `d` = distance (miles).
  - Patrick's total time = Tanya's travel time + 1h:
      d/p = 1 + d/(p+2)   ⟺   2*d = p*(p+2)
  - Patrick's total time = José's travel time + 2h
    (Tanya's speed = p+2, José's speed = p+2+7 = p+9, José left 2h after Patrick):
      d/p = 2 + d/(p+9)   ⟺   9*d = 2*p*(p+9)
  - p > 0  ⟹  unique solution  p = 18/5,  d = 252/25.
  - 252 = 2²·3²·7  and  25 = 5²  are coprime, so the distance is 252/25 miles
    and  m + n = 252 + 25 = 277.

  Kernel-verified via the chatdb-proof-search MCP:
    episode        398e56f6-da6e-4ce1-b11c-fc79cdb84073
    problem_version bb790403-f0fb-4edd-a368-386614bae22e
    outcome        kernel_verified  (termination: root_proved)
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

theorem patrick_tanya_jose_distance :
    ∀ (p d : ℝ), 0 < p → 2 * d = p * (p + 2) → 9 * d = 2 * p * (p + 9) → d = 252 / 25 := by
  intro p d hp h1 h2
  have hpow : 5 * p ^ 2 = 18 * p := by linear_combination 2 * h2 - 9 * h1
  have hprod : p * (5 * p - 18) = 0 := by linear_combination hpow
  have hpval : p = 18 / 5 := by nlinarith [hp, hprod]
  subst hpval
  norm_num at h1
  linarith [h1]
