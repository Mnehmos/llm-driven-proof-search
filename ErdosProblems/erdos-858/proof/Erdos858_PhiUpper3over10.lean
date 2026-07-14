/-
Erdős Problem #858 — Proposition 5.6 / α₂ localization, upper (Chojecki 2026,
"An exact frontier theorem and the asymptotic constant for Erdős problem #858").

Φ(3/10) < 1 — a numeric upper bracket for the critical exponent α₂.

The limiting density is Φ(u) = log((1-u)/u) + I(u). At u = 3/10 = 0.30 the prime
term is log((1-3/10)/(3/10)) = log(7/3), and the semiprime term is bounded above by
the kernel-verified I-upper-bound atom (`erdos858_I_upper_bound`, #74):
  I(3/10) ≤ ((1-u)/2 - u)·(1/u)·log((1-2u)/u)|_{u=3/10}
          = (1/20)·(10/3)·log(4/3) = (1/6)·log(4/3) ≤ (1/6)·(4/3 - 1) = 1/18
(the last step via log(4/3) ≤ 4/3 - 1). Modelling I(3/10) by a parameter `Iq`
with this bound `Iq ≤ 1/18`, we prove Φ(3/10) = log(7/3) + Iq < 1.

The prime-term bound uses the `e`-factoring trick: since 7/3 = e·(7/(3e)) with
7/(3e) < 1, `log(7/3) = 1 + log(7/(3e)) ≤ 1 + (7/(3e) - 1) = 7/(3e) < 17/18`
(the last because e > 2.718 ⟹ 51e > 126), so `log(7/3) + Iq < 17/18 + 1/18 = 1`.

Combined with the α₂ squeeze (`erdos858_alpha2_squeeze`, #79) this yields
**α₂ < 3/10 = 0.30**; together with `erdos858_phi_lower_13over50` (#80, α₂ > 0.26)
it localizes **α₂ ∈ (0.26, 0.30)**, bracketing the true `α₂ = 0.28043830…`. Pure
real analysis (exp/log numerics), no PNT.

Proof: rewrite the argument to 7/3 (`norm_num`, with an explicit ℝ cast so the
rewrite matches); `Real.log_le_sub_one_of_pos` on 7/(3e) with
`log(7/(3e)) = log(7/3) - 1` (`Real.log_div` + `Real.log_exp`) gives
`log(7/3) ≤ 7/(3e)`; `div_lt_iff₀` + `nlinarith [Real.exp_one_gt_d9]` gives
`7/(3e) < 17/18`; `linarith` finishes with `Iq ≤ 1/18`.

Kernel-verified via the proofsearch MCP:
  episode 68d8c206-cc10-493e-8c7d-0575db0f3f5a,
  problem_version_id 41218ee6-3e79-4926-9807-4f06e762eec4.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 07bbbaf3c67c46df0cc702e9bb19f92b00ff15e8bfe62c5bab0cf2fb3610bf56.
-/
import Mathlib

namespace Erdos858

/-- Φ(3/10) < 1: at `u = 3/10 = 0.30` the density prime term is `log(7/3)`, bounded
above by `7/(3e) < 17/18` (via the `e`-factoring `log(7/3) ≤ 7/(3e)`), and the
semiprime term `Iq ≤ 1/18` (from the I-upper bound #74), so `Φ(3/10) < 1`. With the
α₂ squeeze this gives `α₂ < 3/10`. -/
theorem erdos858_phi_upper_3over10 :
    ∀ Iq : ℝ, Iq ≤ 1/18 → Real.log ((1 - 3/10) / (3/10)) + Iq < 1 := by
  intro Iq hIq
  rw [show ((1:ℝ) - 3/10) / (3/10) = 7/3 by norm_num]
  have hepos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have he : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hlogsplit : Real.log (7 / (3 * Real.exp 1)) = Real.log (7/3) - 1 := by
    rw [← div_div, Real.log_div (by norm_num) (ne_of_gt hepos), Real.log_exp]
  have hb := Real.log_le_sub_one_of_pos (show (0:ℝ) < 7/(3*Real.exp 1) by positivity)
  rw [hlogsplit] at hb
  have ht_lt : 7 / (3 * Real.exp 1) < 17/18 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [he]
  linarith

end Erdos858
