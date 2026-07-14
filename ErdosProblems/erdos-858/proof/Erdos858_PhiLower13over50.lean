/-
Erdős Problem #858 — Proposition 5.6 / α₂ localization, lower (Chojecki 2026,
"An exact frontier theorem and the asymptotic constant for Erdős problem #858").

Φ(13/50) > 1 — a numeric lower bracket for the critical exponent α₂.

The limiting density is Φ(u) = log((1-u)/u) + I(u) with the semiprime term
I(u) ≥ 0 (kernel-verified, `erdos858_prop56_semiprime_integral_nonneg`). At
u = 13/50 = 0.26 the prime term alone exceeds 1: `(1-13/50)/(13/50) = 37/13 ≈
2.846 > e`, so `log(37/13) > 1`; adding the nonnegative semiprime term keeps
Φ(13/50) > 1. Modelling I(13/50) by a nonnegative parameter `Iq` (justified by
the `I(u) ≥ 0` atom), this establishes Φ(13/50) > 1.

Combined with the α₂ squeeze (`erdos858_alpha2_squeeze`: Φ strictly antitone with
unique root Φ(α₂)=1) this yields **α₂ > 13/50 = 0.26** — a tightening of the prior
localization `α₂ ∈ (1/4, 1/3)` toward the true `α₂ = 0.28043830…`. Pure real
analysis (exp/log numerics), no PNT.

Proof: `Real.exp_one_lt_d9` gives `exp 1 < 2.7182818286 < 37/13` (the last by
`norm_num` + `linarith`); then `1 = log(exp 1) < log(37/13)` via `Real.log_lt_log`
(with `Real.log_exp`), and the nonnegative `Iq` is added by `linarith`.

Kernel-verified via the proofsearch MCP:
  episode 8be64996-ed40-4b7a-92de-268b67b1488e,
  problem_version_id a4924eca-7194-4cee-bf50-fc66a8a62104.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash b2c5b6a9f4faceebb4a2bc6a4902b8163d7ed4e33c0651210bc58a0305587c93.
-/
import Mathlib

namespace Erdos858

/-- Φ(13/50) > 1: at `u = 13/50 = 0.26` the density prime term `log((1-u)/u) =
log(37/13) > 1` (since `37/13 > e`), so adding the nonnegative semiprime term
`Iq ≥ 0` keeps `Φ(13/50) > 1`. With the α₂ squeeze this gives `α₂ > 13/50`. -/
theorem erdos858_phi_lower_13over50 :
    ∀ Iq : ℝ, 0 ≤ Iq → 1 < Real.log ((1 - 13/50) / (13/50)) + Iq := by
  intro Iq hIq
  have hlt : Real.exp 1 < (1 - 13/50) / (13/50) := by
    have h2 : (2.7182818286 : ℝ) < (1 - 13/50) / (13/50) := by norm_num
    linarith [Real.exp_one_lt_d9]
  have hprime : (1:ℝ) < Real.log ((1 - 13/50) / (13/50)) := by
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log ((1 - 13/50) / (13/50)) := Real.log_lt_log (Real.exp_pos 1) hlt
  linarith

end Erdos858
