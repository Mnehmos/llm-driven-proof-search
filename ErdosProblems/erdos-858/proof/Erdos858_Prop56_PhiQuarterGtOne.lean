/-
Erdős Problem #858 — Proposition 5.6 (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

The limiting prime+semiprime density is Φ(u) = log((1-u)/u) + I(u) on [1/4, 1/3),
where the semiprime contribution is the interval integral
  I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv.
Locating the unique root α₂ of Φ(u) = 1 inside (1/4, 1/3) needs the left-endpoint
boundary value Φ(1/4) > 1. Because
  Φ(1/4) = log((1-1/4)/(1/4)) + I(1/4) = log 3 + I(1/4),
with I(1/4) ≥ 0 (the semiprime integral is nonnegative on its nonempty forward
range u ≤ 1/3 — this is the already-verified sign-of-integrand atom
`erdos858_prop56_semiprime_integral_nonneg`, matching #39 at u = 1/4), and
log 3 > 1 (since 3 > e), one gets Φ(1/4) ≥ log 3 > 1.

This is the CONDITIONAL clean atom: it takes I(1/4) ≥ 0 as a hypothesis `Iq ≥ 0`
and proves the endpoint inequality
  1 < log((1-1/4)/(1/4)) + Iq   (i.e. 1 < log 3 + Iq).
Paired with Φ(1/3) = log 2 < 1 (see `erdos858_prop56_core`) and strict
antitonicity of Φ on [1/4, 1/2] (see `erdos858_prop56_full_monotone`), this
Φ(1/4) > 1 boundary pins the root α₂ = 0.2804… strictly inside (1/4, 1/3).

Lean note — the log-3 > 1 lemma path:
  (1-1/4)/(1/4) = 3 by `norm_num`; then
  log 3 > 1  ⟺  exp 1 < 3  via `Real.lt_log_iff_exp_lt (h : 0 < 3)`
  (Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:166), and
  exp 1 < 3 is `Real.exp_one_lt_three`
  (Mathlib/Analysis/Complex/ExponentialBounds.lean:43, namespace Real).
  (`Real.exp_one_lt_d9 : exp 1 < 2.7182818286` at line 37 is the alternative
  route: `lt_trans Real.exp_one_lt_d9 (by norm_num)`.)
  A final `rw` of the fraction to 3 plus `linarith` with `Iq ≥ 0` closes the goal.

Kernel-verified via the proofsearch MCP:
  episode eaf17724-0290-4d5c-b55b-e94cb3d767ec,
  problem_version_id f63f6560-55bd-4595-bb0b-651c95e061b3.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 1dc10454d41f392149e7541a5c67d2932027e5ed85894f04b246322f5971786a.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6, left-endpoint boundary atom: given `I(1/4) ≥ 0` (supplied as
`Iq ≥ 0`, matching the verified semiprime-integral nonnegativity), the density at
`u = 1/4` exceeds `1`:
  `1 < Φ(1/4) = log((1-1/4)/(1/4)) + I(1/4) = log 3 + Iq`.
This `Φ(1/4) > 1` boundary value, with `Φ(1/3) = log 2 < 1` and strict
antitonicity, places the root `α₂` of `Φ = 1` strictly inside `(1/4, 1/3)`. -/
theorem erdos858_prop56_phi_quarter_gt_one :
    ∀ Iq : ℝ, 0 ≤ Iq → 1 < Real.log ((1 - 1/4)/(1/4)) + Iq := by
  intro Iq hIq
  have h3 : ((1 - 1/4)/(1/4) : ℝ) = 3 := by norm_num
  have hlog : (1:ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  rw [h3]
  linarith

end Erdos858
