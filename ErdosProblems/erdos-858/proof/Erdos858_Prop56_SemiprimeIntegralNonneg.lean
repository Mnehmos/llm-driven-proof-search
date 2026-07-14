/-
Erdős Problem #858 — Proposition 5.6 (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

The limiting prime+semiprime density is Φ(u) = log((1-u)/u) + I(u) on [1/4, 1/3),
where the semiprime contribution is the interval integral
  I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv.
The paper differentiates Φ via Leibniz' rule (variable upper endpoint (1-u)/2,
variable lower endpoint u, and an integrand depending on the parameter u through
the factor 1-u-v) to prove Φ strictly decreasing on [1/4, 1/2]. A prerequisite
sign input to that analysis is that the semiprime integral I(u) is nonnegative on
its nonempty range: for u ∈ (0, 1/3] the domain is nonempty (u ≤ (1-u)/2) and the
integrand is pointwise nonnegative there — for every v ∈ [u, (1-u)/2] one has
v ≤ (1-u)/2, hence (1-u-v)/v ≥ 1, so log((1-u-v)/v) ≥ 0, and 1/v > 0. Therefore
I(u) ≥ 0: the semiprime term never decreases the density. This is the "sign of the
integrand" atom of the Prop 5.6 Leibniz argument, complementing the already-verified
prime-term antitonicity core (Erdos858_Prop56_PhiCore).

Lean note: intervalIntegral.integral_nonneg (hab : a ≤ b) (hf : ∀ u ∈ Icc a b,
0 ≤ f u) is UNCONDITIONAL — it needs no IntervalIntegrable hypothesis, sidestepping
the 1/v·log singularity structure entirely. The pointwise nonnegativity is pure
ordered-field/log algebra: `one_le_div` turns v ≤ 1-u-v into 1 ≤ (1-u-v)/v, then
`Real.log_nonneg` and `mul_nonneg` finish. Orientation caveat: this uses the forward
domain u ≤ (1-u)/2, valid exactly for u ≤ 1/3; for u > 1/3 the Lean `intervalIntegral`
is the orientation-reversed negative (nonzero), NOT the paper's set-integral-vanishes
reading of "I(u) = 0 on [1/3, 1/2]".

Kernel-verified via the proofsearch MCP:
  episode a4afd2d6-e146-4144-b1e7-e3acd0759fcf,
  problem_version_id 8cc9e844-3efa-42a3-9aba-96c6ca698cb0.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 34cf2b70a980f9878decdbabd05a4181edbe58ad54b5bf6bcf78d851a425e52a.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6, semiprime-integral sign atom: the semiprime contribution
`I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv` to the density `Φ` is nonnegative on
its nonempty forward range `u ∈ (0, 1/3]`. This is the "sign of the integrand" input
to the Leibniz-rule monotonicity argument of Prop 5.6. -/
theorem erdos858_prop56_semiprime_integral_nonneg :
    ∀ (u : ℝ), 0 < u → u ≤ 1 / 3 →
      0 ≤ ∫ v in u..(1 - u) / 2, (1 / v) * Real.log ((1 - u - v) / v) := by
  intro u hu0 hu3
  have hab : u ≤ (1 - u) / 2 := by linarith
  apply intervalIntegral.integral_nonneg hab
  intro v hv
  obtain ⟨hv1, hv2⟩ := hv
  have hvpos : 0 < v := lt_of_lt_of_le hu0 hv1
  have hle : v ≤ 1 - u - v := by linarith
  have h1le : 1 ≤ (1 - u - v) / v := (one_le_div hvpos).mpr hle
  have hlog : 0 ≤ Real.log ((1 - u - v) / v) := Real.log_nonneg h1le
  have hinv : (0:ℝ) ≤ 1 / v := le_of_lt (one_div_pos.mpr hvpos)
  exact mul_nonneg hinv hlog

end Erdos858
