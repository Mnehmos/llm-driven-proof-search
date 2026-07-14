/-
Erdős Problem #858 — Proposition 5.6 (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

Semiprime-integral UPPER bound atom — the reusable analytic tool for tightening
the root α₂ and the constant c₂.

The limiting prime+semiprime density is Φ(u) = log((1-u)/u) + I(u) on [1/4, 1/3),
where the semiprime contribution is the interval integral
  I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv.
Locating the root α₂ of Φ(u)=1 and tightening c₂ = 1/2 + ∫_{α₂}^{1/2}(1-Φ(u))du
requires explicit two-sided bounds on I(u). This is the explicit UPPER bound: on
1/4 < u < 1/3 the integrand g(v) = (1/v)·log((1-u-v)/v) is dominated pointwise on
the domain [u,(1-u)/2] by its left-endpoint value c = (1/u)·log((1-2u)/u), so
  I(u) ≤ ((1-u)/2 - u)·(1/u)·log((1-2u)/u).

Companion to `erdos858_prop56_semiprime_integral_nonneg` (the trivial lower bound
0 ≤ I(u)); together they bracket I(u). The Meissel–Mertens constant cancels in the
interval form, so this bound needs no PNT / Mertens — it is pure real analysis on
an explicit elementary integrand.

Proof sketch: `intervalIntegral.integral_mono_on` compares g to the CONSTANT c on
`Icc u ((1-u)/2)`; the constant integral is `((1-u)/2 - u) • c` via
`intervalIntegral.integral_const` (+ `smul_eq_mul`). Pointwise g(v) ≤ c on the
domain: `1/v ≤ 1/u` (from `one_div_le_one_div_of_le`, u ≤ v > 0) and
`log((1-u-v)/v) ≤ log((1-2u)/u)` (from `Real.log_le_log`, with the ratio
inequality `(1-u-v)/v ≤ (1-2u)/u` reduced by `div_le_div_iff₀` to
`(1-u)(v-u) ≥ 0` and closed by `nlinarith`), both logs nonnegative because
`v ≤ (1-u)/2 ⟹ (1-u-v)/v ≥ 1` (`one_le_div` / `Real.log_nonneg`); combine via
`mul_le_mul`. Integrability of g via `ContinuousOn.intervalIntegrable`, continuity
by `ContinuousOn.div₀` + `ContinuousOn.log` (log argument `1-u-v > 0` since
`v ≤ (1-u)/2`), the constant side via `intervalIntegrable_const`.

Kernel-verified via the proofsearch MCP:
  episode 6b6e60e3-0dbb-434a-b4b1-75230ced871e,
  problem_version_id cd46775a-8f2d-4206-a3a9-e7bee818ea7d.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash cdd270d08c53926fcdf849168f2374a906cd4b50bb3aa1f862ea678ea56e276a.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6, semiprime-integral UPPER bound atom: on `1/4 < u < 1/3` the
semiprime contribution `I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv` to the density
`Φ` is bounded above by the length of its domain times its left-endpoint integrand
value `(1/u)·log((1-2u)/u)`. The reusable analytic tool for tightening `α₂` and `c₂`;
companion to the lower bound `erdos858_prop56_semiprime_integral_nonneg`. -/
theorem erdos858_I_upper_bound :
    ∀ (u : ℝ), 1 / 4 < u → u < 1 / 3 →
      (∫ v in u..(1 - u) / 2, (1 / v) * Real.log ((1 - u - v) / v))
        ≤ ((1 - u) / 2 - u) * ((1 / u) * Real.log ((1 - 2 * u) / u)) := by
  intro u hu1 hu2
  have hu0 : (0:ℝ) < u := by linarith
  have hab : u ≤ (1 - u) / 2 := by linarith
  have hcont : ContinuousOn (fun v => (1 / v) * Real.log ((1 - u - v) / v)) (Set.uIcc u ((1 - u) / 2)) := by
    rw [Set.uIcc_of_le hab]
    have c1 : ContinuousOn (fun v : ℝ => 1 / v) (Set.Icc u ((1 - u) / 2)) := by
      apply ContinuousOn.div₀
      · fun_prop
      · fun_prop
      · intro v hv; exact ne_of_gt (lt_of_lt_of_le hu0 hv.1)
    have c2 : ContinuousOn (fun v : ℝ => Real.log ((1 - u - v) / v)) (Set.Icc u ((1 - u) / 2)) := by
      apply ContinuousOn.log
      · apply ContinuousOn.div₀
        · fun_prop
        · fun_prop
        · intro v hv; exact ne_of_gt (lt_of_lt_of_le hu0 hv.1)
      · intro v hv
        have h1 : (0:ℝ) < 1 - u - v := by linarith [hv.2]
        exact ne_of_gt (div_pos h1 (lt_of_lt_of_le hu0 hv.1))
    exact c1.mul c2
  have hgi : IntervalIntegrable (fun v => (1 / v) * Real.log ((1 - u - v) / v)) MeasureTheory.volume u ((1 - u) / 2) := hcont.intervalIntegrable
  have hci : IntervalIntegrable (fun _ : ℝ => (1 / u) * Real.log ((1 - 2 * u) / u)) MeasureTheory.volume u ((1 - u) / 2) := intervalIntegrable_const
  have hpoint : ∀ v ∈ Set.Icc u ((1 - u) / 2), (1 / v) * Real.log ((1 - u - v) / v) ≤ (1 / u) * Real.log ((1 - 2 * u) / u) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hvpos : 0 < v := lt_of_lt_of_le hu0 hv1
    have h1uv : (0:ℝ) < 1 - u - v := by linarith
    have hinv : 1 / v ≤ 1 / u := one_div_le_one_div_of_le hu0 hv1
    have hval_pos : (0:ℝ) < (1 - u - v) / v := div_pos h1uv hvpos
    have hratio : (1 - u - v) / v ≤ (1 - 2 * u) / u := by
      rw [div_le_div_iff₀ hvpos hu0]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - u by linarith) (show (0:ℝ) ≤ v - u by linarith)]
    have hlog_le : Real.log ((1 - u - v) / v) ≤ Real.log ((1 - 2 * u) / u) := Real.log_le_log hval_pos hratio
    have h1le : (1:ℝ) ≤ (1 - u - v) / v := (one_le_div hvpos).mpr (by linarith)
    have hlog_nonneg : 0 ≤ Real.log ((1 - u - v) / v) := Real.log_nonneg h1le
    have hinv_u_nonneg : (0:ℝ) ≤ 1 / u := le_of_lt (one_div_pos.mpr hu0)
    exact mul_le_mul hinv hlog_le hlog_nonneg hinv_u_nonneg
  calc (∫ v in u..(1 - u) / 2, (1 / v) * Real.log ((1 - u - v) / v))
      ≤ ∫ _ in u..(1 - u) / 2, (1 / u) * Real.log ((1 - 2 * u) / u) :=
        intervalIntegral.integral_mono_on hab hgi hci hpoint
    _ = ((1 - u) / 2 - u) * ((1 / u) * Real.log ((1 - 2 * u) / u)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

end Erdos858
