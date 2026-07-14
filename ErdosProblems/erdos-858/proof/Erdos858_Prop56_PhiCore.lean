/-
Erdős Problem #858 — Proposition 5.6 (real-analytic core): Φ strictly decreasing
and below 1 on the upper range, placing the root α₂ strictly below 1/3.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 5.6.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode f3ae9d6d-5467-4b86-8fc5-6814bf3b2871,
problem_version_id 04bdec8a-73bb-4211-85c9-e271708cef52.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 262f89e3…

Proposition 5.6 states that the limiting prime+semiprime density Φ is continuous
and strictly decreasing on [1/4, 1/2], with Φ(1/4) = 1.2458… > 1 and
Φ(1/3) = log 2 < 1, so there is a unique root α₂ ∈ (1/4, 1/3) of Φ(u) = 1
(numerically α₂ = 0.2804…). On [1/3, 1/2] the semiprime integral term
I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv vanishes (the interval is empty since
(1-u)/2 ≤ u there), so Φ(u) = log((1-u)/u).

This theorem is the self-contained real-analytic core of Prop 5.6 (no analytic
number theory):
  (1) u ↦ log((1-u)/u) is strictly decreasing on (0,1) — the monotonicity the
      paper invokes via d/du log((1-u)/u) = -(1/u)(1/(1-u)) < 0;
  (2) log 2 < 1 — so Φ(1/3) < 1;
  (3) log((1-u)/u) < 1 for all u ∈ [1/3, 1/2), since (1-u)/u ≤ 2 there.
Together these show Φ has no root in [1/3, 1/2] and is strictly decreasing on it,
so the unique solution α₂ of Φ = 1 is strictly below 1/3 — the placement the
paper asserts. The full monotonicity on all of [1/4, 1/2] (via the Leibniz-rule
sign analysis of I'(u) on (1/4,1/3)) is deferred; this is the integral-free part.

Lean note: (1-u)/u = 1/u - 1 (via `sub_div`/`div_self`) turns the fraction
comparison into `one_div_lt_one_div_of_lt`; `Real.log_two_lt_d9` gives log 2 < 1
directly; `div_le_iff₀` reduces (1-u)/u ≤ 2 to u ≥ 1/3.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6, real-analytic core: the prime term `log((1-u)/u)` of `Φ` is
strictly antitone on `(0,1)`, `log 2 < 1`, and `log((1-u)/u) < 1` throughout
`[1/3, 1/2)` — so the root `α₂` of `Φ = 1` lies strictly below `1/3`. -/
theorem erdos858_prop56_core :
    (StrictAntiOn (fun u : ℝ => Real.log ((1 - u) / u)) (Set.Ioo 0 1)) ∧
    (Real.log 2 < 1) ∧
    (∀ u : ℝ, 1 / 3 ≤ u → u < 1 / 2 → Real.log ((1 - u) / u) < 1) := by
  have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  refine ⟨?_, hlog2, ?_⟩
  · intro a ha b hb hab
    show Real.log ((1 - b) / b) < Real.log ((1 - a) / a)
    have ha0 : 0 < a := ha.1
    have hb0 : 0 < b := hb.1
    have hb1 : b < 1 := hb.2
    have h1b : 0 < 1 - b := by linarith
    have hbpos : 0 < (1 - b) / b := by positivity
    have hbne : b ≠ 0 := ne_of_gt hb0
    have hane : a ≠ 0 := ne_of_gt ha0
    have h1 : 1 / b < 1 / a := one_div_lt_one_div_of_lt ha0 hab
    have e1 : (1 - b) / b = 1 / b - 1 := by rw [sub_div, div_self hbne]
    have e2 : (1 - a) / a = 1 / a - 1 := by rw [sub_div, div_self hane]
    have hfrac : (1 - b) / b < (1 - a) / a := by rw [e1, e2]; linarith
    exact Real.log_lt_log hbpos hfrac
  · intro u hu1 hu2
    have hupos : 0 < u := by linarith
    have h1u : 0 < 1 - u := by linarith
    have hfrac_pos : 0 < (1 - u) / u := by positivity
    have hfrac_le : (1 - u) / u ≤ 2 := by rw [div_le_iff₀ hupos]; linarith
    calc Real.log ((1 - u) / u) ≤ Real.log 2 := Real.log_le_log hfrac_pos hfrac_le
      _ < 1 := hlog2

end Erdos858
