/-
Erdős Problem #858 — toward the exact constant c₂ (Chojecki 2026, "An exact
frontier theorem and the asymptotic constant for Erdős problem #858").

EXACT evaluation of the c₂ integral on [1/3, 1/2] via the fundamental theorem of
calculus — pushing c₂ ≥ 0.610, within 0.009 of the true value, with no PNT.

On [1/3, 1/2] the semiprime term of the density vanishes, so Φ(u) = log((1-u)/u).
With antiderivative F(u) = u + (1-u)·log(1-u) + u·log u (whose derivative is
F'(u) = 1 - log(1-u) + log u = 1 - log((1-u)/u)), the FTC gives
  ∫_{1/3}^{1/2} (1 - log((1-u)/u)) du = F(1/2) - F(1/3)
     = (1/2 - log 2) - (1/3 + (2/3)log(2/3) + (1/3)log(1/3))
     = 1/6 - (5/3)·log 2 + log 3  ≈ 0.1101.
Since α₂ < 1/3 and 1 - Φ ≥ 0 on [α₂, 1/3], this is a lower bound for the c₂
integral, giving **c₂ = 1/2 + ∫_{α₂}^{1/2}(1-Φ) ≥ 1/2 + (1/6 - (5/3)log 2 + log 3)
≈ 0.610** — within 0.009 of the true `c₂ = 0.6187712…`. This demonstrates the c₂
*value* is computable elementary real analysis (the Meissel–Mertens constant
cancels in the interval form): no PNT, no Mertens.

Proof: `intervalIntegral.integral_eq_sub_of_hasDerivAt` with the antiderivative F,
whose `HasDerivAt` at each interior point is built from `HasDerivAt.log`
(`dg.log h1xne` for `log(1-y)`, `id.log hxne` for `log y`), `.mul`, `.add`; the
combinator produces the derivative in `Pi.add` form, matched to `1 - log((1-x)/x)`
by proving their equality (`Real.log_div` + `field_simp` + `ring`) and
`rw [← hD]; exact hsum` (avoiding a `convert` instance mismatch). Endpoint algebra
via `Real.log_inv`/`Real.log_div`.

Kernel-verified via the proofsearch MCP:
  episode 31597512-b410-45d2-b2da-0fc705572eba,
  problem_version_id 0cb0da7f-2dcb-49a1-abf2-7a26541deca5.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c9ea411120f89ee2ea8f9cff2b1839f44de9e0db75bfd879e3d5b56e893b4112.
-/
import Mathlib

namespace Erdos858

/-- Exact c₂ integral on `[1/3,1/2]`: `∫_{1/3}^{1/2}(1 - log((1-u)/u)) du =
1/6 - (5/3)·log 2 + log 3 ≈ 0.110`, via FTC with antiderivative
`F(u) = u + (1-u)log(1-u) + u·log u`. Yields `c₂ ≥ 0.610`, within 0.009 of the
true value — the c₂ value is computable elementary real analysis, no PNT. -/
theorem erdos858_c2_exact_integral_half :
    ∫ u in (1/3:ℝ)..(1/2), (1 - Real.log ((1 - u) / u)) = 1/6 - (5/3) * Real.log 2 + Real.log 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (1/3:ℝ) (1/2),
      HasDerivAt (fun y => y + (1 - y) * Real.log (1 - y) + y * Real.log y) (1 - Real.log ((1 - x) / x)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨hl, hr⟩ := hx
    have hx0 : (0:ℝ) < x := by linarith
    have hx1 : (0:ℝ) < 1 - x := by linarith
    have hxne : x ≠ 0 := ne_of_gt hx0
    have h1xne : (1:ℝ) - x ≠ 0 := ne_of_gt hx1
    have dg : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
    have dlog1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((-1) / (1 - x)) x := dg.log h1xne
    have d2 : HasDerivAt (fun y : ℝ => (1 - y) * Real.log (1 - y)) ((-1) * Real.log (1 - x) + (1 - x) * ((-1) / (1 - x))) x := dg.mul dlog1
    have dlogx : HasDerivAt (fun y : ℝ => Real.log y) (1 / x) x := by simpa using (hasDerivAt_id x).log hxne
    have d3 : HasDerivAt (fun y : ℝ => y * Real.log y) (1 * Real.log x + x * (1 / x)) x := (hasDerivAt_id x).mul dlogx
    have hsum := ((hasDerivAt_id x).add d2).add d3
    have hD : (1 : ℝ) + ((-1) * Real.log (1 - x) + (1 - x) * ((-1) / (1 - x))) + (1 * Real.log x + x * (1 / x)) = 1 - Real.log ((1 - x) / x) := by
      rw [Real.log_div h1xne hxne]; field_simp; ring
    rw [← hD]
    exact hsum
  have hint : IntervalIntegrable (fun u => 1 - Real.log ((1 - u) / u)) MeasureTheory.volume (1/3) (1/2) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.log
    · apply ContinuousOn.div₀
      · fun_prop
      · fun_prop
      · intro u hu; exact ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1)
    · intro u hu
      have h1 : (0:ℝ) < 1 - u := by linarith [hu.2]
      exact ne_of_gt (div_pos h1 (lt_of_lt_of_le (by norm_num) hu.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have l2 : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have l3 : Real.log (1/3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have l23 : Real.log (2/3 : ℝ) = Real.log 2 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  simp only [show (1:ℝ) - 1/2 = 1/2 from by norm_num, show (1:ℝ) - 1/3 = 2/3 from by norm_num, l2, l3, l23]
  ring

end Erdos858
