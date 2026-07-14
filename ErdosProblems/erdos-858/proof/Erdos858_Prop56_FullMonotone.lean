/-
Erdős Problem #858 — Proposition 5.6 (FULL monotonicity): Φ is strictly
decreasing on all of [1/4, 1/2].
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 5.6.)

The limiting prime+semiprime density is Φ(u) = log((1-u)/u) + I(u) on [1/4, 1/2],
with the semiprime contribution
  I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv
(nonempty and nonnegative on [1/4, 1/3], vanishing on [1/3, 1/2]).
Proposition 5.6 asserts Φ is continuous and strictly decreasing on [1/4, 1/2].
The paper differentiates Φ by Leibniz' rule: the prime term log((1-u)/u) has
derivative -(1/(u(1-u))) < 0, and the semiprime term satisfies I'(u) ≤ 0
(I'(u) < 0 on (1/4, 1/3) by the paper's sign analysis; I ≡ 0 hence I' = 0 on
(1/3, 1/2)). Therefore Φ'(u) = -(1/(u(1-u))) + I'(u) < 0 throughout the open
interior, so Φ is strictly decreasing on the closed interval [1/4, 1/2].

This snapshot is the deriv-sign → strict-antitonicity capstone of Prop 5.6,
stated conditionally on the Leibniz-rule derivative data and the continuity that
the paper supplies (and that the companion snapshots verify):
  - the continuity of Φ on [1/4, 1/2]  (Erdos858_Prop56_Continuity, the prime
    term on the integral-free interval);
  - the differentiability of I on the open interior with derivative I'  (the two
    Leibniz halves: Erdos858_Prop56_EndpointDeriv #44 — variable-limit endpoint
    contribution — and Erdos858_Prop56_ParamDeriv #55 — interior parameter
    integral);
  - the sign I'(u) ≤ 0 on (1/4, 1/2)  (paper's I'(u) < 0 on (1/4,1/3),
    complementing Erdos858_Prop56_SemiprimeIntegralNonneg I(u) ≥ 0, and I' = 0 on
    (1/3,1/2)).
Given those inputs, the theorem discharges the genuinely new content: the
prime-term derivative computation -(1/(u(1-u))), the interior sign argument, and
the mean-value monotonicity mechanism over the full range [1/4, 1/2]. Together
with the α₂ < 1/3 placement (Erdos858_Prop56_PhiCore) this establishes Prop 5.6's
"Φ strictly decreasing on [1/4, 1/2]" claim.

Kernel-verified via the proofsearch MCP:
  episode 5d49df5c-a730-4e43-b721-bd5f3a89ca78,
  problem_version_id b5933cf5-cf34-477b-8561-373a2b91fe8d.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4fea605deb4271ddfaa736b7e9cb2f7f59194f186e9c90a8e633ad1c5db1f990.

Lean note (the deriv-sign → monotonicity lemma the pin provides):
`strictAntiOn_of_hasDerivWithinAt_neg` (Mathlib/Analysis/Calculus/Deriv/
MeanValue.lean:463):
  {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
  (hf'₀ : ∀ x ∈ interior D, f' x < 0) : StrictAntiOn f D.
Its sibling `strictAntiOn_of_deriv_neg` (:442) uses `deriv f x < 0`; the pointwise
`HasDerivWithinAt` form here avoids naming `deriv`. `hD` is `convex_Icc`;
`interior_Icc` rewrites `interior (Icc a b) = Ioo a b` to expose the strict
bounds. The prime-term derivative is assembled from `(hasDerivAt_id').const_sub`
(for `1 - u`, deriv `-1`), `hasDerivAt_id'` (for `u`, deriv `1`), `HasDerivAt.div`
(quotient rule, deriv `((-1)*x - (1-x)*1)/x^2`), and `HasDerivAt.log` (deriv
`_ / ((1-x)/x)`); the intermediate derivatives are stated in beta-reduced clean
form and accepted by defeq from the combinator terms, then reconciled to
`-(1/(x(1-x)))` by `field_simp; ring` (the context `≠ 0` facts are picked up
automatically). `HasDerivAt.add` folds in the hypothesised `HasDerivAt Ifun (I' x) x`,
and `.hasDerivWithinAt` lifts to the within form, unifying the ambient set with
`interior (Icc …)` directly. The interior sign is `div_pos one_pos (mul_pos …)`
plus `linarith` with `I' x ≤ 0`.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6 (full monotonicity): the limiting prime+semiprime density
`Φ(u) = log((1-u)/u) + I(u)` is strictly decreasing on `[1/4, 1/2]`, given the
Leibniz-rule derivative data the paper supplies — `Φ` continuous on `[1/4,1/2]`,
the semiprime integral `I` differentiable on the open interior `(1/4,1/2)` with
derivative `I'`, and `I' ≤ 0` there. The prime term contributes derivative
`-(1/(u(1-u))) < 0`, so `Φ'(u) = -(1/(u(1-u))) + I'(u) < 0` on the interior and
`Φ` is `StrictAntiOn (Set.Icc (1/4) (1/2))`. -/
theorem erdos858_prop56_full_monotone :
    ∀ (Ifun I' : ℝ → ℝ),
      ContinuousOn (fun u => Real.log ((1 - u) / u) + Ifun u) (Set.Icc (1/4 : ℝ) (1/2)) →
      (∀ u ∈ Set.Ioo (1/4 : ℝ) (1/2), HasDerivAt Ifun (I' u) u) →
      (∀ u ∈ Set.Ioo (1/4 : ℝ) (1/2), I' u ≤ 0) →
      StrictAntiOn (fun u => Real.log ((1 - u) / u) + Ifun u) (Set.Icc (1/4 : ℝ) (1/2)) := by
  intro Ifun I' hcont hderiv hIneg
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (f' := fun u => -(1 / (u * (1 - u))) + I' u)
    (convex_Icc (1/4 : ℝ) (1/2)) hcont ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hu0 : x ≠ 0 := ne_of_gt hxpos
    have h1xpos : (0 : ℝ) < 1 - x := by linarith
    have h1u : (1 : ℝ) - x ≠ 0 := ne_of_gt h1xpos
    have hfrac : (1 - x) / x ≠ 0 := div_ne_zero h1u hu0
    have hnum : HasDerivAt (fun u : ℝ => 1 - u) (-1 : ℝ) x := (hasDerivAt_id' x).const_sub (1 : ℝ)
    have hden : HasDerivAt (fun u : ℝ => u) (1 : ℝ) x := hasDerivAt_id' x
    have hdiv : HasDerivAt (fun u : ℝ => (1 - u) / u)
        (((-1 : ℝ) * x - (1 - x) * 1) / x ^ 2) x := hnum.div hden hu0
    have hlogd : HasDerivAt (fun u : ℝ => Real.log ((1 - u) / u))
        ((((-1 : ℝ) * x - (1 - x) * 1) / x ^ 2) / ((1 - x) / x)) x := hdiv.log hfrac
    have hval : (((-1 : ℝ) * x - (1 - x) * 1) / x ^ 2) / ((1 - x) / x)
        = -(1 / (x * (1 - x))) := by
      field_simp
      ring
    rw [hval] at hlogd
    have hphi : HasDerivAt (fun u : ℝ => Real.log ((1 - u) / u) + Ifun u)
        (-(1 / (x * (1 - x))) + I' x) x := hlogd.add (hderiv x ⟨hx1, hx2⟩)
    exact hphi.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxpos : (0 : ℝ) < x := by linarith
    have h1xpos : (0 : ℝ) < 1 - x := by linarith
    have hprod : (0 : ℝ) < x * (1 - x) := mul_pos hxpos h1xpos
    have hinvpos : (0 : ℝ) < 1 / (x * (1 - x)) := div_pos one_pos hprod
    have hIle : I' x ≤ 0 := hIneg x ⟨hx1, hx2⟩
    show -(1 / (x * (1 - x))) + I' x < 0
    linarith

end Erdos858
