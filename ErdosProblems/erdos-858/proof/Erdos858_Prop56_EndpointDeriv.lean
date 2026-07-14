/-
Erdős Problem #858 — Proposition 5.6 (Leibniz endpoint contribution).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 5.6.)

In the Leibniz decomposition of d/du of the semiprime-density integral
I(u) = ∫_u^{(1-u)/2} f(u,v) dv, the total derivative splits into (a) an interior
term ∫_u^{(1-u)/2} ∂_u f(u,v) dv from differentiating the integrand, and (b) an
endpoint (variable-limit) contribution from the two u-dependent limits of
integration. This snapshot isolates part (b): treating the integrand as a FIXED
continuous function g (parameter frozen), the map u ↦ ∫_{v=u}^{(1-u)/2} g(v) dv has
derivative g((1-u)/2)·(-1/2) − g(u). The upper limit (1-u)/2 (derivative -1/2)
contributes +g((1-u)/2)·(-1/2); the lower limit u (derivative 1) contributes
−g(u) — the classical two-variable-endpoint form of the Fundamental Theorem of
Calculus. It holds at every real u for continuous g (no interior-interval
restriction is needed). This is the endpoint half of Prop 5.6's Leibniz rule; the
companion interior term still requires a parametric-integral differentiation lemma.

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode da32aac2-8925-49d8-917a-baf7fc9c99e8,
problem_version_id 08d7b8fc-b1dd-431c-aba7-c12c8c598c77.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 554f37d691a29304b33be047f7dcdd892088f20192b94dbdbb8c432506638ece.

Lean note (FTC lemmas the pin provides — all in namespace `intervalIntegral`,
Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean):
- `integral_hasFDerivAt` (2-variable Fréchet FTC-1): HasFDerivAt of
  `(p ↦ ∫ x in p.1..p.2, f x)` at `(a,b)` with fderiv
  `(snd).smulRight (f b) - (fst).smulRight (f a)`; hypotheses IntervalIntegrable +
  StronglyMeasurableAtFilter (×2) + ContinuousAt (×2), all discharged here from
  `Continuous g` (Continuous.intervalIntegrable, Continuous.aestronglyMeasurable.
  stronglyMeasurableAtFilter, Continuous.continuousAt).
- single-endpoint forms also present: `integral_hasDerivAt_right` (`u ↦ ∫ a..u`,
  deriv `f b`) and `integral_hasDerivAt_left` (`u ↦ ∫ u..b`, deriv `-f a`), plus
  the `_of_tendsto_ae` and `WithinAt`/`FTCFilter` one-sided variants.
The full 2-variable-endpoint form is therefore reachable directly by composing
`integral_hasFDerivAt` with the endpoint curve `γ(w) = (w, (1-w)/2)` (whose
HasDerivAt `(1, -1/2)` comes from `hasDerivAt_id`.prodMk of `const_sub`/`div_const`)
via `HasFDerivAt.comp_hasDerivAt`; no split into two single-endpoint pieces is
needed. The composed derivative `L (1, -1/2)` is reconciled to the clean scalar
`g((1-u)/2)*(-1/2) - g u` by `simp [ContinuousLinearMap.sub_apply, smulRight_apply,
coe_snd', coe_fst', smul_eq_mul]` + `ring`.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6 (Leibniz endpoint contribution): for a fixed continuous
`g : ℝ → ℝ`, the variable-limit integral `u ↦ ∫_{v=u}^{(1-u)/2} g v` has derivative
`g((1-u)/2)·(-1/2) − g u` at every `u`. This is the endpoint (variable-limit) half
of the Leibniz decomposition of `d/du` of `I(u) = ∫_u^{(1-u)/2} f(u,v) dv`, with the
integrand frozen; the upper endpoint `(1-u)/2` (derivative `-1/2`) and lower endpoint
`u` (derivative `1`) contribute via the two-variable-endpoint FTC. -/
theorem erdos858_prop56_endpoint_deriv :
    ∀ (g : ℝ → ℝ), Continuous g → ∀ (u : ℝ),
      HasDerivAt (fun w => ∫ v in w..(1 - w) / 2, g v)
        (g ((1 - u) / 2) * (-1 / 2) - g u) u := by
  intro g hg u
  have hF := intervalIntegral.integral_hasFDerivAt
    (f := g) (a := u) (b := (1 - u) / 2)
    (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter
    hg.continuousAt hg.continuousAt
  have hγ : HasDerivAt (fun w : ℝ => (w, (1 - w) / 2)) ((1 : ℝ), (-1 / 2 : ℝ)) u :=
    (hasDerivAt_id u).prodMk (((hasDerivAt_id u).const_sub 1).div_const 2)
  have hcomp := hF.comp_hasDerivAt u hγ
  have key :
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (g ((1 - u) / 2))
          - (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (g u)) ((1 : ℝ), (-1 / 2 : ℝ)))
        = g ((1 - u) / 2) * (-1 / 2) - g u := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', smul_eq_mul]
    ring
  rw [key] at hcomp
  exact hcomp

end Erdos858
