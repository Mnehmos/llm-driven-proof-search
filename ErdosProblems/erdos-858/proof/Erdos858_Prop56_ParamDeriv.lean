/-
Erdős Problem #858 — Proposition 5.6 (Leibniz rule, PARAMETER/interior half):
differentiation under the integral sign for the parameter-dependent integrand.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 5.6.)

In the monotonicity analysis of the limiting prime+semiprime density Φ one
differentiates the semiprime integral I(u) = ∫_u^{(1-u)/2} f(u,v) dv with
f(u,v) = (1/v)·log((1-u-v)/v). The Leibniz rule splits I'(u) into (a) an endpoint
(variable-limit) contribution — the companion snapshot Erdos858_Prop56_EndpointDeriv
(#44) — and (b) this INTERIOR term ∫ ∂_u f(u,v) dv obtained by differentiating the
integrand under the integral sign, with ∂_u f(u,v) = -(1/(v·(1-u-v))).

This snapshot proves the full interior term (differentiation under ∫) on a fixed
sub-interval [a,b] ⊂ (0,1/2) with the parameter u₀ < 1/2 in its domain: the map
u ↦ ∫_a^b f(u,v) dv is differentiable at u₀ with derivative ∫_a^b ∂_u f(u₀,v) dv.
Positivity of u₀ is not needed; the essential hypotheses are 0 < a ≤ b < 1/2 and
u₀ < 1/2 (together keeping 1-u₀-v > 0 on [a,b]).

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 612606ae-2709-4d1e-828a-57c18a6136aa,
problem_version_id f257dfa9-8391-4b38-b00b-7b300416f936.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a05e646fcc2ba314f413ecb6e53d509d454932d3e7799a86b9cea55bfcfbe75d.
(Verified form: the ∀-quantified statement; here the hypotheses are theorem
binders — definitionally the same proposition. The MCP proof `intro`s them first.)

Lean note (the parametric-integral lemma the pin provides, and its hypotheses).
The pin's differentiation-under-∫ API lives in namespace `intervalIntegral`
(Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean):
- `hasDerivAt_integral_of_dominated_loc_of_deriv_le` {F F' : 𝕜 → ℝ → E} {x₀ : 𝕜}
  {s : Set 𝕜} takes  hs : s ∈ 𝓝 x₀ ;  hF_meas : ∀ᶠ x in 𝓝 x₀,
  AEStronglyMeasurable (F x) (μ.restrict (Ι a b)) ;  hF_int : IntervalIntegrable
  (F x₀) μ a b ;  hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)) ;
  h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t ;  bound_integrable :
  IntervalIntegrable bound μ a b ;  h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s,
  HasDerivAt (fun x => F x t) (F' x t) x ;  and concludes
  IntervalIntegrable (F' x₀) μ a b ∧ HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ)
  (∫ t in a..b, F' x₀ t ∂μ) x₀  (we take `.2`).
  Sibling `hasDerivAt_integral_of_dominated_loc_of_lip` swaps the derivative bound
  for a Lipschitz bound; `..._of_fderiv_le`/`..._of_lip` give the Fréchet forms.

BLOCKING OBLIGATION — none on a fixed [a,b] ⊂ (0,1/2). The domination hypothesis
(h_bound + bound_integrable), which is the only place a `1/v`/`1/(1-u-v)`
singularity could bite, is discharged by a CONSTANT dominator: choose the parameter
neighborhood s = Iio c with c = (u₀+(1-b))/2 < 1-b, so for x < c and v ∈ (a,b]
we get 1-x-v > m₀ := 1-c-b > 0 and v ≥ a > 0, hence |∂_u f| = 1/(v(1-x-v)) ≤
1/(a·m₀), a constant (integrable via `intervalIntegrable_const`). The full lemma is
therefore reachable; no hypothesis blocks it. (The genuine §5 wall is elsewhere:
the sharp Mertens constant / c₂ / Φ numerics, and the DEGENERATE variable-limit
endpoints u, (1-u)/2 where the interval collapses toward v = 0 and 1/v ceases to be
integrable — that endpoint regime, not this interior term, is what needs more.)

Discharge of the remaining hypotheses:
- hF_meas / hF'_meas / hF_int: `ContinuousOn.aestronglyMeasurable` (+ `measurableSet_uIoc`)
  and `ContinuousOn.intervalIntegrable`, with continuity by `ContinuousOn.div₀` +
  `fun_prop` (mirroring the verified Erdos858_Prop56_Continuity snapshot) and
  `ContinuousOn.log` for the non-vanishing log argument.
- h_diff (a.e. HasDerivAt of the parameter map): `hasDerivAt_id.const_sub.sub_const`
  → `.div_const` → `HasDerivAt.log` → `HasDerivAt.const_mul`, with the derivative
  reconciled to -(1/(t(1-x-t))) by `field_simp`.
- hs: `Iio_mem_nhds`;  bound_integrable: `intervalIntegrable_const`.
-/
import Mathlib

open MeasureTheory
open scoped Interval Topology

namespace Erdos858

/-- Proposition 5.6 (Leibniz rule, parameter/interior half): differentiation under
the integral sign for the semiprime integrand on a fixed `[a,b] ⊂ (0,1/2)`. For
`0 < a ≤ b < 1/2` and `u₀ < 1/2`, the parameter-dependent integral
`u ↦ ∫_a^b (1/v)·log((1-u-v)/v) dv` is differentiable at `u₀` with derivative
`∫_a^b -(1/(v·(1-u₀-v))) dv`, i.e. `d/du` passes under `∫`. Together with the
endpoint half (`Erdos858_Prop56_EndpointDeriv`, #44) this is Prop 5.6's Leibniz rule
for `I'(u)`. -/
theorem erdos858_prop56_param_deriv
    (a b u0 : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1 / 2) (hu : u0 < 1 / 2) :
    HasDerivAt (fun u : ℝ => ∫ v in a..b, (1 / v) * Real.log ((1 - u - v) / v))
      (∫ v in a..b, -(1 / (v * (1 - u0 - v)))) u0 := by
  have hcont_gen : ∀ x : ℝ, x < 1 - b →
      ContinuousOn (fun v => (1 / v) * Real.log ((1 - x - v) / v)) (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab]
    have c1 : ContinuousOn (fun v : ℝ => 1 / v) (Set.Icc a b) := by
      apply ContinuousOn.div₀
      · fun_prop
      · fun_prop
      · intro v hv; exact ne_of_gt (lt_of_lt_of_le ha hv.1)
    have c2 : ContinuousOn (fun v : ℝ => Real.log ((1 - x - v) / v)) (Set.Icc a b) := by
      apply ContinuousOn.log
      · apply ContinuousOn.div₀
        · fun_prop
        · fun_prop
        · intro v hv; exact ne_of_gt (lt_of_lt_of_le ha hv.1)
      · intro v hv
        have h1 : (0:ℝ) < 1 - x - v := by linarith [hv.2]
        exact ne_of_gt (div_pos h1 (lt_of_lt_of_le ha hv.1))
    exact c1.mul c2
  have hu1b : u0 < 1 - b := by linarith
  set c : ℝ := (u0 + (1 - b)) / 2 with hc
  have huc : u0 < c := by rw [hc]; linarith
  have hcb : c < 1 - b := by rw [hc]; linarith
  set m0 : ℝ := 1 - c - b with hm
  have hm0 : (0:ℝ) < m0 := by rw [hm]; linarith
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u v => (1 / v) * Real.log ((1 - u - v) / v))
    (F' := fun u v => -(1 / (v * (1 - u - v))))
    (bound := fun _ => 1 / (a * m0))
    (s := Set.Iio c)
    ?hs ?hF_meas ?hF_int ?hF'_meas ?hbound ?hbint ?hdiff).2
  case hs => exact Iio_mem_nhds huc
  case hF_meas =>
    filter_upwards [Iio_mem_nhds hu1b] with x hx
    have hx' : x < 1 - b := hx
    exact ((hcont_gen x hx').mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  case hF_int => exact (hcont_gen u0 hu1b).intervalIntegrable
  case hF'_meas =>
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    apply ContinuousOn.neg
    apply ContinuousOn.div₀
    · fun_prop
    · fun_prop
    · intro v hv
      rw [Set.uIoc_of_le hab] at hv
      have hvpos : (0:ℝ) < v := lt_of_lt_of_le ha (le_of_lt hv.1)
      have hnum : (0:ℝ) < 1 - u0 - v := by linarith [hv.2]
      exact ne_of_gt (mul_pos hvpos hnum)
  case hbound =>
    refine MeasureTheory.ae_of_all _ (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le hab] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hxc : x < c := hx
    have htpos : (0:ℝ) < t := lt_trans ha ht1
    have hxtpos : (0:ℝ) < 1 - x - t := by linarith
    have hD : (0:ℝ) < t * (1 - x - t) := mul_pos htpos hxtpos
    have hm_le : m0 ≤ 1 - x - t := by linarith
    have hle : a * m0 ≤ t * (1 - x - t) :=
      mul_le_mul (le_of_lt ht1) hm_le (le_of_lt hm0) (le_of_lt htpos)
    show ‖-(1 / (t * (1 - x - t)))‖ ≤ 1 / (a * m0)
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos one_pos hD)]
    exact one_div_le_one_div_of_le (mul_pos ha hm0) hle
  case hbint => exact intervalIntegrable_const
  case hdiff =>
    refine MeasureTheory.ae_of_all _ (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le hab] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hxc : x < c := hx
    have htpos : (0:ℝ) < t := lt_trans ha ht1
    have hxtpos : (0:ℝ) < 1 - x - t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have hxtne : (1:ℝ) - x - t ≠ 0 := ne_of_gt hxtpos
    have harg : (1 - x - t) / t ≠ 0 := div_ne_zero hxtne htne
    have hd1 : HasDerivAt (fun u : ℝ => 1 - u - t) (-1 : ℝ) x :=
      ((hasDerivAt_id x).const_sub (1 : ℝ)).sub_const t
    have hd2 : HasDerivAt (fun u : ℝ => (1 - u - t) / t) ((-1 : ℝ) / t) x := hd1.div_const t
    have hd3 : HasDerivAt (fun u : ℝ => Real.log ((1 - u - t) / t))
        (((-1 : ℝ) / t) / ((1 - x - t) / t)) x := hd2.log harg
    have hd4 : HasDerivAt (fun u : ℝ => (1 / t) * Real.log ((1 - u - t) / t))
        ((1 / t) * (((-1 : ℝ) / t) / ((1 - x - t) / t))) x := hd3.const_mul (1 / t)
    have hval : (1 / t) * (((-1 : ℝ) / t) / ((1 - x - t) / t)) = -(1 / (t * (1 - x - t))) := by
      field_simp
    rw [hval] at hd4
    exact hd4

end Erdos858
