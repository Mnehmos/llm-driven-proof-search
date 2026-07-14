import Mathlib

/-!
# Erdős #647 — Layer A part 2b: log(t+2) error integral bound

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-13.

  problem_version_id  8bf294a3-c882-4588-9894-e2fbc8ee0edf
  episode_id          6fa25185-251b-4203-a843-63fc2b0c43e6
  root_statement_hash 935fe42967e7ff964228916ae4a685a231db58b3131fe2f491aff2da5b1c0a61
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: a *uniform* upper bound on the `log(t+2)` error integral from
Chebyshev's effective lower bound `θ(t) ≥ (t−1)log 2 − log(t+2) − 2√t·log t`.
For `x ≥ 2`,

  ∫_2^x (log t + 1)·log(t+2)/(t²·log²t) dt ≤ 1 + 1/log 2   (uniformly in x).

This is the first genuine analytic *inequality* of the density-bound
Layer A (not an antiderivative identity). Proof: pointwise, for `t ≥ 2`,
`log(t+2) ≤ 2·log t` (from `(t−2)(t+1) ≥ 0`) and
`log t + 1 ≤ (1 + 1/log 2)·log t` (from `log t ≥ log 2 > 0`), so the
integrand is `≤ 2(1+1/log 2)·t⁻²`; then `intervalIntegral.integral_mono_on`
against `∫ t⁻² = 1/2 − 1/x ≤ 1/2`. Together with the (analogous) `√t·log t`
error bound and the two main-term antiderivatives, this closes the
`θ`-substitution and yields a quantitative Mertens lower bound
`∑_{p≤x} 1/p ≥ log 2 · log log x − C`.
-/

theorem erdos647_mertens_error_log :
    ∀ x : ℝ, 2 ≤ x →
      (∫ t in (2:ℝ)..x, (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2))
        ≤ 1 + (Real.log 2)⁻¹ := by
  intro x hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := 2 * (1 + (Real.log 2)⁻¹) with hC
  have hCpos : 0 ≤ C := by rw [hC]; positivity
  have hptwise : ∀ t ∈ Set.Icc (2:ℝ) x,
      (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2) ≤ C * (t^2)⁻¹ := by
    intro t ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlog2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    have htsq : t + 2 ≤ t^2 := by nlinarith
    have hlogadd : Real.log (t + 2) ≤ Real.log (t^2) := Real.log_le_log (by linarith) htsq
    have hlogsq : Real.log (t^2) = 2 * Real.log t := by rw [Real.log_pow]; push_cast; ring
    have hAle : Real.log (t + 2) ≤ 2 * Real.log t := by rw [hlogsq] at hlogadd; exact hlogadd
    have hLinv : 1 ≤ (Real.log 2)⁻¹ * Real.log t := by
      have h := mul_le_mul_of_nonneg_left hlog2t (le_of_lt (inv_pos.mpr hlog2pos))
      rwa [inv_mul_cancel₀ (ne_of_gt hlog2pos)] at h
    rw [div_le_iff₀ (by positivity)]
    have hsimp : C * (t^2)⁻¹ * (t^2 * (Real.log t)^2) = C * (Real.log t)^2 := by
      field_simp
    rw [hsimp, hC]
    have h3a : Real.log t ≤ (Real.log 2)⁻¹ * (Real.log t)^2 := by
      have h := mul_le_mul_of_nonneg_right hLinv (le_of_lt hlogtpos)
      rw [one_mul] at h
      nlinarith [h]
    have h1 : (Real.log t + 1) * Real.log (t + 2) ≤ (Real.log t + 1) * (2 * Real.log t) :=
      mul_le_mul_of_nonneg_left hAle (by positivity)
    nlinarith [h1, h3a]
  have hcontlogt : ContinuousOn (fun t => Real.log t) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
  have hcontlogt2 : ContinuousOn (fun t => Real.log (t + 2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    exact Real.continuousOn_log.comp ((continuous_add_right 2).continuousOn)
      (fun t ht => ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
  have hdenne : ∀ t ∈ Set.uIcc (2:ℝ) x, t^2 * (Real.log t)^2 ≠ 0 := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith))) (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith))))
  have hcontLHS : ContinuousOn (fun t => (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) :=
    ((hcontlogt.add continuousOn_const).mul hcontlogt2).div (((continuous_pow 2).continuousOn).mul (hcontlogt.pow 2)) hdenne
  have hcontRHS : ContinuousOn (fun t => C * (t^2)⁻¹) (Set.uIcc (2:ℝ) x) := by
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ ((continuous_pow 2).continuousOn)
    rw [Set.uIcc_of_le hx]
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
  have hintLHS : IntervalIntegrable (fun t => (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x := hcontLHS.intervalIntegrable
  have hintRHS : IntervalIntegrable (fun t => C * (t^2)⁻¹) MeasureTheory.volume 2 x := hcontRHS.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hx hintLHS hintRHS hptwise
  have hpow : ∫ t in (2:ℝ)..x, (t^2)⁻¹ = (2:ℝ)⁻¹ - x⁻¹ := by
    have hmain2 : ∀ t ∈ Set.uIcc (2:ℝ) x, HasDerivAt (fun s => -s⁻¹) ((t^2)⁻¹) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htne : t ≠ 0 := ne_of_gt (by linarith)
      have hi : HasDerivAt (fun s : ℝ => s⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv htne
      have hneg := hi.neg
      have hval : - -(t^2)⁻¹ = (t^2)⁻¹ := by ring
      rw [hval] at hneg
      exact hneg
    have hcpow : ContinuousOn (fun t => (t^2)⁻¹) (Set.uIcc (2:ℝ) x) := by
      apply ContinuousOn.inv₀ ((continuous_pow 2).continuousOn)
      rw [Set.uIcc_of_le hx]
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain2 (hcpow.intervalIntegrable)]
    ring
  rw [intervalIntegral.integral_const_mul, hpow] at hmono
  have hfinal : C * ((2:ℝ)⁻¹ - x⁻¹) ≤ 1 + (Real.log 2)⁻¹ := by
    have hxpos : (0:ℝ) < x := by linarith
    have hprod : 0 ≤ C * x⁻¹ := mul_nonneg hCpos (by positivity)
    have hChalf : C * (2:ℝ)⁻¹ = 1 + (Real.log 2)⁻¹ := by rw [hC]; ring
    nlinarith [hprod, hChalf]
  linarith [hmono, hfinal]
