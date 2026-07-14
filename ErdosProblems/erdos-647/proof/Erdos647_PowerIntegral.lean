import Mathlib

/-!
# Erdős #647 — Layer A part 2b: power-law comparison antiderivative

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-13.

  problem_version_id  89b0e678-f69b-427d-9e71-9523856a7cab
  episode_id          1f97aff1-1173-4246-b6dd-06d15ff25ee4
  root_statement_hash cd03a308ddacbad0f6723dfd5c88377d555d9737d0ce99b92a5b4d325db0fe9b
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: `∫_2^x t⁻² dt = 1/2 − 1/x` (for `x ≥ 2`), via `F(t) = −1/t`.

Role: comparison target for the convergent error term in the
`θ(t) ≥ (t−1)log 2 − log(t+2) − 2√t·log t` substitution. For `t ≥ 2`,
`log(t+2) ≤ 2·log t` (since `(t−2)(t+1) ≥ 0`) and
`log t + 1 ≤ (1 + 1/log 2)·log t`, so the `log(t+2)` error integrand
`(log t+1)·log(t+2)/(t²·log²t) ≤ 2(1+1/log 2)·t⁻²`, and this lemma
bounds its integral by `2(1+1/log 2)·(1/2 − 1/x) ≤ 1 + 1/log 2`.
-/

theorem erdos647_power_integral :
    ∀ x : ℝ, 2 ≤ x → ∫ t in (2:ℝ)..x, ((t^2)⁻¹) = (2:ℝ)⁻¹ - x⁻¹ := by
  intro x hx
  have hmain : ∀ t ∈ Set.uIcc (2:ℝ) x, HasDerivAt (fun s => -s⁻¹) ((t^2)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htne : t ≠ 0 := ne_of_gt (by linarith)
    have hi : HasDerivAt (fun s : ℝ => s⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv htne
    have hneg := hi.neg
    have hval : - -(t^2)⁻¹ = (t^2)⁻¹ := by ring
    rw [hval] at hneg
    exact hneg
  have hcont : ContinuousOn (fun t => (t^2)⁻¹) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact pow_ne_zero 2 (ne_of_gt (by linarith))
  have hint : IntervalIntegrable (fun t => (t^2)⁻¹) MeasureTheory.volume 2 x := hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]
  ring
