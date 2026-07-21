/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 1 (Tier 1): Gaussian small-ball / anti-concentration bound.

NOT the open conjecture. This is the standard estimate that every smoothed-analysis
proof in this literature (Spielman-Teng 2004, Dadush-Huiberts 2018, Huiberts-Lee-Zhang
2023/2025) opens with, used to bound the probability that a Gaussian-perturbed scalar
coefficient lands within a small window of a fixed threshold -- i.e. that a perturbed
LP constraint (A = Abar + G, entries of G iid N(0, sigma^2), matching this problem's own
perturbation model) is near-degenerate.

Byte-stamped snapshot of the exact assembled module the verifier kernel-checked.
  problem_version_id: d2f3e8c3-4b2b-4570-981d-2f0c01d76883
  episode_id:          1f3255d1-62b9-4105-bca4-3da2290d5858
  statement_hash:       762c7306e47c38d97b8f925538ad47159750c1ca8c7411fb70af3c026d59699b
  module_source_hash:   fc13e724ac9c50d73d6ae85ac4313b0f32575827a70593f9d19bad6d0c6e3936
  declaration_manifest_hash: 03c802bc07e266a4ac2e4a8c21f6792fd91c986ae899c6370191b6e1b1009644
  lean_environment_hash: 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  outcome: kernel_verified (pass@1, single SubmitModule step, root_proved)
  toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa (this repo's lean-checker pin)

Reproduce: `lake env lean` this file from lean-checker's root (or copy into
LeanChecker/ and adjust the import path if needed).
-/
import Mathlib

namespace SolveAll011.Milestone1

/-- The Gaussian pdf is bounded above by its value at the mode `x = m`:
`(σ * √(2π))⁻¹`. Pure pointwise calculus: the exponential factor has a
nonpositive exponent, hence is `≤ 1`. -/
theorem gaussianPDFReal_le_max (m σ x : ℝ) (v : NNReal) (hσ : 0 < σ)
    (hv2 : (v : ℝ) = σ ^ 2) :
    ProbabilityTheory.gaussianPDFReal m v x ≤ (σ * Real.sqrt (2 * Real.pi))⁻¹ := by
  simp only [ProbabilityTheory.gaussianPDFReal_def]
  have hnonpos : -(x - m) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
    rw [hv2]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x - m)]) (by positivity)
  have hexp_le : Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    have h0 := Real.exp_le_exp.mpr hnonpos
    rwa [Real.exp_zero] at h0
  have hsqrt_eq : Real.sqrt (2 * Real.pi * (v : ℝ)) = σ * Real.sqrt (2 * Real.pi) := by
    rw [hv2, show (2 : ℝ) * Real.pi * σ ^ 2 = σ ^ 2 * (2 * Real.pi) by ring,
      Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
  rw [hsqrt_eq]
  have hsqrt_pos2 : (0 : ℝ) < σ * Real.sqrt (2 * Real.pi) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hexp_le (inv_pos.mpr hsqrt_pos2).le)
    (le_of_eq (mul_one _))

/-- **Gaussian small-ball / anti-concentration bound.** For `X ~ N(m, σ²)` with
`σ > 0`, and any fixed threshold `t` and radius `ε ≥ 0`:
`Pr[|X - t| ≤ ε] ≤ 2ε / (σ√(2π))`.

This is the foundational estimate behind every smoothed-analysis argument for the
simplex method: applied to a single perturbed coefficient `a = ābar + g`
(`g ~ N(0, σ²)`, exactly this problem's perturbation model), it bounds the
probability that `a` lands within `ε` of a degeneracy-inducing threshold `t`. -/
theorem gaussian_anticoncentration (m t ε σ : ℝ) (v : NNReal) (hv2 : (v : ℝ) = σ ^ 2)
    (hσ : 0 < σ) (hε : 0 ≤ ε) :
    ProbabilityTheory.gaussianReal m v (Set.Icc (t - ε) (t + ε))
      ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hv2
    exact (pow_ne_zero 2 hσ.ne') hv2.symm
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral m hv0]
  apply ENNReal.ofReal_le_ofReal
  have hCbound : ∀ x ∈ Set.Icc (t - ε) (t + ε),
      ‖ProbabilityTheory.gaussianPDFReal m v x‖ ≤ (σ * Real.sqrt (2 * Real.pi))⁻¹ := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg m v x)]
    exact gaussianPDFReal_le_max m σ x v hσ hv2
  have hmeas : MeasureTheory.volume (Set.Icc (t - ε) (t + ε)) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hnorm_le := MeasureTheory.norm_setIntegral_le_of_norm_le_const hmeas hCbound
  have hInt_nonneg : (0 : ℝ) ≤ ∫ x in Set.Icc (t - ε) (t + ε), ProbabilityTheory.gaussianPDFReal m v x :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x _ => ProbabilityTheory.gaussianPDFReal_nonneg m v x)
  rw [Real.norm_eq_abs, abs_of_nonneg hInt_nonneg] at hnorm_le
  rw [Real.volume_real_Icc_of_le (show t - ε ≤ t + ε by linarith)] at hnorm_le
  have heq : t + ε - (t - ε) = 2 * ε := by ring
  rw [heq] at hnorm_le
  have hfinal : (σ * Real.sqrt (2 * Real.pi))⁻¹ * (2 * ε) = 2 * ε / (σ * Real.sqrt (2 * Real.pi)) := by
    ring
  rw [hfinal] at hnorm_le
  exact hnorm_le

end SolveAll011.Milestone1
