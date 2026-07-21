/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-COND (step 3b, a.s.-nonsingularity route) (Tier 1, architecture A-COND): a fixed
Gaussian hyperplane has measure zero.

NOT the open conjecture. For `N(center, σ²I)` and any unit `u`, the affine hyperplane
`{x | ⟨u,x⟩ = t}` is null: `P(⟨u,x⟩ = t) = 0`. Take `ε → 0` in the small-ball bound
`P(|⟨u,x⟩ − t| ≤ ε) ≤ 2ε/(σ√2π)` (M2.0). This is the ELEMENTARY route to a.s.-nonsingularity of
the Gaussian matrix that the σ_min lower-tail needs, avoiding the missing "zero set of a nonzero
polynomial is Lebesgue-null" analytic theorem: `det A = 0` iff column `i` lies in the span of the
other columns, which sits inside a fixed hyperplane normal to any unit `u ⊥` that span; column
`i` (independent of the others, M2-COND3a) avoids that hyperplane a.s. by this lemma, so
`det ≠ 0` a.s.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified). The
tracked root inlines M1/M2.0 into one raw_lean_block; this snapshot presents the modular form.
  M2-COND-3b-hyp0  gaussian_hyperplane_measure_zero
                   problem_version  c2a131a2-c0bd-4207-8ffe-1323458952d5
                   episode          ba309a56-f0a4-4a4e-a258-bcac90018883
                   statement_hash   f7011700ef84a4de44602a8b75f2010087e3d8391d9d24bbcac2f04854901d64
                   module_source_hash 205a0a519152a3c4dabb7b09e3c7359f7d089bfed56c1f1fa44fc9c3c436dd1d
                   declaration_manifest_hash 1d67bd4e7a2e1d3f3435464ebd2d87c3846063722d19de1a899fe9440e87e54b
                   obligation_id    50d84fb5-8165-4c73-96ac-a6907cb4b926
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` = [propext, Classical.choice, Quot.sound].
Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2CONDhyp0

theorem gaussianPDFReal_le_max (m σ x : ℝ) (v : NNReal) (hσ : 0 < σ)
    (hv2 : (v : ℝ) = σ ^ 2) :
    ProbabilityTheory.gaussianPDFReal m v x ≤ (σ * Real.sqrt (2 * Real.pi))⁻¹ := by
  simp only [ProbabilityTheory.gaussianPDFReal_def]
  have hnonpos : -(x - m) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
    rw [hv2]; exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x - m)]) (by positivity)
  have hexp_le : Real.exp (-(x - m) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
    have h0 := Real.exp_le_exp.mpr hnonpos; rwa [Real.exp_zero] at h0
  have hsqrt_eq : Real.sqrt (2 * Real.pi * (v : ℝ)) = σ * Real.sqrt (2 * Real.pi) := by
    rw [hv2, show (2 : ℝ) * Real.pi * σ ^ 2 = σ ^ 2 * (2 * Real.pi) by ring,
      Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]
  rw [hsqrt_eq]
  have hsqrt_pos2 : (0 : ℝ) < σ * Real.sqrt (2 * Real.pi) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hexp_le (inv_pos.mpr hsqrt_pos2).le) (le_of_eq (mul_one _))

theorem gaussian_anticoncentration (m t ε σ : ℝ) (v : NNReal) (hv2 : (v : ℝ) = σ ^ 2)
    (hσ : 0 < σ) (hε : 0 ≤ ε) :
    ProbabilityTheory.gaussianReal m v (Set.Icc (t - ε) (t + ε))
      ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h, NNReal.coe_zero] at hv2; exact (pow_ne_zero 2 hσ.ne') hv2.symm
  rw [ProbabilityTheory.gaussianReal_apply_eq_integral m hv0]
  apply ENNReal.ofReal_le_ofReal
  have hCbound : ∀ x ∈ Set.Icc (t - ε) (t + ε),
      ‖ProbabilityTheory.gaussianPDFReal m v x‖ ≤ (σ * Real.sqrt (2 * Real.pi))⁻¹ := by
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg m v x)]
    exact gaussianPDFReal_le_max m σ x v hσ hv2
  have hmeaslt : MeasureTheory.volume (Set.Icc (t - ε) (t + ε)) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hnorm_le := MeasureTheory.norm_setIntegral_le_of_norm_le_const hmeaslt hCbound
  have hInt_nonneg : (0 : ℝ) ≤ ∫ x in Set.Icc (t - ε) (t + ε), ProbabilityTheory.gaussianPDFReal m v x :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x _ => ProbabilityTheory.gaussianPDFReal_nonneg m v x)
  rw [Real.norm_eq_abs, abs_of_nonneg hInt_nonneg] at hnorm_le
  rw [Real.volume_real_Icc_of_le (show t - ε ≤ t + ε by linarith)] at hnorm_le
  have heq : t + ε - (t - ε) = 2 * ε := by ring
  rw [heq] at hnorm_le
  have hfinal : (σ * Real.sqrt (2 * Real.pi))⁻¹ * (2 * ε) = 2 * ε / (σ * Real.sqrt (2 * Real.pi)) := by ring
  rw [hfinal] at hnorm_le
  exact hnorm_le

theorem gaussian_hyperplane_anticoncentration
    (n : ℕ) (center : EuclideanSpace ℝ (Fin n)) (σ t ε : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hσ : 0 < σ) (hε : 0 ≤ ε) (hu : ‖u‖ = 1) :
    ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        {x | |inner ℝ u x - t| ≤ ε}
      ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
  have hS : (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := Matrix.PosSemidef.one.smul (sq_nonneg σ)
  have hLmeas : Measurable (⇑(innerSL ℝ u)) := (innerSL ℝ u).continuous.measurable
  have hset : {x : EuclideanSpace ℝ (Fin n) | |inner ℝ u x - t| ≤ ε}
      = (⇑(innerSL ℝ u)) ⁻¹' (Set.Icc (t - ε) (t + ε)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, innerSL_apply_apply, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  rw [hset, ← MeasureTheory.Measure.map_apply hLmeas measurableSet_Icc,
    ProbabilityTheory.IsGaussian.map_eq_gaussianReal (innerSL ℝ u)]
  have hmem : MeasureTheory.MemLp id 2
      (ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hvar : ProbabilityTheory.variance (⇑(innerSL ℝ u))
      (ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) = σ ^ 2 := by
    rw [coe_innerSL_apply, ← ProbabilityTheory.covarianceBilin_self hmem u,
      ProbabilityTheory.covarianceBilin_multivariateGaussian hS u u,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    have h2 : inner ℝ u u = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have h3 : dotProduct (WithLp.ofLp u) (WithLp.ofLp u) = inner ℝ u u := by
      rw [PiLp.inner_apply]; simp [dotProduct, pow_two]
    rw [h3, h2, mul_one]
  exact gaussian_anticoncentration _ t ε σ _
    (by rw [hvar]; exact Real.coe_toNNReal _ (sq_nonneg σ)) hσ hε

/-- **A fixed Gaussian hyperplane has measure zero.** `P(⟨u,x⟩ = t) = 0` for a unit `u`, by
`ε → 0` in the small-ball bound. The elementary a.s.-nonsingularity route. -/
theorem gaussian_hyperplane_measure_zero
    (n : ℕ) (center : EuclideanSpace ℝ (Fin n)) (σ t : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hσ : 0 < σ) (hu : ‖u‖ = 1) :
    ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        {x | inner ℝ u x = t} = 0 := by
  set μ := ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) with hμ
  have hbound : ∀ ε : ℝ, 0 < ε → μ {x | inner ℝ u x = t} ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
    intro ε hε
    refine le_trans (MeasureTheory.measure_mono ?_) (gaussian_hyperplane_anticoncentration n center σ t ε u hσ hε.le hu)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hx, sub_self, abs_zero]
    exact hε.le
  by_contra hne
  have hfin : μ {x | inner ℝ u x = t} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  set r := (μ {x | inner ℝ u x = t}).toReal with hr
  have hrpos : 0 < r := ENNReal.toReal_pos hne hfin
  set ε := r * σ * Real.sqrt (2 * Real.pi) / 4 with hε
  have hεpos : 0 < ε := by
    have : 0 < Real.sqrt (2 * Real.pi) := by positivity
    positivity
  have hle := hbound ε hεpos
  have hcalc : 2 * ε / (σ * Real.sqrt (2 * Real.pi)) = r / 2 := by
    have hσne : σ ≠ 0 := hσ.ne'
    have hsqne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    rw [hε]; field_simp; ring
  rw [hcalc] at hle
  have hmu : μ {x | inner ℝ u x = t} = ENNReal.ofReal r := (ENNReal.ofReal_toReal hfin).symm
  rw [hmu, ENNReal.ofReal_le_ofReal_iff (by linarith)] at hle
  linarith

end SolveAll011.M2CONDhyp0

#print axioms SolveAll011.M2CONDhyp0.gaussian_hyperplane_measure_zero
