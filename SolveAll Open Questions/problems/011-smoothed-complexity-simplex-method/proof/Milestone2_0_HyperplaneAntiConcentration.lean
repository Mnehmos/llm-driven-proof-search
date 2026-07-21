/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2.0 (Tier 1, A-COND architecture): distance from a Gaussian-perturbed vector
to a fixed hyperplane.

NOT the open conjecture. This is the first genuinely joint/geometric rung of the
Rudelson–Vershynin distance-to-subspace route toward smallest-singular-value
anti-concentration (M2). It lifts the scalar small-ball bound M1 to a multivariate
Gaussian: for an isotropic-covariance perturbation N(center, σ²I) on
`EuclideanSpace ℝ (Fin n)` with ARBITRARY center (matching the smoothed-analysis
adversary A = Ābar + G, entries of G i.i.d. N(0,σ²)), any unit normal `u` and any
threshold `t`, the probability that `x` lands in the ε-slab around the affine
hyperplane `{x | ⟪u,x⟫ = t}` — whose signed distance for a unit normal is exactly
`|⟪u,x⟫ − t|` — is at most `2ε/(σ√(2π))`.

The reduction: the pushforward of `multivariateGaussian center (σ²I)` under the
continuous linear functional `⟪u,·⟫` is a 1-D `gaussianReal` (Mathlib's
`IsGaussian.map_eq_gaussianReal`), with variance `uᵀ(σ²I)u = σ²·‖u‖² = σ²`
(computed exactly via `covarianceBilin_multivariateGaussian`). M1 is uniform in the
mean, so the arbitrary center passes through untouched. No independence beyond the
Gaussian law is used.

What it says: "a Gaussian-perturbed point is unlikely to lie in a thin slab around
one fixed hyperplane." What it does NOT yet say: anything about a *matrix* being
near-singular (the joint σ_min statement, M2), which requires a union/net argument
over the `n` columns built on top of this per-hyperplane bound.

Tracked, kernel-verified (fidelity `attested`, dev-mode; caps at kernel_verified,
never certified):
  problem_version_id: ff02637d-bdd8-4989-aff3-70f2decac8ee
  episode_id:          851ff2ce-de85-4164-a274-024f4f2bcac3
  statement_hash:       7031dca12c656cb4dbd9602e90746e1f8223fc438f6aebe5ffcf2895d18b19e4
  module_source_hash:   55538342234cf14e98f0f45f5ace408f29b83a665412e991d769ebf39980832a
  declaration_manifest_hash: dd5b7bbb3e18fec36bd8f79cf4c7d6c4477ca5d07140fabad76e5eb47b3bd7e5
  lean_environment_hash: 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  obligation_id:        c507ce88-aa33-4d33-b39a-1f60e3c4d52d
  outcome: kernel_verified (root_proved; second submission — first failed on a
    helper-transport artifact, not a mathematical error; see trace/trajectory.md)
  toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa (this repo's pin)

`#print axioms` on the root reports exactly [propext, Classical.choice, Quot.sound]
— the standard Mathlib axioms, no `sorryAx`, no `admit`, no project-defined axioms.

Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2_0

/-- (M1 helper, reused) The Gaussian pdf is bounded above by its mode value. -/
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

/-- (M1, reused) Gaussian small-ball / anti-concentration bound. -/
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

/-- **M2.0 — Gaussian vector near a fixed hyperplane.** For a multivariate Gaussian
with arbitrary `center` and isotropic covariance `σ²·I` on `EuclideanSpace ℝ (Fin n)`,
any unit vector `u` (`‖u‖ = 1`) and any threshold `t`, the probability that the
projection `⟪u, x⟫` lands within `ε` of `t` — i.e. that `x` falls in the ε-slab around
the affine hyperplane `{x | ⟪u,x⟫ = t}` — is at most `2ε/(σ√(2π))`.

The bound is uniform over the adversary's `center` (M1 does not see the mean), and the
variance of the projection is computed exactly as `uᵀ(σ²I)u = σ²`. -/
theorem gaussian_hyperplane_anticoncentration
    (n : ℕ) (center : EuclideanSpace ℝ (Fin n)) (σ t ε : ℝ) (u : EuclideanSpace ℝ (Fin n))
    (hσ : 0 < σ) (hε : 0 ≤ ε) (hu : ‖u‖ = 1) :
    ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        {x | |inner ℝ u x - t| ≤ ε}
      ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
  have hS : (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sq_nonneg σ)
  have hLmeas : Measurable (⇑(innerSL ℝ u)) := (innerSL ℝ u).continuous.measurable
  have hset : {x : EuclideanSpace ℝ (Fin n) | |inner ℝ u x - t| ≤ ε}
      = (⇑(innerSL ℝ u)) ⁻¹' (Set.Icc (t - ε) (t + ε)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, innerSL_apply_apply, abs_le]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  rw [hset, ← MeasureTheory.Measure.map_apply hLmeas measurableSet_Icc,
    ProbabilityTheory.IsGaussian.map_eq_gaussianReal (innerSL ℝ u)]
  have hmem : MeasureTheory.MemLp id 2
      (ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hvar : ProbabilityTheory.variance (⇑(innerSL ℝ u))
      (ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)))
      = σ ^ 2 := by
    rw [coe_innerSL_apply, ← ProbabilityTheory.covarianceBilin_self hmem u,
      ProbabilityTheory.covarianceBilin_multivariateGaussian hS u u,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    have h2 : inner ℝ u u = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have h3 : dotProduct (WithLp.ofLp u) (WithLp.ofLp u) = inner ℝ u u := by
      rw [PiLp.inner_apply]
      simp [dotProduct, pow_two]
    rw [h3, h2, mul_one]
  exact gaussian_anticoncentration _ t ε σ _
    (by rw [hvar]; exact Real.coe_toNNReal _ (sq_nonneg σ)) hσ hε

end SolveAll011.M2_0

#print axioms SolveAll011.M2_0.gaussian_hyperplane_anticoncentration
