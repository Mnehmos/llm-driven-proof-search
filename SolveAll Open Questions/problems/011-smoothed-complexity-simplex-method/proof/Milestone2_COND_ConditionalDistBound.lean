/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-COND (conditional piece) (Tier 1, architecture A-COND): distance from a
Gaussian-perturbed vector to a FIXED subspace of codimension ≥ 1, via Mathlib's genuine
`Metric.infDist`.

NOT the open conjecture. This is the per-ω conditional bound the σ_min conditioning step
(M2-COND) consumes: for `N(center, σ²I)`, a fixed subspace `W`, and any unit vector `u ⊥ W`,
`P(dist(x, W) ≤ ε) ≤ 2ε/(σ√(2π))`. Key point: it needs only the EXISTENCE of one unit normal
(not a measurable selection), so it discharges the conditional inequality; the remaining
M2-COND work is purely measure-theoretic (matrix-Gaussian-as-product Fubini + measurable
choice of a normal of the random span of the other columns).

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified). The
tracked root inlines M1/M2.0 and the geometric lemma into one raw_lean_block; this snapshot
presents the equivalent modular form.
  M2-COND  gaussian_dist_subspace_le
           problem_version  337087ce-1a8e-4dc0-bd74-a770082a408a
           episode          b15cd230-3d17-4c8a-be21-0ce0f7d18636
           statement_hash   60ecff763acfc53a482ed79471122e5a8c19f0b065bfef77da63640b21c84c94
           module_source_hash f07c20ce63af1abfd5f1f7a5f3d3aa46838386a737290c859bdcf78c135d702b
           declaration_manifest_hash c28b25389ff59cf685d54c31c67b4e7346116da7fdf7207f761e1f9b686d04f4
           obligation_id    30e3b2f2-b124-4b86-9d3f-1a2e23f9bee2
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` on both roots = [propext, Classical.choice, Quot.sound].
Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2COND

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

/-- (M2.0) single-hyperplane bound. -/
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
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
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
    have h2 : inner ℝ u u = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have h3 : dotProduct (WithLp.ofLp u) (WithLp.ofLp u) = inner ℝ u u := by
      rw [PiLp.inner_apply]; simp [dotProduct, pow_two]
    rw [h3, h2, mul_one]
  exact gaussian_anticoncentration _ t ε σ _
    (by rw [hvar]; exact Real.coe_toNNReal _ (sq_nonneg σ)) hσ hε

/-- Geometric fact: for a unit `u` orthogonal to `W`, `|⟨u,x⟩| ≤ dist(x, W)`. -/
theorem abs_inner_le_infDist_of_perp
    {n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hperp : ∀ w ∈ W, inner ℝ u w = (0 : ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    |inner ℝ u x| ≤ Metric.infDist x (↑W : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [Metric.le_infDist ⟨0, W.zero_mem⟩]
  intro y hy
  have hEq : inner ℝ u x = inner ℝ u (x - y) := by
    rw [inner_sub_right, hperp y hy, sub_zero]
  rw [dist_eq_norm]
  calc |inner ℝ u x| = |inner ℝ u (x - y)| := by rw [hEq]
    _ ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm u (x - y)
    _ = ‖x - y‖ := by rw [hu, one_mul]

/-- **M2-COND conditional bound — distance to a FIXED subspace of codim ≥ 1.**
`P(dist(x, W) ≤ ε) ≤ 2ε/(σ√(2π))` for a unit normal `u ⊥ W`. The per-ω conditional bound
the σ_min conditioning step consumes; needs only existence of one normal. -/
theorem gaussian_dist_subspace_le
    (n : ℕ) (center : EuclideanSpace ℝ (Fin n)) (σ ε : ℝ)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n))
    (hσ : 0 < σ) (hε : 0 ≤ ε) (hu : ‖u‖ = 1) (hperp : ∀ w ∈ W, inner ℝ u w = (0 : ℝ)) :
    ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        {x | Metric.infDist x (↑W : Set (EuclideanSpace ℝ (Fin n))) ≤ ε}
      ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
  have hsub : {x : EuclideanSpace ℝ (Fin n) | Metric.infDist x (↑W : Set _) ≤ ε}
      ⊆ {x | |inner ℝ u x - 0| ≤ ε} := by
    intro x hx
    simp only [Set.mem_setOf_eq, sub_zero]
    exact le_trans (abs_inner_le_infDist_of_perp W u hu hperp x) hx
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact gaussian_hyperplane_anticoncentration n center σ 0 ε u hσ hε hu

end SolveAll011.M2COND

#print axioms SolveAll011.M2COND.gaussian_dist_subspace_le
