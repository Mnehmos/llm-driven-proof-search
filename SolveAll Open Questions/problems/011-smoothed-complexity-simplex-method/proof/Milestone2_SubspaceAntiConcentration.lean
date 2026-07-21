/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2 tower (Tier 1, architecture A-COND): distance from a Gaussian-perturbed
vector to a fixed subspace, with the sharp codimension gain.

NOT the open conjecture. This lifts the M1/M2.0 scalar and single-hyperplane bounds to
the multivariate JOINT statement the Rudelson–Vershynin smallest-singular-value argument
consumes: for an isotropic Gaussian N(center, σ²I) and an arbitrary orthonormal family
u : Fin k → ℝⁿ (an orthonormal basis of the orthogonal complement of a codimension-k
subspace, in ARBITRARY orientation), the probability that all k projections land in their
ε-windows is ≤ (2ε/(σ√(2π)))^k — the full k-th power. The content is that distinct
projections of an isotropic Gaussian are INDEPENDENT (proved, not assumed, from the σ²I
covariance + orthonormality), so the joint slab probability factorizes into a product of
k one-dimensional M1 marginals.

Tracked, kernel-verified roots (fidelity `attested`, dev-mode; caps at kernel_verified):

  M2.1  gaussian_two_coord_anticoncentration  (codimension-2, coordinate-aligned)
        problem_version  c548e3fe-04a2-46ad-8d69-5cebc531f015
        episode          10653478-f63b-4704-8761-cb3cec0cc503
        statement_hash   dd3b81bd871f967c55ffb4fe6f1ac4614313e5aadd888a13a98de8985639bf91
        module_source_hash 0665a4404c00dd8be0de25322676449b121ad2377687076813172c78d62713d9
        obligation_id    d7fd24d1-6aef-40c9-9bc5-4a9cbbef1bde

  M2.2  gaussian_subspace_anticoncentration  (general, arbitrary orientation, codim k)
        problem_version  4a4d86dd-175c-4a0e-86f3-f1656e629c64
        episode          ea3c53fe-fca3-4764-b89d-26a5d9546654
        statement_hash   3ad10c1dd02b569b30d76e57863563a324a708c6d01b7114024bcbc43f99353f
        module_source_hash af28f30e3e9cca24203f70eceb6fc78544dbed11ec8643849c43127b0b197587
        declaration_manifest_hash bdc8d671461b7688cc6f858d6407e0a46cb947c41d276d06448f56e28e638670
        obligation_id    cde9e7cc-69fd-4592-b808-66f8883d0b13

  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

M2.2 SUBSUMES M2.1 (coordinate directions are an orthonormal family) and M2.0 (k = 1).
`#print axioms` on both roots reports exactly [propext, Classical.choice, Quot.sound] —
no sorryAx, no admit, no project axioms.

Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2

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
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
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

/-- **M2.1 — codimension-2 (coordinate-aligned) product anti-concentration.**
Two distinct coordinates of an isotropic Gaussian `N(center, σ²I)` are independent, so the
joint two-slab probability is the *product* of the two M1 marginals: `≤ (2ε/(σ√(2π)))²`.
(Tracked: problem `c548e3fe`, episode `10653478`.) -/
theorem gaussian_two_coord_anticoncentration
    (n : ℕ) (center : EuclideanSpace ℝ (Fin n)) (σ ε : ℝ) (i j : Fin n) (t : Fin n → ℝ)
    (hij : i ≠ j) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        {x | |x i - t i| ≤ ε ∧ |x j - t j| ≤ ε}
      ≤ ENNReal.ofReal ((2 * ε / (σ * Real.sqrt (2 * Real.pi))) ^ 2) := by
  have hS : (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sq_nonneg σ)
  have hb0 : (0 : ℝ) ≤ 2 * ε / (σ * Real.sqrt (2 * Real.pi)) := by
    apply div_nonneg
    · nlinarith [hε]
    · positivity
  have hclm : (fun x : EuclideanSpace ℝ (Fin n) => (x i, x j))
      = ⇑((EuclideanSpace.proj (𝕜 := ℝ) i).prod (EuclideanSpace.proj (𝕜 := ℝ) j)) := by
    funext x; rfl
  have hpair : ProbabilityTheory.HasGaussianLaw
      (fun x : EuclideanSpace ℝ (Fin n) => (x i, x j))
      (ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
    rw [hclm]; exact ⟨ProbabilityTheory.isGaussian_map _⟩
  have hcov : ProbabilityTheory.covariance (fun x => x i) (fun x => x j)
      (ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) = 0 := by
    rw [ProbabilityTheory.covariance_eval_multivariateGaussian hS i j]
    simp [Matrix.smul_apply, Matrix.one_apply_ne hij]
  have hindep : ProbabilityTheory.IndepFun (fun x : EuclideanSpace ℝ (Fin n) => x i) (fun x => x j)
      (ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    hpair.indepFun_of_covariance_eq_zero hcov
  have hset : {x : EuclideanSpace ℝ (Fin n) | |x i - t i| ≤ ε ∧ |x j - t j| ≤ ε}
      = (fun x => x i) ⁻¹' (Set.Icc (t i - ε) (t i + ε))
        ∩ (fun x => x j) ⁻¹' (Set.Icc (t j - ε) (t j + ε)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hbound : ∀ (k : Fin n),
      ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
          ((fun x => x k) ⁻¹' (Set.Icc (t k - ε) (t k + ε)))
        ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
    intro k
    have hmk : Measurable (fun x : EuclideanSpace ℝ (Fin n) => x k) := by fun_prop
    have hmp := ProbabilityTheory.measurePreserving_eval_multivariateGaussian
      (μ := center) (S := σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) (i := k) hS
    rw [← MeasureTheory.Measure.map_apply hmk measurableSet_Icc, hmp.map_eq]
    have hv2 : (((σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) k k).toNNReal : ℝ) = σ ^ 2 := by
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      exact Real.coe_toNNReal _ (sq_nonneg σ)
    exact gaussian_anticoncentration (center k) (t k) ε σ _ hv2 hσ hε
  rw [hset, hindep.measure_inter_preimage_eq_mul _ _ measurableSet_Icc measurableSet_Icc]
  refine le_trans (mul_le_mul' (hbound i) (hbound j)) (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hb0, ← pow_two]

/-- **M2.2 — general (arbitrary-orientation) subspace anti-concentration.**
For `N(center, σ²I)` and ANY orthonormal family `u : Fin k → ℝⁿ` (orthonormal basis of the
orthogonal complement of a codimension-`k` subspace), the projections `⟨u j, ·⟩` are jointly
independent Gaussians, so the joint slab probability is `≤ (2ε/(σ√(2π)))^k`. Since
`{x | ‖P_{Wᗮ} x‖ ≤ ε} ⊆ {x | ∀ j, |⟨u j,x⟩| ≤ ε}`, this is the sharp codimension-`k`
distance-to-subspace bound for an arbitrary subspace. Subsumes M2.1 and M2.0.
(Tracked: problem `4a4d86dd`, episode `ea3c53fe`.) -/
theorem gaussian_subspace_anticoncentration
    (n k : ℕ) (center : EuclideanSpace ℝ (Fin n)) (σ ε : ℝ)
    (u : Fin k → EuclideanSpace ℝ (Fin n)) (t : Fin k → ℝ)
    (hu : Orthonormal ℝ u) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
        {x | ∀ j, |inner ℝ (u j) x - t j| ≤ ε}
      ≤ ENNReal.ofReal ((2 * ε / (σ * Real.sqrt (2 * Real.pi))) ^ k) := by
  set μ := ProbabilityTheory.multivariateGaussian center (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) with hμdef
  have hS : (σ ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sq_nonneg σ)
  have hmem : MeasureTheory.MemLp id 2 μ := ProbabilityTheory.IsGaussian.memLp_two_id
  have hb0 : (0 : ℝ) ≤ 2 * ε / (σ * Real.sqrt (2 * Real.pi)) := by
    apply div_nonneg
    · nlinarith [hε]
    · positivity
  have hclm : (fun x : EuclideanSpace ℝ (Fin n) => (fun j => inner ℝ (u j) x))
      = ⇑(ContinuousLinearMap.pi (fun j => innerSL ℝ (u j))) := by
    funext x; funext j; rfl
  have htuple : ProbabilityTheory.HasGaussianLaw
      (fun x : EuclideanSpace ℝ (Fin n) => (fun j => inner ℝ (u j) x)) μ := by
    rw [hclm]; exact ⟨ProbabilityTheory.isGaussian_map _⟩
  have hcovbil : ∀ a b : EuclideanSpace ℝ (Fin n),
      ProbabilityTheory.covarianceBilin μ a b = σ ^ 2 * inner ℝ a b := by
    intro a b
    rw [ProbabilityTheory.covarianceBilin_multivariateGaussian hS a b,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    have h3 : dotProduct (WithLp.ofLp a) (WithLp.ofLp b) = inner ℝ a b := by
      rw [PiLp.inner_apply]; simp [dotProduct, mul_comm]
    rw [h3]
  have hindep : ProbabilityTheory.iIndepFun
      (fun (j : Fin k) (x : EuclideanSpace ℝ (Fin n)) => inner ℝ (u j) x) μ := by
    refine ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_eq_zero htuple ?_
    intro i j hij
    rw [← ProbabilityTheory.covarianceBilin_apply_eq_cov hmem (u i) (u j), hcovbil (u i) (u j),
      hu.2 hij, mul_zero]
  have hset : {x : EuclideanSpace ℝ (Fin n) | ∀ j, |inner ℝ (u j) x - t j| ≤ ε}
      = ⋂ j ∈ (Finset.univ : Finset (Fin k)),
          (fun x => inner ℝ (u j) x) ⁻¹' (Set.Icc (t j - ε) (t j + ε)) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc, abs_le,
      Finset.mem_univ, true_implies]
    constructor
    · intro h j; exact ⟨by linarith [(h j).1], by linarith [(h j).2]⟩
    · intro h j; exact ⟨by linarith [(h j).1], by linarith [(h j).2]⟩
  have hbound : ∀ (j : Fin k),
      μ ((fun x => inner ℝ (u j) x) ⁻¹' (Set.Icc (t j - ε) (t j + ε)))
        ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
    intro j
    have hmk : Measurable (⇑(innerSL ℝ (u j))) := (innerSL ℝ (u j)).continuous.measurable
    have hpre : (fun x : EuclideanSpace ℝ (Fin n) => inner ℝ (u j) x)
          ⁻¹' (Set.Icc (t j - ε) (t j + ε))
        = (⇑(innerSL ℝ (u j))) ⁻¹' (Set.Icc (t j - ε) (t j + ε)) := by
      rw [coe_innerSL_apply]
    rw [hpre, ← MeasureTheory.Measure.map_apply hmk measurableSet_Icc,
      ProbabilityTheory.IsGaussian.map_eq_gaussianReal (innerSL ℝ (u j))]
    have hvar : ProbabilityTheory.variance (⇑(innerSL ℝ (u j))) μ = σ ^ 2 := by
      rw [coe_innerSL_apply, ← ProbabilityTheory.covarianceBilin_self hmem (u j),
        hcovbil (u j) (u j), real_inner_self_eq_norm_sq, hu.norm_eq_one j, one_pow, mul_one]
    exact gaussian_anticoncentration _ (t j) ε σ _
      (by rw [hvar]; exact Real.coe_toNNReal _ (sq_nonneg σ)) hσ hε
  rw [hset, hindep.measure_inter_preimage_eq_mul Finset.univ (fun i _ => measurableSet_Icc)]
  calc ∏ j ∈ (Finset.univ : Finset (Fin k)),
          μ ((fun x => inner ℝ (u j) x) ⁻¹' (Set.Icc (t j - ε) (t j + ε)))
      ≤ ∏ _j ∈ (Finset.univ : Finset (Fin k)),
          ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) :=
        Finset.prod_le_prod' (fun j _ => hbound j)
    _ = ENNReal.ofReal ((2 * ε / (σ * Real.sqrt (2 * Real.pi))) ^ k) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.ofReal_pow hb0]

end SolveAll011.M2

#print axioms SolveAll011.M2.gaussian_two_coord_anticoncentration
#print axioms SolveAll011.M2.gaussian_subspace_anticoncentration
