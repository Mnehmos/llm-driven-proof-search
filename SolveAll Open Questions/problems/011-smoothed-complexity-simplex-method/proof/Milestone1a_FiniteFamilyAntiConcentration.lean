/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 1a (Tier 1): finite-family Gaussian anti-concentration (union bound),
its homogeneous k-coefficient corollary, and the LP perturbation-model bridge.

NOT the open conjecture. This lifts the M1 scalar small-ball bound to a finite
family of Gaussian-perturbed coefficients via a union bound (countable
subadditivity — NO independence assumption). It bounds "some individual
perturbed coefficient is ε-close to a degeneracy threshold"; it does NOT bound
"a basis is near-singular" (a joint/determinant statement — the M2 target).

Tracked, kernel-verified results (fidelity `attested`, dev-mode; caps at
kernel_verified, never certified):
  M1a.1  gaussian_anticoncentration_union
         problem_version d2... -> 46bd7c1a-45ae-4b00-a839-48797a740c6b
         episode         e4c031ff-c334-49b5-8e2b-0c2ec5102c3f
         statement_hash  cd45ebe4f8ada258bbdf14bc6d845f4314aee77eec1cb2ce7c2004117df8d07b
         module_source_hash c1ac7485dd051dcf97f3fc53405cb3e90cdfa4d04b06d5deef35a7a0f9b04a79
  M1a.2  gaussian_anticoncentration_union_homogeneous
         problem_version c1e88e47-4e7e-4a13-805c-137578751afc
         episode         e04f96ea-0d23-42ca-9349-65db3e91d339
         statement_hash  d3f497b58d0a79fe46bcf66f6a6bc7716726a78eec54083fa904e9a0605027aa
         module_source_hash be142854cf8723614c066439f4b5a9e62efc75f0a3b930bb6bd9f41136935ebf
  M1a.3  perturbed_coeff_some_near_threshold  (lean_checked bridge wrapper; a
         definitional rename of M1a.2 — no new mathematics, so not separately
         tracked as an MCP root)
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` on all three roots reports exactly
[propext, Classical.choice, Quot.sound] — the standard Mathlib axioms, with no
`sorryAx`, no `admit`, and no project-defined axioms.

NOTE on generality: the tracked statements fix the index type `ι : Type` and
sample space `Ω : Type` at universe 0 (monomorphic), to keep the registered
statement hash simple. The mathematics is universe-polymorphic; a `Type*`
version compiles identically (see the campaign's dev notes). Universe 0 covers
every intended application (finite index types, standard probability spaces).

Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M1a

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

/-- **M1a.1 — Finite-family Gaussian anti-concentration (union bound).**
For a finite index type `ι` and random variables `X i` on a common space `Ω`,
each with Gaussian law `N(m i, σ i ²)`, the probability that *some* `X i` lands
within `ε i` of its threshold `t i` is bounded by the sum of the individual
small-ball bounds. No independence assumption — countable subadditivity of the
measure suffices. (Tracked: problem `46bd7c1a`, episode `e4c031ff`.) -/
theorem gaussian_anticoncentration_union
    {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ι → Ω → ℝ) (m t ε σ : ι → ℝ) (v : ι → NNReal)
    (hmeas : ∀ i, Measurable (X i))
    (hv2 : ∀ i, (v i : ℝ) = (σ i) ^ 2)
    (hσ : ∀ i, 0 < σ i)
    (hε : ∀ i, 0 ≤ ε i)
    (hlaw : ∀ i, P.map (X i) = ProbabilityTheory.gaussianReal (m i) (v i)) :
    P {ω | ∃ i, |X i ω - t i| ≤ ε i}
      ≤ ∑ i, ENNReal.ofReal (2 * ε i / (σ i * Real.sqrt (2 * Real.pi))) := by
  have hset : {ω | ∃ i, |X i ω - t i| ≤ ε i}
      = ⋃ i, (X i) ⁻¹' (Set.Icc (t i - ε i) (t i + ε i)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨i, h1, h2⟩; exact ⟨i, by linarith, by linarith⟩
    · rintro ⟨i, h1, h2⟩; exact ⟨i, by linarith, by linarith⟩
  rw [hset]
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hmap : P ((X i) ⁻¹' (Set.Icc (t i - ε i) (t i + ε i)))
      = ProbabilityTheory.gaussianReal (m i) (v i) (Set.Icc (t i - ε i) (t i + ε i)) := by
    rw [← MeasureTheory.Measure.map_apply (hmeas i) measurableSet_Icc, hlaw i]
  rw [hmap]
  exact gaussian_anticoncentration (m i) (t i) (ε i) (σ i) (v i) (hv2 i) (hσ i) (hε i)

/-- **M1a.2 — Homogeneous corollary.** When all `k = |ι|` coefficients share the
same `σ` and `ε`, the union bound collapses to the clean `k · 2ε/(σ√(2π))`.
(Tracked: problem `c1e88e47`, episode `e04f96ea`.) -/
theorem gaussian_anticoncentration_union_homogeneous
    {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : ι → Ω → ℝ) (m t : ι → ℝ) (ε σ : ℝ) (v : ι → NNReal)
    (hmeas : ∀ i, Measurable (X i))
    (hv2 : ∀ i, (v i : ℝ) = σ ^ 2)
    (hσ : 0 < σ)
    (hε : 0 ≤ ε)
    (hlaw : ∀ i, P.map (X i) = ProbabilityTheory.gaussianReal (m i) (v i)) :
    P {ω | ∃ i, |X i ω - t i| ≤ ε}
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * ε / (σ * Real.sqrt (2 * Real.pi)))) := by
  have hset : {ω | ∃ i, |X i ω - t i| ≤ ε}
      = ⋃ i, (X i) ⁻¹' (Set.Icc (t i - ε) (t i + ε)) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨i, h1, h2⟩; exact ⟨i, by linarith, by linarith⟩
    · rintro ⟨i, h1, h2⟩; exact ⟨i, by linarith, by linarith⟩
  rw [hset]
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  have hterm : ∀ i : ι, P ((X i) ⁻¹' (Set.Icc (t i - ε) (t i + ε)))
      ≤ ENNReal.ofReal (2 * ε / (σ * Real.sqrt (2 * Real.pi))) := by
    intro i
    have hmap : P ((X i) ⁻¹' (Set.Icc (t i - ε) (t i + ε)))
        = ProbabilityTheory.gaussianReal (m i) (v i) (Set.Icc (t i - ε) (t i + ε)) := by
      rw [← MeasureTheory.Measure.map_apply (hmeas i) measurableSet_Icc, hlaw i]
    rw [hmap]
    exact gaussian_anticoncentration (m i) (t i) ε σ (v i) (hv2 i) hσ hε
  refine le_trans (Finset.sum_le_sum (fun i _ => hterm i)) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card ι)), ENNReal.ofReal_natCast]

/-- **M1a.3 — LP perturbation-model bridge** (lean_checked; a definitional
rename of M1a.2). If `k` scalar coefficients are each perturbed to a Gaussian
`N(mean i, σ²)` — matching `A = Ā + G` with `G` entrywise `N(0,σ²)` — the
probability that *any one* lands within `ε` of a fixed threshold `threshold i`
is at most `k · 2ε/(σ√(2π))`.

What it says: "some individual perturbed coefficient is ε-close to a threshold."
What it does NOT say: anything about a *basis* being near-singular, which is a
joint statement about a determinant / smallest singular value of a perturbed
submatrix (the M2 target). The gap from here to the LP pivot-count analysis is
exactly that joint estimate plus the shadow-vertex geometry. -/
theorem perturbed_coeff_some_near_threshold
    {ι : Type} [Fintype ι] {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (coeff : ι → Ω → ℝ) (mean threshold : ι → ℝ) (ε σ : ℝ) (v : ι → NNReal)
    (hmeas : ∀ i, Measurable (coeff i))
    (hv2 : ∀ i, (v i : ℝ) = σ ^ 2)
    (hσ : 0 < σ)
    (hε : 0 ≤ ε)
    (hlaw : ∀ i, P.map (coeff i) = ProbabilityTheory.gaussianReal (mean i) (v i)) :
    P {ω | ∃ i, |coeff i ω - threshold i| ≤ ε}
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * ε / (σ * Real.sqrt (2 * Real.pi)))) :=
  gaussian_anticoncentration_union_homogeneous P coeff mean threshold ε σ v hmeas hv2 hσ hε hlaw

end SolveAll011.M1a

#print axioms SolveAll011.M1a.gaussian_anticoncentration_union
#print axioms SolveAll011.M1a.gaussian_anticoncentration_union_homogeneous
#print axioms SolveAll011.M1a.perturbed_coeff_some_near_threshold
