/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-DEF (Tier 1, architecture A-COND): the smallest-singular-value lower bound in
Rudelson–Vershynin form, with `σ_min` DEFINED as a unit-sphere infimum.

NOT the open conjecture, and NOT probability — the deterministic capstone of the σ_min
ladder. `sigmaMinCols a := ⨅_{‖x‖=1} ‖∑ j, x_j • a_j‖` (for `E = ℝⁿ` and `a j` the columns
of a matrix `A`, this is exactly `σ_min(A) = min_{‖x‖=1} ‖A x‖`). The main theorem is the
Rudelson–Vershynin lower bound `σ_min(cols) ≥ n^{-1/2} · min_i dist(a i, span of others)`.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified). The
tracked statement inlines the `⨅` directly (so no `def` needs marshalling through the module
API) and inlines the deterministic RV chain; this snapshot presents the equivalent, cleaner
`def`-based API form.
  M2-DEF  sigmaMin_cols_ge   (tracked root uses the inlined-⨅ statement)
          problem_version  73ac63c1-97df-4a2f-83f9-25b52cf49ef6
          episode          9bdee270-3333-4e6f-995d-9489ff936ce8
          statement_hash   f3cb5ad111fcc7696095b2115a017e7d33c58816d00359d9ee8e2044c9462c27
          module_source_hash 0e684f2c57b6e24a513a39133a8a85900fb464b2a4732869aa6305e0d087e46d
          declaration_manifest_hash 35c70e3a07353010b40e87841fabb0846bba0092456c05fb5428256ae08ee2fc
          obligation_id    0e22db28-f3c5-4198-85a7-099f0761f7f4
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms sigmaMinCols_ge` = [propext, Classical.choice, Quot.sound].
Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2DEF

/-- (M2-GEOM helper) atomic projection inequality. -/
theorem abs_smul_infDist_le_norm_smul_add_mem
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) (a : E) (c : ℝ) (w : E) (hw : w ∈ W) :
    |c| * Metric.infDist a (↑W : Set E) ≤ ‖c • a + w‖ := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp only [abs_zero, zero_mul, zero_smul, zero_add]; exact norm_nonneg w
  · have hwc : (c⁻¹ • w) ∈ W := W.smul_mem _ hw
    have hz : c • a + w = c • (a - (-(c⁻¹ • w))) := by
      rw [sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hz, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left (Metric.infDist_le_dist_of_mem (W.neg_mem hwc)) (abs_nonneg c)

/-- (M2-GEOM) per-vector RV projection bound. -/
theorem abs_coord_mul_infDist_span_le_norm_sum
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (a : Fin n → E) (x : Fin n → ℝ) (i : Fin n) :
    |x i| * Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E)
      ≤ ‖∑ j, x j • a j‖ := by
  set W := Submodule.span ℝ (a '' {j | j ≠ i}) with hW
  have hmem : (∑ j ∈ Finset.univ.erase i, x j • a j) ∈ W := by
    refine Submodule.sum_mem _ (fun j hj => ?_)
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact W.smul_mem _ (Submodule.subset_span (Set.mem_image_of_mem a hji))
  have hsplit : (∑ j, x j • a j) = x i • a i + ∑ j ∈ Finset.univ.erase i, x j • a j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [hsplit]
  exact abs_smul_infDist_le_norm_smul_add_mem W (a i) (x i) _ hmem

/-- (M2-GEOM) coordinate lemma: `∃ i, ‖x‖ ≤ √n · |x i|`. -/
theorem exists_coord_ge (n : ℕ) (hn : 0 < n) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ i, ‖x‖ ≤ Real.sqrt n * |x i| := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i => |x i|)
  refine ⟨i0, ?_⟩
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ (n : ℝ) * |x i0| ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2
        = ∑ _i : Fin n, |x i0| ^ 2 - ∑ i : Fin n, (|x i0| ^ 2 - ‖x i‖ ^ 2) := by
          rw [Finset.sum_sub_distrib]; ring
      _ ≤ ∑ _i : Fin n, |x i0| ^ 2 := by
          have : 0 ≤ ∑ i : Fin n, (|x i0| ^ 2 - ‖x i‖ ^ 2) :=
            Finset.sum_nonneg (fun i _ => by
              rw [Real.norm_eq_abs]; nlinarith [abs_nonneg (x i), abs_nonneg (x i0), hi0 i])
          linarith
      _ = (n : ℝ) * |x i0| ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2)
      ≤ Real.sqrt ((n : ℝ) * |x i0| ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * |x i0| := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (abs_nonneg _)]

/-- (M2-GEOMσ) the deterministic RV lower bound `(min_i dist)·‖x‖ ≤ √n·‖∑ x_j a_j‖`. -/
theorem rv_min_dist_bound
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (hn : 0 < n)
    (a : Fin n → E) (x : EuclideanSpace ℝ (Fin n)) :
    (Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
        (fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E)))
        * ‖x‖
      ≤ Real.sqrt n * ‖∑ j, x j • a j‖ := by
  set hne := Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  set d := fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E) with hd
  have hd_nonneg : (0 : ℝ) ≤ Finset.univ.inf' hne d :=
    Finset.le_inf' _ _ (fun i _ => Metric.infDist_nonneg)
  obtain ⟨i0, hi0⟩ := exists_coord_ge n hn x
  calc Finset.univ.inf' hne d * ‖x‖
      ≤ Finset.univ.inf' hne d * (Real.sqrt n * |x i0|) :=
        mul_le_mul_of_nonneg_left hi0 hd_nonneg
    _ = Real.sqrt n * (Finset.univ.inf' hne d * |x i0|) := by ring
    _ ≤ Real.sqrt n * (|x i0| * d i0) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ i0)) (abs_nonneg _)
    _ ≤ Real.sqrt n * ‖∑ j, x j • a j‖ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact abs_coord_mul_infDist_span_le_norm_sum a (fun j => x j) i0

/-- **M2-DEF — smallest singular value of a column family** as the infimum of `‖∑ x_j a_j‖`
over unit coefficient vectors. For `E = ℝⁿ` and `a j` the columns of a matrix `A`, this is
`σ_min(A) = min_{‖x‖=1} ‖A x‖`. -/
noncomputable def sigmaMinCols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (a : Fin n → E) : ℝ :=
  ⨅ x : {v : EuclideanSpace ℝ (Fin n) // ‖v‖ = 1}, ‖∑ j, (x : EuclideanSpace ℝ (Fin n)) j • a j‖

/-- **σ_min anti-concentration lower bound (Rudelson–Vershynin).**
`σ_min(cols) ≥ n^{-1/2} · min_i dist(a i, span of the other columns)`. -/
theorem sigmaMinCols_ge {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (hn : 0 < n)
    (a : Fin n → E) :
    Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
        (fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E))
      / Real.sqrt n ≤ sigmaMinCols a := by
  haveI : Nonempty {v : EuclideanSpace ℝ (Fin n) // ‖v‖ = 1} :=
    ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, by rw [PiLp.norm_single]; norm_num⟩⟩
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  unfold sigmaMinCols
  apply le_ciInf
  intro x
  rw [div_le_iff₀ hsqrt_pos]
  have hx := rv_min_dist_bound n hn a (x : EuclideanSpace ℝ (Fin n))
  rw [x.2, mul_one] at hx
  rw [mul_comm]
  exact hx

end SolveAll011.M2DEF

#print axioms SolveAll011.M2DEF.sigmaMinCols_ge
