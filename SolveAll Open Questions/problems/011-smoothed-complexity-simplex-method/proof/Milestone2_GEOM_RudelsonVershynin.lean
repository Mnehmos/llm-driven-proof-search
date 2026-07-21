/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-GEOM (Tier 1, architecture A-COND): the DETERMINISTIC geometric core of the
Rudelson–Vershynin smallest-singular-value reduction.

NOT the open conjecture, and NOT probability — pure linear algebra in a real normed space.
This is the step that converts `σ_min(A) = min_{‖x‖=1} ‖A x‖` into a lower bound by
column-to-span distances: for columns `a_j` and coefficients `x_j`,
`|x i| · dist(a_i, span{a_j : j≠i}) ≤ ‖∑_j x_j a_j‖`. Combined with the coordinate bound
`∃ i, |x_i| ≥ ‖x‖/√n`, this yields `σ_min(A) ≥ n^{-1/2} · min_i dist(A_i, span of others)`.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  M2-GEOM  abs_coord_mul_infDist_span_le_norm_sum
           problem_version  8d13dff9-8bb3-49a3-a712-1357ef33e609
           episode          d99aa6a8-a43f-4cdc-ab37-a3f6a9e2edbb
           statement_hash   8588c87e9472e58b75a9b627108a430e3c3d130aeda402feef294eee6df1d73c
           module_source_hash efc9983b9d7d35fcb705f6cd227be42d904743c3a633397d6c9cfb090edb96ff
           declaration_manifest_hash 0f8355f247822668f865521bdd2434c5956a7ba4d6eed72ea57aeba0ebb0f409
           obligation_id    3034f98b-3396-4d09-99c3-8f7b7e1ce9dc
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

Repair record: submission 1 kernel_fail — the helper's `rcases` case split used `·`
bullets, which do not survive `flat_tactic_sequence` helper transport; resubmitted with a
bullet-free sequential chain. `#print axioms` on both = [propext, Classical.choice, Quot.sound].

Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2GEOM

/-- **Atomic projection inequality.** In any real normed space, for a submodule `W`, a vector
`a`, a scalar `c`, and any `w ∈ W`: `|c| · dist(a, W) ≤ ‖c • a + w‖`. Because
`c • a + w = c • (a − (−c⁻¹ w))` with `−c⁻¹ w ∈ W`, so `‖c•a+w‖ = |c|·‖a − (−c⁻¹w)‖ ≥
|c|·dist(a,W)`. (For `c = 0` both sides collapse to `0 ≤ ‖w‖`.) -/
theorem abs_smul_infDist_le_norm_smul_add_mem
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) (a : E) (c : ℝ) (w : E) (hw : w ∈ W) :
    |c| * Metric.infDist a (↑W : Set E) ≤ ‖c • a + w‖ := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    simp only [abs_zero, zero_mul, zero_smul, zero_add]
    exact norm_nonneg w
  · have hwc : (c⁻¹ • w) ∈ W := W.smul_mem _ hw
    have hz : c • a + w = c • (a - (-(c⁻¹ • w))) := by
      rw [sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hz, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
    exact mul_le_mul_of_nonneg_left
      (Metric.infDist_le_dist_of_mem (W.neg_mem hwc)) (abs_nonneg c)

/-- **Per-vector Rudelson–Vershynin bound (M2-GEOM).** For a finite family `a : Fin n → E`
of vectors (the "columns") and coefficients `x : Fin n → ℝ`, at every index `i`:
`|x i| · dist(a i, span{a j : j ≠ i}) ≤ ‖∑ j, x j • a j‖`. The linear combination splits as
`x i • a i + (element of the span of the other columns)`, so the atomic inequality applies.
This is the geometric heart that lower-bounds `σ_min` by column-to-span distances. -/
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

/-- **Coordinate lemma.** Every vector `x` in `ℝⁿ` has a coordinate with `|x i| ≥ ‖x‖/√n`,
i.e. `‖x‖ ≤ √n · |x i|` (because `‖x‖² = ∑ x_j² ≤ n · max_j x_j²`). -/
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

/-- **M2-GEOM σ_min form — the full deterministic Rudelson–Vershynin lower bound.**
For columns `a : Fin n → E` (`n ≥ 1`) and any coefficient vector `x ∈ ℝⁿ`:
`(min_i dist(a i, span{a j:j≠i})) · ‖x‖ ≤ √n · ‖∑ j, x j • a j‖`. Dividing by `‖x‖` over
unit `x` gives `σ_min(A) ≥ n^{-1/2} · min_i dist(A_i, span of the other columns)` — the
Rudelson–Vershynin distance-to-span lower bound on the smallest singular value. (Tracked:
problem `ca8e0109`, episode `56a975eb`, statement_hash `aeb92904…`; the tracked root uses an
equivalent fully-inlined proof.) -/
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

end SolveAll011.M2GEOM

#print axioms SolveAll011.M2GEOM.abs_smul_infDist_le_norm_smul_add_mem
#print axioms SolveAll011.M2GEOM.abs_coord_mul_infDist_span_le_norm_sum
#print axioms SolveAll011.M2GEOM.exists_coord_ge
#print axioms SolveAll011.M2GEOM.rv_min_dist_bound
