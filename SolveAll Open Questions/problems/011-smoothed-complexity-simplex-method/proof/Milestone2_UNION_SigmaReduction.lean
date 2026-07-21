/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone M2-UNION-geom (Tier 1, A-COND): the deterministic σ_min → column-distance reduction —
the geometric assembly glue for the σ_min anti-concentration union bound.

NOT the open conjecture; pure deterministic linear algebra + order theory, self-contained on the
campaign's verified Rudelson–Vershynin lower bound. For columns `a : Fin n → E` (`n ≥ 1`) with
smallest singular value `σ_min(a) := ⨅_{x≠0} ‖∑ x_j a_j‖/‖x‖`, if `σ_min(a) ≤ ε` then SOME column
is within `√n · ε` of the span of the other columns:
`∃ i, dist(a_i, span{a_j : j≠i}) ≤ √n · ε`.

Proof: `sigmaMin_lower_bound` (inlined) gives `(min_i dist_i)/√n ≤ σ_min(a) ≤ ε`, so
`min_i dist_i ≤ √n·ε`; the finite minimum is achieved (`Finset.exists_mem_eq_inf'`), giving a
column `i` with `dist_i = min_i dist_i ≤ √n·ε`.

Role: the deterministic half of the union-bound step of the σ_min anti-concentration lower-tail.
Composed with a probabilistic union bound over columns it yields
`P(σ_min(A) ≤ ε) ≤ P(∃ i, dist(A_i, span others) ≤ ε√n) ≤ Σ_i P(dist(A_i, span others) ≤ ε√n)`,
each term bounded by the campaign's fixed-subspace anti-concentration (M2.0/M2.2) applied under
conditioning (a perturbed column `c+σG` is a.c. and misses the fixed span of the others a.s.,
`scaled_gaussian_subspace_measure_zero`), giving the Sankar–Spielman–Teng `n·2ε√n/(σ√(2π))` bound.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  sigmaMin_le_imp_exists_col_dist_le
    problem_version  6abbb760-ecd9-43da-a7b6-6933524aa9c9
    episode          0236838c-bd2f-4836-a2fc-296659aef898
    statement_hash   1c31ea7336d91bb508538d8ae0b6e482333a7527925418f42c6db5676cb3425a
    module_source_hash 7c5c19d1c91f2aa48f734947abc40ebc41b3f532a822d3d4b009015047ec19bc
    declaration_manifest_hash a1822eef11ca90750db2e0e1934eb0ca1655fba1d2a89ac2f0a83344dd908a01
    obligation_id    01c7e27b-49e3-448d-a69b-a1fc015dd2bd
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` = [propext, Classical.choice, Quot.sound]. Reproduce: `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2UNION

/-- **Deterministic σ_min → column-distance reduction.** If `σ_min(a) ≤ ε` then some column is
within `√n · ε` of the span of the other columns. -/
theorem sigmaMin_le_imp_exists_col_dist_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (a : Fin n → E) (ε : ℝ)
    (hσ : (⨅ x : {v : EuclideanSpace ℝ (Fin n) // v ≠ 0}, ‖∑ j, x.1 j • a j‖ / ‖x.1‖) ≤ ε) :
    ∃ i, Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E)
      ≤ Real.sqrt n * ε := by
  have slb : (Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
        (fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E)))
        / Real.sqrt n
      ≤ ⨅ x : {v : EuclideanSpace ℝ (Fin n) // v ≠ 0}, ‖∑ j, x.1 j • a j‖ / ‖x.1‖ := by
    have rv : ∀ (x : EuclideanSpace ℝ (Fin n)),
        (Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
            (fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E)))
            * ‖x‖
          ≤ Real.sqrt n * ‖∑ j, x j • a j‖ := by
      intro x
      have atom : ∀ (W : Submodule ℝ E) (b : E) (c : ℝ) (w : E), w ∈ W →
          |c| * Metric.infDist b (↑W : Set E) ≤ ‖c • b + w‖ := by
        intro W b c w hw
        rcases eq_or_ne c 0 with hc | hc
        · subst hc; simp only [abs_zero, zero_mul, zero_smul, zero_add]; exact norm_nonneg w
        · have hwc : (c⁻¹ • w) ∈ W := W.smul_mem _ hw
          have hz : c • b + w = c • (b - (-(c⁻¹ • w))) := by
            rw [sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hc, one_smul]
          rw [hz, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_left
            (Metric.infDist_le_dist_of_mem (W.neg_mem hwc)) (abs_nonneg c)
      have pervec : ∀ i : Fin n, |x i| *
          Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E)
            ≤ ‖∑ j, x j • a j‖ := by
        intro i
        have hmem : (∑ j ∈ Finset.univ.erase i, x j • a j)
            ∈ Submodule.span ℝ (a '' {j | j ≠ i}) := by
          refine Submodule.sum_mem _ (fun j hj => ?_)
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          exact (Submodule.span ℝ (a '' {j | j ≠ i})).smul_mem _
            (Submodule.subset_span (Set.mem_image_of_mem a hji))
        have hsplit : (∑ j, x j • a j) = x i • a i + ∑ j ∈ Finset.univ.erase i, x j • a j :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
        rw [hsplit]
        exact atom (Submodule.span ℝ (a '' {j | j ≠ i})) (a i) (x i) _ hmem
      have coord : ∃ i, ‖x‖ ≤ Real.sqrt n * |x i| := by
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
      set hne := Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
      set d := fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E) with hd
      have hd_nonneg : (0 : ℝ) ≤ Finset.univ.inf' hne d :=
        Finset.le_inf' _ _ (fun i _ => Metric.infDist_nonneg)
      obtain ⟨i0, hi0⟩ := coord
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
            exact pervec i0
    haveI : Nonempty {v : EuclideanSpace ℝ (Fin n) // v ≠ 0} := by
      refine ⟨⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ), ?_⟩⟩
      intro h
      have hcoord : (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) ⟨0, hn⟩ = 0 := by
        rw [h]; rfl
      rw [EuclideanSpace.single_apply] at hcoord
      simp at hcoord
    apply le_ciInf
    intro x
    have hxpos : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    rw [div_le_iff₀ hsqrt, div_mul_eq_mul_div, le_div_iff₀ hxpos]
    exact (rv x.1).trans_eq (mul_comm _ _)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have h1 := slb.trans hσ
  have h2 : (Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
        (fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E)))
      ≤ Real.sqrt n * ε := by
    rw [div_le_iff₀ hsqrt, mul_comm] at h1
    exact h1
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
    (fun i => Metric.infDist (a i) (↑(Submodule.span ℝ (a '' {j | j ≠ i})) : Set E))
  exact ⟨i, hi ▸ h2⟩

end SolveAll011.M2UNION

#print axioms SolveAll011.M2UNION.sigmaMin_le_imp_exists_col_dist_le
