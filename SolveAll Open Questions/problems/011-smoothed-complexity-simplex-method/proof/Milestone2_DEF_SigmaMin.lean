/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-DEF (Tier 1, architecture A-COND): smallest-singular-value definition +
Rudelson–Vershynin lower bound, self-contained.

NOT the open conjecture; pure deterministic linear algebra. Defines the smallest singular
value of a column family `a : Fin n → E` as the infimum of the Rayleigh quotient
`‖∑ x_j a_j‖ / ‖x‖` over nonzero coefficient vectors (here the inlined `⨅` over the
nonzero-vector subtype), and proves `σ_min(a) ≥ n^{-1/2} · min_i dist(a_i, span of others)` —
the Rudelson–Vershynin distance-to-span lower bound, feeding the σ_min anti-concentration
program. The `rv` block reproduces the M2-GEOMσ deterministic bound inline.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  M2-DEF  sigmaMin_lower_bound
          problem_version  ecacc32e-d778-4cb3-892d-40bacfa3d10a
          episode          5a5ec38c-7f82-4e55-9d06-026255f3f050
          statement_hash   67cb826cc811c7c18f7bec0d1a9b8d37f8166601b59705689caaf1f60769cc31
          module_source_hash e347531334dc9d80bb40f665ff7a49848e0a74f5f89ecdbf7de88d10385ab5b0
          declaration_manifest_hash e50cb6437ae32d0033f267df254cf2853e566c4b91b78fbf636ad72b69e214fa
          obligation_id    1a8c9fc2-5bb7-40dd-b0a5-f24ec5ee7923
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` = [propext, Classical.choice, Quot.sound]. (One deprecation warning:
`EuclideanSpace.single_apply`; harmless.) Reproduce: `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2DEF

/-- **M2-DEF — smallest-singular-value lower bound (self-contained).**
The infimum of the Rayleigh quotient `‖∑ x_j a_j‖ / ‖x‖` over nonzero coefficient vectors —
i.e. the smallest singular value of the column family `a` — is at least
`n^{-1/2} · min_i dist(a i, span of the other columns)`. This is the Rudelson–Vershynin
distance-to-span lower bound on `σ_min`, with `σ_min` expressed as the inlined `⨅`. -/
theorem sigmaMin_lower_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (hn : 0 < n) (a : Fin n → E) :
    (Finset.univ.inf' (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
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

end SolveAll011.M2DEF

#print axioms SolveAll011.M2DEF.sigmaMin_lower_bound
