/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Milestone 2-COND (step 3b core) (Tier 1, architecture A-COND): the adjugate row is a normal to
the other columns — the generalized cross-product normal for general `n`.

NOT the open conjecture. Mathlib packages `crossProduct` only for `Fin 3`; this supplies the
general-`n` measurable normal the σ_min conditioning step (M2-COND step 3b) needs. For an `n×n`
real matrix `A`, the `i`-th row of `adjugate A` is orthogonal (dot product 0) to every column
`j ≠ i` of `A`. The adjugate row is a polynomial (cofactor) function of the entries — hence
continuous and MEASURABLE — so, placing the "other columns" as columns `j ≠ i`, it is a
measurable normal of their span. Proof: read off `adjugate A * A = det A • 1` at entry `(i,j)`.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  M2-COND-3b-core  adjugate_row_dotProduct_col_eq_zero
                   problem_version  4f595606-3260-4b07-b870-a0d71716ddfc
                   episode          6216166d-5194-4278-95a5-cfdc41c13d46
                   statement_hash   bfd1a6427e74c0b07afe722b83fe50b8c6f770e63a7101f0c0e7e09101512b9b
                   module_source_hash 05d092a0e3867c3b90d59fe7aec7cc80238a0a39a2d1f162c8087193a21bc51d
                   declaration_manifest_hash e712b020ec7a9a51437984e3480cb38e4fb557940a19643e16620c8a0924e73f
                   obligation_id    1edf9680-ca39-49b0-ba55-020b181eb091
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` = [propext, Classical.choice, Quot.sound].
Reproduce: copy into lean-checker and `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.M2CONDadj

/-- **M2-COND step 3b core — the adjugate row is a normal to the other columns.** For an `n×n`
real matrix `A`, the `i`-th row of `adjugate A` is orthogonal to every column `j ≠ i`:
`∑ k, adjugate A i k * A k j = 0`. Read off `adjugate A * A = det A • 1` at `(i,j)`.
The adjugate row is polynomial in the entries, hence measurable — the generalized
cross-product normal for general `n` (Mathlib's `crossProduct` covers only `Fin 3`). -/
theorem adjugate_row_dotProduct_col_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    (∑ k, Matrix.adjugate A i k * A k j) = 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul A) i) j
  rw [Matrix.mul_apply] at h
  rw [h, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]

/-- **M2-COND step 3b measurability** — the adjugate-row normal map is continuous (hence
measurable once the matrix space carries the Gaussian's Borel σ-algebra). Together with the
orthogonality above, the `i`-th adjugate row is a MEASURABLE normal of the span of the other
columns. (Tracked: problem `beafa0cb`, episode `1aa443a1`, statement_hash `37cde840…`.) -/
theorem continuous_adjugate_row (n : ℕ) (i : Fin n) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => Matrix.adjugate A i) := by
  fun_prop

/-- **M2-COND step 3b (nonzero normal)** — when `A` is nonsingular, the `i`-th adjugate row is
nonzero, so the normal is genuine (not the zero vector) wherever `det A ≠ 0` — which holds a.s.
under the Gaussian matrix measure. (Tracked: problem `8624ced9`, episode `4af0617a`,
statement_hash `969a5b76…`.) -/
theorem adjugate_row_ne_zero_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (hdet : A.det ≠ 0) : Matrix.adjugate A i ≠ 0 := by
  intro hzero
  have h := congrFun (congrFun (Matrix.adjugate_mul A) i) i
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  have hsum : (∑ k, Matrix.adjugate A i k * A k i) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    have hk : Matrix.adjugate A i k = 0 := by
      have := congrFun hzero k; simpa using this
    rw [hk, zero_mul]
  rw [hsum] at h
  exact hdet h.symm

end SolveAll011.M2CONDadj

#print axioms SolveAll011.M2CONDadj.adjugate_row_dotProduct_col_eq_zero
#print axioms SolveAll011.M2CONDadj.continuous_adjugate_row
#print axioms SolveAll011.M2CONDadj.adjugate_row_ne_zero_of_det_ne_zero
