import Mathlib

/-!
# Erdős #858 — Mertens-2 error/weight integral (K-term of the Abel reduction #54)

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  paper ref           Erdős #858 (Chojecki 2026), Mertens second theorem;
                      weight integral of the Abel-summation reduction (§ Mertens-2)
  problem_version_id  0113e4df-32ac-4c2a-a58f-9928f05ea213
  episode_id          e8e25055-e977-456f-a972-6025705ed7f0
  root_statement_hash 509ebfe4281026c30c35638fee0194c069a0e3940274cfd3df4b787391a3c78c
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
                      mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the closed form of the weight/error integral appearing in the
Mertens second theorem (`∑_{p≤x} 1/p = log log x + M + o(1)`) after Abel
summation. The antiderivative of `1/(t·log²t)` is `−1/log t = −(log t)⁻¹`,
since

  d/dt [−(log t)⁻¹] = (log t)⁻² · (1/t) = 1/(t·log²t).

The fundamental theorem of calculus therefore gives, for `x ≥ 2`,

  ∫_2^x 1/(t·log²t) dt = (log 2)⁻¹ − (log x)⁻¹ ≤ (log 2)⁻¹,

the upper bound following from `(log x)⁻¹ > 0` for `x ≥ 2`.

Role in the density-bound program: this is the `K`-term ingredient consumed
by the Mertens-2 Abel reduction (campaign step #54). Technique mirrors the
kernel-verified erdos-647 pieces `Erdos647_MertensWeightIntegral` and
`Erdos647_MertensMainTerm`: `intervalIntegral.integral_eq_sub_of_hasDerivAt`
with a hand-built antiderivative (`HasDerivAt` via
`((Real.hasDerivAt_log _).inv _).neg`) and `ContinuousOn.intervalIntegrable`.
-/

theorem erdos858_mertens2_error_integral :
    ∀ x : ℝ, 2 ≤ x →
      (∫ t in (2:ℝ)..x, 1 / (t * (Real.log t) ^ 2)) = (Real.log 2)⁻¹ - (Real.log x)⁻¹ ∧
      (∫ t in (2:ℝ)..x, 1 / (t * (Real.log t) ^ 2)) ≤ (Real.log 2)⁻¹ := by
  intro x hx
  have hsubset : Set.Icc (2:ℝ) x ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    have h1 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  have hmain : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun s => -(Real.log s)⁻¹) (1 / (t * (Real.log t) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have hbase : HasDerivAt (fun s => -(Real.log s)⁻¹) (-(-t⁻¹ / Real.log t ^ 2)) t :=
      ((Real.hasDerivAt_log htne).inv hlogtne).neg
    have hval : -(-t⁻¹ / Real.log t ^ 2) = 1 / (t * (Real.log t) ^ 2) := by
      first
      | (field_simp; ring)
      | field_simp
    rw [hval] at hbase
    exact hbase
  have hcont : ContinuousOn (fun t => 1 / (t * (Real.log t) ^ 2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono hsubset).pow 2)
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htne : t ≠ 0 := ne_of_gt (by linarith)
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact mul_ne_zero htne (pow_ne_zero 2 hlogtne)
  have hint : IntervalIntegrable (fun t => 1 / (t * (Real.log t) ^ 2)) MeasureTheory.volume 2 x :=
    hcont.intervalIntegrable
  have hval_eq : (∫ t in (2:ℝ)..x, 1 / (t * (Real.log t) ^ 2)) = (Real.log 2)⁻¹ - (Real.log x)⁻¹ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]
    ring
  refine ⟨hval_eq, ?_⟩
  rw [hval_eq]
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hinvpos : 0 ≤ (Real.log x)⁻¹ := le_of_lt (inv_pos.mpr hlogx)
  linarith
