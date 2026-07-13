import Mathlib

/-!
# Erdős #647 — Layer A part 2b (piece): integral of the Mertens weight

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-13.

  problem_version_id  1fc1ab2d-de49-4660-8d7c-8aefeb853a73
  episode_id          700f297f-d8bc-448f-b118-2921e1b98491
  root_statement_hash a9a3ca286fad52e416ba8ee74768a661e33d22b0528d82f9022c4f636b7795df
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the closed form of the integral of the Mertens *weight*
`w(t) = (log t + 1)/(t²·log²t)` itself. Since `F₂(t) = -1/(t·log t)`
has derivative `w(t)`, the FTC gives, for `x ≥ 2`,

  ∫_2^x (log t + 1)/(t²·log²t) dt = 1/(2·log 2) - 1/(x·log x).

Bounded above by `1/(2·log 2)` and increasing to it. This is one exact
piece of the rigorous `θ(t) ≥ (t−1)log 2 − …` substitution bound: in
`log 2 · [∫ w(t)·t − ∫ w(t)]`, the `∫ w(t)·t` term is the part-2a
antiderivative (`Erdos647_MertensMainTerm`) and this lemma is the
`∫ w(t)` term. Together they assemble the double-log main term of the
quantitative Mertens lower bound.
-/

theorem erdos647_mertens_weight_integral :
    ∀ x : ℝ, 2 ≤ x →
      ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2)
        = (2 * Real.log 2)⁻¹ - (x * Real.log x)⁻¹ := by
  intro x hx
  have hsubset : Set.Icc (2:ℝ) x ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    have h1 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  have hmain : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun s => -(s * Real.log s)⁻¹)
        ((Real.log t + 1) / (t^2 * (Real.log t)^2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have htl : HasDerivAt (fun s => s * Real.log s) (Real.log t + 1) t := by
      have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (1 * Real.log t + t * t⁻¹) t :=
        (hasDerivAt_id t).mul (Real.hasDerivAt_log htne)
      have heq : (1:ℝ) * Real.log t + t * t⁻¹ = Real.log t + 1 := by field_simp
      rwa [heq] at h1
    have htlne : t * Real.log t ≠ 0 := mul_ne_zero htne hlogtne
    have hinv : HasDerivAt (fun s => (s * Real.log s)⁻¹) (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := htl.inv htlne
    have hneg := hinv.neg
    have hval : -(-(Real.log t + 1) / (t * Real.log t) ^ 2) = (Real.log t + 1) / (t^2 * (Real.log t)^2) := by
      field_simp
    rw [hval] at hneg
    exact hneg
  have hcont : ContinuousOn (fun t => (Real.log t + 1) / (t^2 * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · exact (Real.continuousOn_log.mono hsubset).add continuousOn_const
    · exact ((continuousOn_id.pow 2)).mul ((Real.continuousOn_log.mono hsubset).pow 2)
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htne : t ≠ 0 := ne_of_gt (by linarith)
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact mul_ne_zero (pow_ne_zero 2 htne) (pow_ne_zero 2 hlogtne)
  have hint : IntervalIntegrable (fun t => (Real.log t + 1) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]
  ring
