import Mathlib

/-!
# Erdős #647 — Layer A part 2a: main-term antiderivative for quantitative Mertens

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-13.

  problem_version_id  781d4876-55c9-4c3c-9420-602b508771be
  episode_id          36f8eaa9-7116-44a3-b633-f8f1a03210f4
  root_statement_hash 513062caa29c528d7f2df3f6e92de50073c08703b87b05fe15abc49064431b65
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: the exact closed form of the integral carrying the double-log
Mertens growth. Since `F(t) = log(log t) - 1/log t` has derivative
`(log t + 1)/(t · log²t)`, the fundamental theorem of calculus gives,
for `x ≥ 2`,

  ∫_2^x (log t + 1)/(t · log²t) dt
    = (log log x - 1/log x) - (log log 2 - 1/log 2).

Role in the density-bound program: this is the `θ(t) = t` idealization
of the Mertens integral in the kernel-verified identity (problem
`d584666d`)

  ∑_{p≤x} 1/p = θ(x)/(x·log x) + ∫_{(2,x]} (log t+1)/(t²·log²t)·θ(t) dt.

Substituting Mathlib's effective bound `θ(t) ≈ t` turns the double-log
main term of quantitative Mertens into exactly this antiderivative. The
next milestone bounds the true integral below via `Chebyshev.theta_ge`.
-/

theorem erdos647_mertens_mainterm :
    ∀ x : ℝ, 2 ≤ x →
      ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2)
        = (Real.log (Real.log x) - (Real.log x)⁻¹)
          - (Real.log (Real.log 2) - (Real.log 2)⁻¹) := by
  intro x hx
  have hsubset : Set.Icc (2:ℝ) x ⊆ {t : ℝ | t ≠ 0} := by
    intro t ht
    have h1 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  have hmain : ∀ t ∈ Set.uIcc (2:ℝ) x,
      HasDerivAt (fun s => Real.log (Real.log s) - (Real.log s)⁻¹)
        ((Real.log t + 1) / (t * (Real.log t)^2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log htne
    have hloglog : HasDerivAt (fun s => Real.log (Real.log s)) ((Real.log t)⁻¹ * t⁻¹) t :=
      (Real.hasDerivAt_log hlogtne).comp t hlog
    have hinv : HasDerivAt (fun s => (Real.log s)⁻¹) (-t⁻¹ / Real.log t ^ 2) t :=
      hlog.inv hlogtne
    have hsub := hloglog.sub hinv
    have hval : (Real.log t)⁻¹ * t⁻¹ - -t⁻¹ / Real.log t ^ 2 = (Real.log t + 1) / (t * (Real.log t)^2) := by
      field_simp
      ring
    rw [hval] at hsub
    exact hsub
  have hcont : ContinuousOn (fun t => (Real.log t + 1) / (t * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · exact (Real.continuousOn_log.mono hsubset).add continuousOn_const
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono hsubset).pow 2)
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htne : t ≠ 0 := ne_of_gt (by linarith)
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact mul_ne_zero htne (pow_ne_zero 2 hlogtne)
  have hint : IntervalIntegrable (fun t => (Real.log t + 1) / (t * (Real.log t)^2)) MeasureTheory.volume 2 x :=
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]
