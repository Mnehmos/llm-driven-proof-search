/-
Erdős Problem #858 — §5 quantitative Mertens, UPPER bound.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5; the Mertens-type control underlying Lemma 5.2.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 9e56ec0a-f75c-4b3d-a7cf-b165913fb269,
problem_version_id 81a545eb-79d5-4e8a-bfd0-1aa47fa74630.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 0964e4e6…

Result:  ∀ x ≥ 2,  Σ_{p≤x, p prime} 1/p ≤ log 4 · loglog x + (4 − log 4 · loglog 2).

This is the UPPER half of quantitative Mertens for #858 — the companion to the
lower bound Σ_{p≤x} 1/p ≥ log 2 · loglog x − C carried over from Erdős #647.
Together they bracket the prime harmonic sum as Θ(loglog x) with explicit
constants (log 2 ≤ leading constant ≤ log 4 = 2 log 2), which is the qualitative
growth content underneath Lemma 5.2 (Mertens on polynomial intervals). This
refutes the campaign's earlier "analytic wall" assessment of §5: the Chebyshev
route is open.

Proof outline (self-contained; cross-submission lemma referencing is not usable
in this environment, so the shared #647 pieces are inlined):
  1. Abel summation (Mathlib `sum_mul_eq_sub_sub_integral_mul`) gives the exact
     identity   Σ_{p≤x} 1/p = θ(x)/(x log x)
                 + ∫_{(2,x]} (log t+1)/(t² log²t)·θ(t) dt,
     with θ = Chebyshev's first function.  [same identity as the #647 lower-bound
     assembly, hid block]
  2. Pointwise on [2,x], θ(t) ≤ log 4 · t (Mathlib `Chebyshev.theta_le_log4_mul_x`,
     Chebyshev's upper bound) and the weight (log t+1)/(t² log²t) ≥ 0, so the
     integral ≤ log 4 · ∫_2^x (log t+1)/(t log²t) dt.
  3. Main-term antiderivative (#647 hMain block):
     ∫_2^x (log t+1)/(t log²t) dt = (loglog x − 1/log x) − (loglog 2 − 1/log 2).
  4. Boundary term θ(x)/(x log x) ≤ log 4·x/(x log x) = log 4/log x ≤ log 4/log 2 = 2.
  5. Combine, using log 4·(log 2)⁻¹ = 2 and log 4·(log x)⁻¹ ≥ 0, and drop the
     negative −log 4/log x term, to reach the stated constant 4 − log 4·loglog 2.

Unlike the lower bound, no error integrals are needed: θ is bounded above by
log 4·t directly, so the upper direction is strictly simpler than #647's
lower-bound assembly.

Lean notes: `eq1` (the cofactor identity (log 4·t)·w = log 4·v) is closed by
`field_simp` ALONE — a trailing `ring` errors with "No goals to be solved"
(contrast #647's `hval`, whose field_simp leaves a genuine polynomial goal). The
`Nat.floor` bracket subscript is U+208A (₊), not U+2099 (ₙ).
-/
import Mathlib

namespace Erdos858

/-- §5 quantitative Mertens, upper bound: the prime harmonic sum is at most
`log 4 · loglog x + (4 − log 4 · loglog 2)` for every `x ≥ 2`. Companion to the
`log 2 · loglog x − C` lower bound, giving a two-sided `Θ(loglog x)` bracket. -/
theorem erdos858_mertens_upper :
    ∀ x : ℝ, 2 ≤ x →
      (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ)))
        ≤ Real.log 4 * Real.log (Real.log x) + (4 - Real.log 4 * Real.log (Real.log 2)) := by
  intro x hx
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : 0 < x := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsubset2 : Set.Icc (2:ℝ) x ⊆ {t:ℝ | t ≠ 0} := by
    intro t ht
    have h1 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
  have hid : ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ))
      = Chebyshev.theta x / (x * Real.log x)
        + ∫ t in Set.Ioc (2:ℝ) x,
            (Real.log t + 1) / (t^2 * (Real.log t)^2) * Chebyshev.theta t := by
    set f : ℝ → ℝ := fun t => (t * Real.log t)⁻¹ with hf_def
    set g : ℝ → ℝ := fun t => -(Real.log t + 1) / (t^2 * (Real.log t)^2) with hg_def
    set c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0 with hc_def
    have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
    have hderiv : ∀ t ∈ Set.Icc (2:ℝ) x, HasDerivAt f (g t) t := by
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htpos : (0:ℝ) < t := by linarith
      have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
      have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
      have htne : t ≠ 0 := ne_of_gt htpos
      have h1 : HasDerivAt (fun s : ℝ => s * Real.log s) (1 * Real.log t + t * t⁻¹) t :=
        (hasDerivAt_id t).mul (Real.hasDerivAt_log htne)
      have h1' : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
        have heq1 : (1:ℝ) * Real.log t + t * t⁻¹ = Real.log t + 1 := by field_simp
        rwa [heq1] at h1
      have hne : t * Real.log t ≠ 0 := mul_ne_zero htne hlogtne
      have h2 : HasDerivAt (fun s : ℝ => (s * Real.log s)⁻¹) (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := h1'.inv hne
      have heq2 : -(Real.log t + 1) / (t * Real.log t) ^ 2 = g t := by
        rw [hg_def]; ring
      rw [heq2] at h2
      exact h2
    have hf_diff : ∀ t ∈ Set.Icc (2:ℝ) x, DifferentiableAt ℝ f t := fun t ht => (hderiv t ht).differentiableAt
    have hderiv_eq : Set.EqOn g (deriv f) (Set.Icc (2:ℝ) x) := fun t ht => (hderiv t ht).deriv.symm
    have hgcont : ContinuousOn g (Set.Icc (2:ℝ) x) := by
      apply ContinuousOn.div
      · exact ((Real.continuousOn_log.mono hsubset2).add continuousOn_const).neg
      · exact (continuousOn_pow 2).mul ((Real.continuousOn_log.mono hsubset2).pow 2)
      · intro t ht
        have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        have htpos : (0:ℝ) < t := by linarith
        have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
        positivity
    have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (2:ℝ) x) MeasureTheory.volume := by
      apply MeasureTheory.IntegrableOn.congr_fun (f := g)
      · exact hgcont.integrableOn_Icc
      · exact hderiv_eq
      · exact measurableSet_Icc
    have hthetadef : ∀ y : ℝ, Chebyshev.theta y = ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, c k := by
      intro y
      rw [Chebyshev.theta, hc_def, Finset.sum_filter]
      rw [show Finset.Icc 0 ⌊y⌋₊ = insert 0 (Finset.Ioc 0 ⌊y⌋₊) by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega]
      rw [Finset.sum_insert (by simp)]
      simp
    have h2le : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have habel := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0:ℝ) ≤ 2) hx hf_diff hf_int
    have hfloor2 : ⌊(2:ℝ)⌋₊ = 2 := by norm_num
    rw [hfloor2] at habel
    have hset : (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime = insert 2 ((Finset.Ioc 2 ⌊x⌋₊).filter Nat.Prime) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, hkn⟩, hp⟩
        have hk2 : 2 ≤ k := hp.two_le
        rcases eq_or_lt_of_le hk2 with heq | hlt
        · left; exact heq.symm
        · right; exact ⟨⟨hlt, hkn⟩, hp⟩
      · rintro (rfl | ⟨⟨h1, hkn⟩, hp⟩)
        · exact ⟨⟨by norm_num, h2le⟩, Nat.prime_two⟩
        · exact ⟨⟨by omega, hkn⟩, hp⟩
    have hLHS : ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, f (k:ℝ) * c k
        = (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ))) - 1/2 := by
      have hfck : ∀ k ∈ Finset.Ioc 2 ⌊x⌋₊, f (k:ℝ) * c k = (if k.Prime then (1/(k:ℝ)) else 0) := by
        intro k hk
        rw [hf_def, hc_def]
        by_cases hp : k.Prime
        · simp only [hp, if_true]
          have hkpos : (k:ℝ) ≠ 0 := by
            have hh : 2 < k := (Finset.mem_Ioc.mp hk).1
            have : 0 < k := by omega
            positivity
          have h3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
          have hklog : Real.log (k:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
          field_simp
        · simp [hp]
      rw [Finset.sum_congr rfl hfck, ← Finset.sum_filter, hset, Finset.sum_insert (by simp)]
      norm_num
    rw [hLHS] at habel
    have hth2sum : ∑ k ∈ Finset.Icc 0 2, c k = Real.log 2 := by
      simp only [show Finset.Icc 0 2 = {0,1,2} by decide, Finset.sum_insert, Finset.sum_singleton]
      rw [hc_def]; norm_num [Nat.prime_two]
    rw [hth2sum] at habel
    have hf2 : f 2 * Real.log 2 = 1/2 := by
      rw [hf_def]; field_simp
    rw [← hthetadef x] at habel
    have hintsimp : ∫ t in Set.Ioc (2:ℝ) x, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
        = ∫ t in Set.Ioc (2:ℝ) x, -((Real.log t + 1) / (t^2 * (Real.log t)^2) * Chebyshev.theta t) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      have ht' : t ∈ Set.Icc (2:ℝ) x := Set.mem_Icc.mpr ⟨le_of_lt ht.1, ht.2⟩
      rw [← hderiv_eq ht', hg_def, ← hthetadef t]
      ring
    rw [hintsimp] at habel
    rw [MeasureTheory.integral_neg] at habel
    rw [hf2] at habel
    have hfxthm : f x * Chebyshev.theta x = Chebyshev.theta x / (x * Real.log x) := by
      rw [hf_def]; ring
    linarith [habel, hfxthm]
  have hMain : ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2)
      = (Real.log (Real.log x) - (Real.log x)⁻¹) - (Real.log (Real.log 2) - (Real.log 2)⁻¹) := by
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
      · exact (Real.continuousOn_log.mono hsubset2).add continuousOn_const
      · exact continuousOn_id.mul ((Real.continuousOn_log.mono hsubset2).pow 2)
      · intro t ht
        have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        have htne : t ≠ 0 := ne_of_gt (by linarith)
        have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
        exact mul_ne_zero htne (pow_ne_zero 2 hlogtne)
    have hint : IntervalIntegrable (fun t => (Real.log t + 1) / (t * (Real.log t)^2)) MeasureTheory.volume 2 x :=
      hcont.intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]
  have hthetamono : Monotone Chebyshev.theta := Chebyshev.theta_mono
  have hthetaIntv : IntervalIntegrable Chebyshev.theta MeasureTheory.volume 2 x := hthetamono.intervalIntegrable
  have hwcont : ContinuousOn (fun t => (Real.log t + 1) / (t^2 * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · exact (Real.continuousOn_log.mono hsubset2).add continuousOn_const
    · exact (continuousOn_pow 2).mul ((Real.continuousOn_log.mono hsubset2).pow 2)
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htpos : (0:ℝ) < t := by linarith
      have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
      positivity
  have hthetawInt : IntervalIntegrable (fun t => Chebyshev.theta t * ((Real.log t + 1) / (t^2 * (Real.log t)^2))) MeasureTheory.volume 2 x := hthetaIntv.mul_continuousOn hwcont
  have hIocEq : (∫ t in Set.Ioc (2:ℝ) x, (Real.log t + 1) / (t^2 * (Real.log t)^2) * Chebyshev.theta t)
      = ∫ t in (2:ℝ)..x, Chebyshev.theta t * ((Real.log t + 1) / (t^2 * (Real.log t)^2)) := by
    rw [intervalIntegral.integral_of_le hx]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t _
    ring
  rw [hIocEq] at hid
  have hv_cont : ContinuousOn (fun t => (Real.log t + 1) / (t * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · exact (Real.continuousOn_log.mono hsubset2).add continuousOn_const
    · exact continuousOn_id.mul ((Real.continuousOn_log.mono hsubset2).pow 2)
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htne : t ≠ 0 := ne_of_gt (by linarith)
      have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact mul_ne_zero htne (pow_ne_zero 2 hlogtne)
  have hv_int : IntervalIntegrable (fun t => (Real.log t + 1) / (t * (Real.log t)^2)) MeasureTheory.volume 2 x := hv_cont.intervalIntegrable
  have hL4v_int : IntervalIntegrable (fun t => Real.log 4 * ((Real.log t + 1) / (t * (Real.log t)^2))) MeasureTheory.volume 2 x := hv_int.const_mul (Real.log 4)
  have hmono : (∫ t in (2:ℝ)..x, Chebyshev.theta t * ((Real.log t + 1) / (t^2 * (Real.log t)^2)))
      ≤ ∫ t in (2:ℝ)..x, Real.log 4 * ((Real.log t + 1) / (t * (Real.log t)^2)) := by
    apply intervalIntegral.integral_mono_on hx hthetawInt hL4v_int
    intro t ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    have hwnn : 0 ≤ (Real.log t + 1) / (t^2 * (Real.log t)^2) := by positivity
    have hθle : Chebyshev.theta t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x (le_of_lt htpos)
    have step1 : Chebyshev.theta t * ((Real.log t + 1) / (t^2 * (Real.log t)^2))
        ≤ (Real.log 4 * t) * ((Real.log t + 1) / (t^2 * (Real.log t)^2)) :=
      mul_le_mul_of_nonneg_right hθle hwnn
    have eq1 : (Real.log 4 * t) * ((Real.log t + 1) / (t^2 * (Real.log t)^2))
        = Real.log 4 * ((Real.log t + 1) / (t * (Real.log t)^2)) := by
      field_simp
    rw [eq1] at step1
    exact step1
  have hL4v_eq : (∫ t in (2:ℝ)..x, Real.log 4 * ((Real.log t + 1) / (t * (Real.log t)^2)))
      = Real.log 4 * Real.log (Real.log x) - Real.log 4 * (Real.log x)⁻¹
        - Real.log 4 * Real.log (Real.log 2) + Real.log 4 * (Real.log 2)⁻¹ := by
    rw [intervalIntegral.integral_const_mul, hMain]; ring
  rw [hL4v_eq] at hmono
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogxge : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hA : Chebyshev.theta x / (x * Real.log x) ≤ 2 := by
    have hθx : Chebyshev.theta x ≤ Real.log 4 * x := Chebyshev.theta_le_log4_mul_x (le_of_lt hxpos)
    rw [div_le_iff₀ (mul_pos hxpos hlogxpos)]
    calc Chebyshev.theta x ≤ Real.log 4 * x := hθx
      _ = 2 * Real.log 2 * x := by rw [hlog4]
      _ ≤ 2 * Real.log x * x := by nlinarith [mul_nonneg (le_of_lt hxpos) (sub_nonneg.mpr hlogxge)]
      _ = 2 * (x * Real.log x) := by ring
  have heqlog4log2 : Real.log 4 * (Real.log 2)⁻¹ = 2 := by
    rw [hlog4, mul_assoc, mul_inv_cancel₀ (ne_of_gt hlog2pos), mul_one]
  have hlog4logx_nn : 0 ≤ Real.log 4 * (Real.log x)⁻¹ :=
    mul_nonneg (le_of_lt hlog4pos) (le_of_lt (inv_pos.mpr hlogxpos))
  rw [hid]
  linarith [hA, hmono, heqlog4log2, hlog4logx_nn]

end Erdos858
