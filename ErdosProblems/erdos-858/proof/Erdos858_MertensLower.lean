/-
Erdős Problem #858 — §5 quantitative Mertens, LOWER bound.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5; the Mertens-type control underlying Lemma 5.2.)

Ported from the kernel-verified Erdős #647 Layer-A assembly
(`erdos647_mertens_assembly`) — a byte-faithful re-verification under a new #858
problem registration, through the tracked proofsearch MCP pipeline on 2026-07-14.

  problem_version_id  5a5ccddf-bd27-4440-ad42-fdcd0f54000e
  episode_id          a748163c-5644-41f3-8612-c0fcebc300a3
  root_statement_hash 2470d4498d67527b14af26b8f3e21b68924d7f4751f105c6895623d310d207d1
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
  mathlib             360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Result:  ∀ x ≥ 2,
  log 2 · loglog x − (1/2 + log 2 · loglog 2 + (1 + 1/log 2)·(1 + 2√2))
    ≤ Σ_{p≤x, p prime} 1/p.

This is the LOWER half of quantitative Mertens for #858 — the companion to the
upper bound Σ_{p≤x} 1/p ≤ log 4 · loglog x + C (Erdos858_MertensUpper.lean).
Together they bracket the prime harmonic sum as Θ(loglog x).

Proof outline (self-contained; cross-submission lemma referencing is not usable in
this environment, so the six shared #647 pieces are inlined):
  1. Abel summation (Mathlib `sum_mul_eq_sub_sub_integral_mul`) gives the exact
     identity  Σ_{p≤x} 1/p = θ(x)/(x log x) + ∫_{(2,x]} (log t+1)/(t² log²t)·θ(t) dt
     (hid block), with θ = Chebyshev's first function.
  2. Main-term antiderivative (hMain): ∫_2^x (log t+1)/(t log²t) dt
       = (loglog x − 1/log x) − (loglog 2 − 1/log 2).
  3. Weight integral (hWeight): ∫_2^x (log t+1)/(t² log²t) dt = 1/(2 log 2) − 1/(x log x).
  4. Log error integral (hE2): ∫_2^x (log t+1)·log(t+2)/(t² log²t) dt ≤ 1 + 1/log 2.
  5. √t error integral (hE3): ∫_2^x (log t+1)·2√t·log t/(t² log²t) dt ≤ 2√2·(1 + 1/log 2).
  6. Real-valued θ bridge (hLge), driven by `Chebyshev.theta_ge`:
       ∀ t ≥ 2, (t−1)log 2 − log(t+2) − 2√t·log t ≤ θ(t).
  Substituting (6) pointwise into the weighted θ-integral of (1) and splitting by
  linearity into (2)–(5) yields the explicit unconditional lower bound.

Provenance note: this port is otherwise byte-identical to the #647 snapshot
(Erdos647_MertensAssembly.lean). The sole deviation is a one-character correction
of a latent, non-compiling parenthesis typo in that snapshot's `hABCD`
have-statement ('(((Real.log 2' → '((Real.log 2', restoring paren balance). The
correction is semantics-preserving (an extra outer paren is defeq); the corrected
form is exactly what kernel-verified here.
-/

import Mathlib

namespace Erdos858

theorem erdos858_mertens_lower :
    ∀ x : ℝ, 2 ≤ x → Real.log 2 * Real.log (Real.log x) -
      (1/2 + Real.log 2 * Real.log (Real.log 2) + (1 + (Real.log 2)⁻¹) * (1 + 2*Real.sqrt 2))
      ≤ ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ)) := by
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
  have hWeight : ∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2)
      = (2 * Real.log 2)⁻¹ - (x * Real.log x)⁻¹ := by
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
      · exact (Real.continuousOn_log.mono hsubset2).add continuousOn_const
      · exact ((continuousOn_id.pow 2)).mul ((Real.continuousOn_log.mono hsubset2).pow 2)
      · intro t ht
        have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        have htne : t ≠ 0 := ne_of_gt (by linarith)
        have hlogtne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
        exact mul_ne_zero (pow_ne_zero 2 htne) (pow_ne_zero 2 hlogtne)
    have hint : IntervalIntegrable (fun t => (Real.log t + 1) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x :=
      hcont.intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]
    ring
  have hE2 : (∫ t in (2:ℝ)..x, (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2))
      ≤ 1 + (Real.log 2)⁻¹ := by
    clear hid hMain hWeight
    set C2 : ℝ := 2 * (1 + (Real.log 2)⁻¹) with hC2
    have hCpos : 0 ≤ C2 := by rw [hC2]; positivity
    have hptwise : ∀ t ∈ Set.Icc (2:ℝ) x,
        (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2) ≤ C2 * (t^2)⁻¹ := by
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htpos : (0:ℝ) < t := by linarith
      have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
      have hlog2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have htsq : t + 2 ≤ t^2 := by nlinarith
      have hlogadd : Real.log (t + 2) ≤ Real.log (t^2) := Real.log_le_log (by linarith) htsq
      have hlogsq : Real.log (t^2) = 2 * Real.log t := by rw [Real.log_pow]; push_cast; ring
      have hAle : Real.log (t + 2) ≤ 2 * Real.log t := by rw [hlogsq] at hlogadd; exact hlogadd
      have hLinv : 1 ≤ (Real.log 2)⁻¹ * Real.log t := by
        have h := mul_le_mul_of_nonneg_left hlog2t (le_of_lt (inv_pos.mpr hlog2pos))
        rwa [inv_mul_cancel₀ (ne_of_gt hlog2pos)] at h
      rw [div_le_iff₀ (by positivity)]
      have hsimp : C2 * (t^2)⁻¹ * (t^2 * (Real.log t)^2) = C2 * (Real.log t)^2 := by
        field_simp
      rw [hsimp, hC2]
      have h3a : Real.log t ≤ (Real.log 2)⁻¹ * (Real.log t)^2 := by
        have h := mul_le_mul_of_nonneg_right hLinv (le_of_lt hlogtpos)
        rw [one_mul] at h
        nlinarith [h]
      have h1 : (Real.log t + 1) * Real.log (t + 2) ≤ (Real.log t + 1) * (2 * Real.log t) :=
        mul_le_mul_of_nonneg_left hAle (by positivity)
      nlinarith [h1, h3a]
    have hcontlogt : ContinuousOn (fun t => Real.log t) (Set.uIcc (2:ℝ) x) := by
      rw [Set.uIcc_of_le hx]
      exact Real.continuousOn_log.mono hsubset2
    have hcontlogt2 : ContinuousOn (fun t => Real.log (t + 2)) (Set.uIcc (2:ℝ) x) := by
      rw [Set.uIcc_of_le hx]
      exact Real.continuousOn_log.comp ((continuous_add_right 2).continuousOn)
        (fun t ht => ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
    have hdenne : ∀ t ∈ Set.uIcc (2:ℝ) x, t^2 * (Real.log t)^2 ≠ 0 := by
      rw [Set.uIcc_of_le hx]
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith))) (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith))))
    have hcontLHS : ContinuousOn (fun t => (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) :=
      ((hcontlogt.add continuousOn_const).mul hcontlogt2).div (((continuous_pow 2).continuousOn).mul (hcontlogt.pow 2)) hdenne
    have hcontRHS : ContinuousOn (fun t => C2 * (t^2)⁻¹) (Set.uIcc (2:ℝ) x) := by
      apply continuousOn_const.mul
      apply ContinuousOn.inv₀ ((continuous_pow 2).continuousOn)
      rw [Set.uIcc_of_le hx]
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
    have hintLHS : IntervalIntegrable (fun t => (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x := hcontLHS.intervalIntegrable
    have hintRHS : IntervalIntegrable (fun t => C2 * (t^2)⁻¹) MeasureTheory.volume 2 x := hcontRHS.intervalIntegrable
    have hmonoE2 := intervalIntegral.integral_mono_on hx hintLHS hintRHS hptwise
    have hpow : ∫ t in (2:ℝ)..x, (t^2)⁻¹ = (2:ℝ)⁻¹ - x⁻¹ := by
      have hmain2 : ∀ t ∈ Set.uIcc (2:ℝ) x, HasDerivAt (fun s => -s⁻¹) ((t^2)⁻¹) t := by
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        have htne : t ≠ 0 := ne_of_gt (by linarith)
        have hi : HasDerivAt (fun s : ℝ => s⁻¹) (-(t^2)⁻¹) t := hasDerivAt_inv htne
        have hneg := hi.neg
        have hval : - -(t^2)⁻¹ = (t^2)⁻¹ := by ring
        rw [hval] at hneg
        exact hneg
      have hcpow : ContinuousOn (fun t => (t^2)⁻¹) (Set.uIcc (2:ℝ) x) := by
        apply ContinuousOn.inv₀ ((continuous_pow 2).continuousOn)
        rw [Set.uIcc_of_le hx]
        intro t ht
        exact pow_ne_zero 2 (ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain2 (hcpow.intervalIntegrable)]
      ring
    rw [intervalIntegral.integral_const_mul, hpow] at hmonoE2
    have hfinal : C2 * ((2:ℝ)⁻¹ - x⁻¹) ≤ 1 + (Real.log 2)⁻¹ := by
      have hprod : 0 ≤ C2 * x⁻¹ := mul_nonneg hCpos (by positivity)
      have hChalf : C2 * (2:ℝ)⁻¹ = 1 + (Real.log 2)⁻¹ := by rw [hC2]; ring
      nlinarith [hprod, hChalf]
    linarith [hmonoE2, hfinal]
  have hE3 : (∫ t in (2:ℝ)..x, (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2))
      ≤ 2 * Real.sqrt 2 * (1 + (Real.log 2)⁻¹) := by
    clear hid hMain hWeight hE2
    set C3 : ℝ := 2 * (1 + (Real.log 2)⁻¹) with hC3
    have hCpos : 0 ≤ C3 := by rw [hC3]; positivity
    have hptwise : ∀ t ∈ Set.Icc (2:ℝ) x,
        (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2) ≤ C3 * (Real.sqrt t / t^2) := by
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htpos : (0:ℝ) < t := by linarith
      have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
      have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
      have hlog2t : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
      have hLinv : 1 ≤ (Real.log 2)⁻¹ * Real.log t := by
        have h := mul_le_mul_of_nonneg_left hlog2t (le_of_lt (inv_pos.mpr hlog2pos))
        rwa [inv_mul_cancel₀ (ne_of_gt hlog2pos)] at h
      have hkey : 2 * (Real.log t + 1) ≤ C3 * Real.log t := by rw [hC3]; nlinarith [hLinv]
      rw [div_le_iff₀ (by positivity)]
      have hsimp : C3 * (Real.sqrt t / t^2) * (t^2 * (Real.log t)^2) = C3 * Real.sqrt t * (Real.log t)^2 := by
        field_simp
      rw [hsimp]
      have hstep : (2 * (Real.log t + 1)) * (Real.sqrt t * Real.log t) ≤ (C3 * Real.log t) * (Real.sqrt t * Real.log t) :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt (mul_pos hsqrtpos hlogtpos))
      nlinarith [hstep]
    have hcontlogt : ContinuousOn (fun t => Real.log t) (Set.uIcc (2:ℝ) x) := by
      rw [Set.uIcc_of_le hx]
      exact Real.continuousOn_log.mono hsubset2
    have hcontsqrt : ContinuousOn (fun t => Real.sqrt t) (Set.uIcc (2:ℝ) x) := Real.continuous_sqrt.continuousOn
    have hdenne : ∀ t ∈ Set.uIcc (2:ℝ) x, t^2 * (Real.log t)^2 ≠ 0 := by
      rw [Set.uIcc_of_le hx]
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith))) (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith))))
    have hdenne2 : ∀ t ∈ Set.uIcc (2:ℝ) x, t^2 ≠ 0 := by
      rw [Set.uIcc_of_le hx]
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact pow_ne_zero 2 (ne_of_gt (by linarith))
    have hcontLHS : ContinuousOn (fun t => (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) :=
      (((hcontlogt.add continuousOn_const).mul ((continuousOn_const.mul hcontsqrt).mul hcontlogt))).div (((continuous_pow 2).continuousOn).mul (hcontlogt.pow 2)) hdenne
    have hcontRHS : ContinuousOn (fun t => C3 * (Real.sqrt t / t^2)) (Set.uIcc (2:ℝ) x) :=
      continuousOn_const.mul (hcontsqrt.div ((continuous_pow 2).continuousOn) hdenne2)
    have hintLHS : IntervalIntegrable (fun t => (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x := hcontLHS.intervalIntegrable
    have hintRHS : IntervalIntegrable (fun t => C3 * (Real.sqrt t / t^2)) MeasureTheory.volume 2 x := hcontRHS.intervalIntegrable
    have hmonoE3 := intervalIntegral.integral_mono_on hx hintLHS hintRHS hptwise
    have hpow : ∫ t in (2:ℝ)..x, (Real.sqrt t / t^2) = 2/Real.sqrt 2 - 2/Real.sqrt x := by
      clear hCpos hptwise hcontLHS hcontRHS hintLHS hintRHS hmonoE3
      have hmain2 : ∀ t ∈ Set.uIcc (2:ℝ) x, HasDerivAt (fun s => -2 * (Real.sqrt s)⁻¹) (Real.sqrt t / t^2) t := by
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
        have htpos : (0:ℝ) < t := by linarith
        have htne : t ≠ 0 := ne_of_gt htpos
        have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
        have hsqrtne : Real.sqrt t ≠ 0 := ne_of_gt hsqrtpos
        have hs := Real.hasDerivAt_sqrt htne
        have hinv := hs.inv hsqrtne
        have hscaled := hinv.const_mul (-2 : ℝ)
        have hsq : (Real.sqrt t)^2 = t := Real.sq_sqrt (le_of_lt htpos)
        have hnum : ∀ s : ℝ, 0 < s → -2 * (-(1/(2*s))/s^2) = s / (s^2)^2 := by
          intro s hs2
          have hsne : s ≠ 0 := ne_of_gt hs2
          field_simp <;> ring
        have hval := hnum (Real.sqrt t) hsqrtpos
        conv_rhs at hval => rw [hsq]
        convert hscaled using 1 <;> first | rfl | (funext s; rfl) | exact hval.symm
      have hcpow : ContinuousOn (fun t => Real.sqrt t / t^2) (Set.uIcc (2:ℝ) x) :=
        hcontsqrt.div ((continuous_pow 2).continuousOn) hdenne2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain2 hcpow.intervalIntegrable]
      ring
    rw [intervalIntegral.integral_const_mul, hpow] at hmonoE3
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hxsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have h2sqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfinal : C3 * (2 / Real.sqrt 2 - 2 / Real.sqrt x) ≤ 2 * Real.sqrt 2 * (1 + (Real.log 2)⁻¹) := by
      have hterm : 2 / Real.sqrt 2 = Real.sqrt 2 := by
        rw [eq_comm, eq_div_iff (ne_of_gt h2sqrtpos)]; nlinarith [hsq2]
      have hnn : 0 ≤ C3 * (2 / Real.sqrt x) := by positivity
      rw [hC3] at hCpos ⊢
      nlinarith [hterm, hnn]
    linarith [hmonoE3, hfinal]
  have hLge : ∀ t : ℝ, 2 ≤ t → (t - 1) * Real.log 2 - Real.log (t + 2) - 2 * Real.sqrt t * Real.log t ≤ Chebyshev.theta t := by
    clear hid hMain hWeight hE2 hE3
    intro t ht
    set n := ⌊t⌋₊ with hn_def
    have ht0 : (0:ℝ) ≤ t := by linarith
    have hn2 : 2 ≤ n := by
      have h2n : ((2:ℕ):ℝ) ≤ t := by exact_mod_cast ht
      exact_mod_cast Nat.le_floor h2n
    have hnt : (n:ℝ) ≤ t := Nat.floor_le ht0
    have htn1 : t < (n:ℝ) + 1 := Nat.lt_floor_add_one t
    have hthle : Chebyshev.theta (n:ℝ) ≤ Chebyshev.theta t := Chebyshev.theta_mono hnt
    have hnge := Chebyshev.theta_ge n
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hterm1 : (t-1)*Real.log 2 ≤ (n:ℝ)*Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hlog2pos)
      linarith [htn1]
    have hterm2 : -Real.log (t+2) ≤ -Real.log ((n:ℝ)+1) := by
      have hle : Real.log ((n:ℝ)+1) ≤ Real.log (t+2) := Real.log_le_log (by linarith) (by linarith)
      linarith
    have hterm3 : -2*Real.sqrt t*Real.log t ≤ -2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by
      have hsqrt_mono : Real.sqrt (n:ℝ) ≤ Real.sqrt t := Real.sqrt_le_sqrt hnt
      have hlog_mono : Real.log (n:ℝ) ≤ Real.log t := Real.log_le_log hnpos hnt
      have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by linarith [hn2, hnpos])
      have hsqt : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
      have hmul : Real.sqrt (n:ℝ) * Real.log (n:ℝ) ≤ Real.sqrt t * Real.log t := mul_le_mul hsqrt_mono hlog_mono hln hsqt
      nlinarith [hmul]
    calc (t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t
        ≤ (n:ℝ)*Real.log 2 - Real.log ((n:ℝ)+1) - 2*Real.sqrt (n:ℝ)*Real.log (n:ℝ) := by linarith [hterm1, hterm2, hterm3]
      _ ≤ Chebyshev.theta (n:ℝ) := hnge
      _ ≤ Chebyshev.theta t := hthle
  have hthetaxnn : 0 ≤ Chebyshev.theta x := Chebyshev.theta_nonneg x
  have hbd0 : 0 ≤ Chebyshev.theta x / (x * Real.log x) := div_nonneg hthetaxnn (le_of_lt (mul_pos hxpos hlogxpos))
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
  have hLcont : ContinuousOn (fun t : ℝ => (t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.sub
    apply ContinuousOn.sub
    · exact (continuousOn_id.sub continuousOn_const).mul continuousOn_const
    · exact Real.continuousOn_log.comp (continuousOn_id.add continuousOn_const) (fun t ht => ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
    · exact (continuousOn_const.mul (Real.continuous_sqrt.continuousOn)).mul (Real.continuousOn_log.mono hsubset2)
  have hwL_int : IntervalIntegrable (fun t => ((t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t) * ((Real.log t + 1) / (t^2 * (Real.log t)^2))) MeasureTheory.volume 2 x :=
    hLcont.intervalIntegrable.mul_continuousOn hwcont
  have hptwise_theta_ge_L : ∀ t ∈ Set.Icc (2:ℝ) x, ((t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t) * ((Real.log t + 1) / (t^2 * (Real.log t)^2)) ≤ Chebyshev.theta t * ((Real.log t + 1) / (t^2 * (Real.log t)^2)) := by
    intro t ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have hwnn : 0 ≤ (Real.log t + 1) / (t^2 * (Real.log t)^2) := by
      have htpos : (0:ℝ) < t := by linarith
      have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
      positivity
    exact mul_le_mul_of_nonneg_right (hLge t ht2) hwnn
  have hmono2 := intervalIntegral.integral_mono_on hx hwL_int hthetawInt hptwise_theta_ge_L
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
  have hw_int : IntervalIntegrable (fun t => (Real.log t + 1) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x := hwcont.intervalIntegrable
  have he2_cont : ContinuousOn (fun t => (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    have hcontlogt : ContinuousOn (fun t => Real.log t) (Set.Icc (2:ℝ) x) := Real.continuousOn_log.mono hsubset2
    have hcontlogt2 : ContinuousOn (fun t => Real.log (t + 2)) (Set.Icc (2:ℝ) x) :=
      Real.continuousOn_log.comp ((continuous_add_right 2).continuousOn) (fun t ht => ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
    have hdenne : ∀ t ∈ Set.Icc (2:ℝ) x, t^2 * (Real.log t)^2 ≠ 0 := by
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith))) (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith))))
    exact ((hcontlogt.add continuousOn_const).mul hcontlogt2).div (((continuous_pow 2).continuousOn).mul (hcontlogt.pow 2)) hdenne
  have he2_int : IntervalIntegrable (fun t => (Real.log t + 1) * Real.log (t + 2) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x := he2_cont.intervalIntegrable
  have he3_cont : ContinuousOn (fun t => (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2)) (Set.uIcc (2:ℝ) x) := by
    rw [Set.uIcc_of_le hx]
    have hcontlogt : ContinuousOn (fun t => Real.log t) (Set.Icc (2:ℝ) x) := Real.continuousOn_log.mono hsubset2
    have hcontsqrt : ContinuousOn (fun t => Real.sqrt t) (Set.Icc (2:ℝ) x) := Real.continuous_sqrt.continuousOn
    have hdenne : ∀ t ∈ Set.Icc (2:ℝ) x, t^2 * (Real.log t)^2 ≠ 0 := by
      intro t ht
      have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith))) (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith))))
    exact (((hcontlogt.add continuousOn_const).mul ((continuousOn_const.mul hcontsqrt).mul hcontlogt))).div (((continuous_pow 2).continuousOn).mul (hcontlogt.pow 2)) hdenne
  have he3_int : IntervalIntegrable (fun t => (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2)) MeasureTheory.volume 2 x := he3_cont.intervalIntegrable
  have hcongr : (∫ t in (2:ℝ)..x, ((t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t) * ((Real.log t + 1) / (t^2 * (Real.log t)^2)))
      = ∫ t in (2:ℝ)..x, (Real.log 2 * ((Real.log t + 1) / (t * (Real.log t)^2)) - Real.log 2 * ((Real.log t + 1) / (t^2 * (Real.log t)^2)) - (Real.log t + 1) * Real.log (t+2) / (t^2 * (Real.log t)^2) - (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2)) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht2 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    have htpos : (0:ℝ) < t := by linarith
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
    have htne : t ≠ 0 := ne_of_gt htpos
    have hlogtne : Real.log t ≠ 0 := ne_of_gt hlogtpos
    field_simp <;> ring
  have hAB : ∫ t in (2:ℝ)..x, (Real.log 2 * ((Real.log t + 1) / (t * (Real.log t)^2)) - Real.log 2 * ((Real.log t + 1) / (t^2 * (Real.log t)^2)))
      = Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2)) - Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2)) := by
    rw [intervalIntegral.integral_sub (hv_int.const_mul _) (hw_int.const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hABC : ∫ t in (2:ℝ)..x, (Real.log 2 * ((Real.log t + 1) / (t * (Real.log t)^2)) - Real.log 2 * ((Real.log t + 1) / (t^2 * (Real.log t)^2)) - (Real.log t + 1) * Real.log (t+2) / (t^2 * (Real.log t)^2))
      = (Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2)) - Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2))) - (∫ t in (2:ℝ)..x, (Real.log t + 1) * Real.log (t+2) / (t^2 * (Real.log t)^2)) := by
    rw [intervalIntegral.integral_sub ((hv_int.const_mul _).sub (hw_int.const_mul _)) he2_int, hAB]
  have hABCD : ∫ t in (2:ℝ)..x, (Real.log 2 * ((Real.log t + 1) / (t * (Real.log t)^2)) - Real.log 2 * ((Real.log t + 1) / (t^2 * (Real.log t)^2)) - (Real.log t + 1) * Real.log (t+2) / (t^2 * (Real.log t)^2) - (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2))
      = ((Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2)) - Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2))) - (∫ t in (2:ℝ)..x, (Real.log t + 1) * Real.log (t+2) / (t^2 * (Real.log t)^2))) - (∫ t in (2:ℝ)..x, (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2)) := by
    rw [intervalIntegral.integral_sub (((hv_int.const_mul _).sub (hw_int.const_mul _)).sub he2_int) he3_int, hABC]
  have hsplit_eq : (∫ t in (2:ℝ)..x, ((t-1)*Real.log 2 - Real.log (t+2) - 2*Real.sqrt t*Real.log t) * ((Real.log t + 1) / (t^2 * (Real.log t)^2)))
      = Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t * (Real.log t)^2))
        - Real.log 2 * (∫ t in (2:ℝ)..x, (Real.log t + 1) / (t^2 * (Real.log t)^2))
        - (∫ t in (2:ℝ)..x, (Real.log t + 1) * Real.log (t+2) / (t^2 * (Real.log t)^2))
        - (∫ t in (2:ℝ)..x, (Real.log t + 1) * (2 * Real.sqrt t * Real.log t) / (t^2 * (Real.log t)^2)) := by
    rw [hcongr, hABCD]
  rw [hMain, hWeight] at hsplit_eq
  rw [hsplit_eq] at hmono2
  have hlogxineq : Real.log 2 / Real.log x ≤ 1 := by
    rw [div_le_one hlogxpos]
    exact Real.log_le_log (by norm_num) hx
  have hxlogxnn : 0 ≤ Real.log 2 / (x * Real.log x) := by positivity
  have heq1 : Real.log 2 * (2 * Real.log 2)⁻¹ = 1/2 := by field_simp <;> ring
  have heq2 : Real.log 2 * (Real.log x)⁻¹ = Real.log 2 / Real.log x := by ring
  have heq3 : Real.log 2 * (x * Real.log x)⁻¹ = Real.log 2 / (x * Real.log x) := by ring
  have heq4 : Real.log 2 * (Real.log 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hlog2pos)
  linarith [hid, hbd0, hmono2, hE2, hE3, hlogxineq, hxlogxnn, heq1, heq2, heq3, heq4]

end Erdos858
