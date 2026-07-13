import Mathlib

/-!
# Erdős #647 — Layer A: exact Mertens-style identity for ∑ 1/p via Chebyshev θ

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-13.

  problem_version_id  d584666d-e50d-488d-b459-5d1265a3aadd
  episode_id          7a7e8098-a5bf-4dd9-97df-145e34ee914b
  root_statement_hash 9802976a83cd2b4a604d3a77e6f1c4cf2800c41b9ec7797550df9f1fa28a7c98
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for all real `x ≥ 2`,

  ∑_{p ≤ x, p prime} 1/p
    = θ(x)/(x·log x) + ∫_{t ∈ (2,x]} (log t + 1)/(t²·log²t) · θ(t) dt

where `θ = Chebyshev.theta` is Mathlib's Chebyshev function
(`∑_{p ≤ x} log p`). Proved by applying Mathlib's Abel summation
formula (`sum_mul_eq_sub_sub_integral_mul`,
`Mathlib.NumberTheory.AbelSummation`) with `f(t) = 1/(t·log t)` and
coefficients `c(k) = log k` on primes, then simplifying both boundary
terms.

Why this matters for #647: the Hughes–Kitamura Brun-sieve density
bound (`|C(x)| ≪ x/(log x)⁷` for candidate counts) needs a
quantitative lower bound on `∑_{p≤z} 1/p` to control the Selberg
sieve's main term. Mathlib has the qualitative divergence of `∑ 1/p`
(`Mathlib.NumberTheory.SumPrimeReciprocals`) but no quantitative
Mertens theorem. This identity is exact — combined with Mathlib's
effective two-sided bounds on θ (`Chebyshev.theta_ge`,
`Chebyshev.theta_le_log4_mul_x`), it reduces quantitative Mertens to
bounding an explicit real integral, which is the next milestone.
-/

theorem erdos647_mertens_identity :
    ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ))
        = Chebyshev.theta x / (x * Real.log x)
          + ∫ t in Set.Ioc (2:ℝ) x,
              (Real.log t + 1) / (t^2 * (Real.log t)^2) * Chebyshev.theta t := by
  intro x hx
  set f : ℝ → ℝ := fun t => (t * Real.log t)⁻¹ with hf_def
  set g : ℝ → ℝ := fun t => -(Real.log t + 1) / (t^2 * (Real.log t)^2) with hg_def
  set c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0 with hc_def
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have hsub : Set.Icc (2:ℝ) x ⊆ {t:ℝ | t ≠ 0} := by
    intro t ht
    have h1 : (2:ℝ) ≤ t := (Set.mem_Icc.mp ht).1
    exact ne_of_gt (by linarith)
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
    · exact ((Real.continuousOn_log.mono hsub).add continuousOn_const).neg
    · exact (continuousOn_pow 2).mul ((Real.continuousOn_log.mono hsub).pow 2)
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
