import Mathlib

/-!
# Erdős #647 — Abel identity for the prime logarithmic moment

Kernel-verified through the tracked proof-search pipeline on 2026-07-15.

  problem_version_id  34305a84-6663-460a-a0e8-006337c85838
  episode_id          fbf2047c-f3aa-4a54-9529-8ab7ecdd81e5
  root_statement_hash a35ce4674c9889b018360f522feeba117076c0036d4083c345d0667d116eec50
  outcome             kernel_verified (root_proved), 4 tracked attempts
  environment_hash    9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d

Abel summation with f(t)=1/t gives
  ∑_{p≤x} log(p)/p = θ(x)/x + ∫_{(2,x]} θ(t)/t² dt.
This is the exact identity needed to control the log moment in L_R's tail.
-/

theorem erdos647_prime_log_div_identity :
    ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, Real.log p / (p:ℝ)
        = Chebyshev.theta x / x +
          ∫ t in Set.Ioc (2:ℝ) x, Chebyshev.theta t / t^2 := by
  intro x hx
  set f : ℝ → ℝ := fun t => t⁻¹ with hf_def
  set g : ℝ → ℝ := fun t => -(t^2)⁻¹ with hg_def
  set c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0 with hc_def
  have hsub : Set.Icc (2:ℝ) x ⊆ {t:ℝ | t ≠ 0} := by
    intro t ht
    exact ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1])
  have hderiv : ∀ t ∈ Set.Icc (2:ℝ) x, HasDerivAt f (g t) t := by
    intro t ht
    have htne : t ≠ 0 := hsub ht
    rw [hf_def, hg_def]
    exact hasDerivAt_inv htne
  have hf_diff : ∀ t ∈ Set.Icc (2:ℝ) x, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hderiv_eq : Set.EqOn g (deriv f) (Set.Icc (2:ℝ) x) :=
    fun t ht => (hderiv t ht).deriv.symm
  have hgcont : ContinuousOn g (Set.Icc (2:ℝ) x) := by
    rw [hg_def]
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have htpos : (0:ℝ) < t := by linarith [(Set.mem_Icc.mp ht).1]
      positivity
  have hf_int : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (2:ℝ) x)
      MeasureTheory.volume := by
    apply MeasureTheory.IntegrableOn.congr_fun (f := g)
    · exact hgcont.integrableOn_Icc
    · exact hderiv_eq
    · exact measurableSet_Icc
  have hthetadef : ∀ y : ℝ, Chebyshev.theta y =
      ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, c k := by
    intro y
    rw [Chebyshev.theta, hc_def, Finset.sum_filter]
    rw [show Finset.Icc 0 ⌊y⌋₊ = insert 0 (Finset.Ioc 0 ⌊y⌋₊) by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega]
    rw [Finset.sum_insert (by simp)]
    simp
  have h2le : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have habel := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0:ℝ) ≤ 2)
    hx hf_diff hf_int
  have hfloor2 : ⌊(2:ℝ)⌋₊ = 2 := by norm_num
  rw [hfloor2] at habel
  have hset : (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime =
      insert 2 ((Finset.Ioc 2 ⌊x⌋₊).filter Nat.Prime) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, hkn⟩, hp⟩
      have hk2 : 2 ≤ k := hp.two_le
      rcases eq_or_lt_of_le hk2 with heq | hlt
      · left
        exact heq.symm
      · right
        exact ⟨⟨hlt, hkn⟩, hp⟩
    · rintro (rfl | ⟨⟨h1, hkn⟩, hp⟩)
      · exact ⟨⟨by norm_num, h2le⟩, Nat.prime_two⟩
      · exact ⟨⟨by omega, hkn⟩, hp⟩
  have hLHS : ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, f (k:ℝ) * c k =
      (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, Real.log p / (p:ℝ)) -
        Real.log 2 / 2 := by
    have hfck : ∀ k ∈ Finset.Ioc 2 ⌊x⌋₊,
        f (k:ℝ) * c k =
          if k.Prime then Real.log k / (k:ℝ) else 0 := by
      intro k hk
      rw [hf_def, hc_def]
      by_cases hp : k.Prime
      · simp only [hp, if_true]
        ring
      · simp [hp]
    rw [Finset.sum_congr rfl hfck, ← Finset.sum_filter, hset,
      Finset.sum_insert (by simp)]
    norm_num
  rw [hLHS] at habel
  have hth2sum : ∑ k ∈ Finset.Icc 0 2, c k = Real.log 2 := by
    simp only [show Finset.Icc 0 2 = {0,1,2} by decide, Finset.sum_insert,
      Finset.sum_singleton]
    rw [hc_def]
    norm_num [Nat.prime_two]
  rw [hth2sum] at habel
  have hf2 : f 2 * Real.log 2 = Real.log 2 / 2 := by
    rw [hf_def]
    ring
  rw [← hthetadef x] at habel
  have hintsimp : ∫ t in Set.Ioc (2:ℝ) x,
      deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
      ∫ t in Set.Ioc (2:ℝ) x, -(Chebyshev.theta t / t^2) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    have ht' : t ∈ Set.Icc (2:ℝ) x :=
      Set.mem_Icc.mpr ⟨le_of_lt ht.1, ht.2⟩
    rw [← hderiv_eq ht', hg_def, ← hthetadef t]
    ring
  rw [hintsimp, MeasureTheory.integral_neg, hf2] at habel
  have hfxthm : f x * Chebyshev.theta x = Chebyshev.theta x / x := by
    rw [hf_def]
    ring
  linarith [habel, hfxthm]
