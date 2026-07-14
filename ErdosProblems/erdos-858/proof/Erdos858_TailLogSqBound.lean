/-
Erdős problem #858 — Chojecki 2026, analytic §5 building block toward the exact
constant c₂ via Mertens' first theorem  Σ_{p≤x}(log p)/p = log x + O(1).

EXPLICIT CONSTANT BOUND for the INTEGER prime-power tail.

For all N, the partial sum of (log n)/n² over the integers 2 ≤ n ≤ N is bounded
by an explicit constant:

    Σ_{n=2}^{N} (log n)/n²  ≤  2.

This is the "tail-numeric" crux underlying the sharp-constant program. Combined
with the per-prime GEOMETRIC-TAIL bound Σ_{k≥2}(log p)/p^k ≤ (log p)/(p(p-1))
(campaign atom #62), it certifies the prime-power correction constant T ≤ 1: the
prime-restricted sum Σ_p (log p)/(p(p-1)) ≈ 0.7554 is smaller, and even this
unrestricted integer over-estimate already gives the ≤ 2 bound flagged as needed
in `Erdos858_Mertens1_PrimePowerGeometricTail`.

Method (the INTEGRAL TEST the campaign flagged as "the only reachable route to a
numeric constant"). The summand `f(x) = log x / x²` is antitone on `[2,∞)`, since

    d/dx (log x / x²) = (1 − 2 log x)/x³ ≤ 0   for x ≥ 2 > e^{1/2}

(using `log x ≥ log 2 > 1/2`). Hence `AntitoneOn.sum_le_integral_Ico` applies. The
antiderivative of `log x / x²` is `−(log x + 1)/x`, so

    ∫_2^N log x / x² dx = (log 2 + 1)/2 − (log N + 1)/N ≤ (log 2 + 1)/2,

the upper bound following from `(log N + 1)/N ≥ 0` for N ≥ 1. Peeling the `n = 2`
term:

    Σ_{n=2}^N (log n)/n² ≤ (log 2)/4 + (log 2 + 1)/2 = (3/4)·log 2 + 1/2 ≤ 5/4 ≤ 2

using `log 2 ≤ 1` (`Real.log_le_sub_one_of_pos`).

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : b4b2d65c-9b4d-41f5-a776-ff8fcce804b1
  episode_id         : b97b4c00-e1ff-45d1-8921-744c5b8988d8
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 3 (1: `lt_or_le` renamed → `by_cases`; 2: post-peel
                       `simp` no-progress → `show`; 3: verified)
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 69f2d5c5475524c4d4946dcb03782dd7a578e3a5e7f4126a6ac10e6693be6dd4

Key Mathlib lemmas:
  `AntitoneOn.sum_le_integral_Ico`  (Mathlib/Analysis/SumIntegralComparisons.lean)
  `antitoneOn_of_deriv_nonpos`      (Mathlib/Analysis/Calculus/Deriv/MeanValue.lean)
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`
                                    (Mathlib/.../IntervalIntegral/FundThmCalculus.lean)
  `Real.log_two_gt_d9`, `Real.log_le_sub_one_of_pos`
Technique mirrors the kernel-verified `Erdos858_Mertens2_ErrorIntegral` (FTC with a
hand-built `HasDerivAt` antiderivative) and `Mathlib.NumberTheory.Harmonic.Bounds`
(the `map_add_right_Ico` / `sum_eq_sum_Ico_succ_bot` reindex-and-peel pattern).
-/
import Mathlib

open scoped BigOperators

/-- Explicit constant bound on the integer tail `Σ_{n=2}^N (log n)/n² ≤ 2`, for all
`N`, via the integral test on the antitone tail of `log x / x²`. Feeds the Mertens-1
prime-power correction `T ≤ 1` for the sharp Erdős-#858 constant `c₂`. -/
theorem erdos858_tail_log_sq_bound :
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 2 N, Real.log (n : ℝ) / (n : ℝ) ^ 2) ≤ 2 := by
  intro N
  by_cases hN : 2 ≤ N
  · -- 2 ≤ N
    have hx2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hsubset : Set.Icc (2 : ℝ) (N : ℝ) ⊆ {t : ℝ | t ≠ 0} := fun t ht =>
      ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith)
    -- Pointwise derivative of F(x) = log x / x^2
    have hderiv : ∀ x : ℝ, 0 < x →
        HasDerivAt (fun s : ℝ => Real.log s / s ^ 2)
          ((x⁻¹ * x ^ 2 - Real.log x * (2 * x)) / (x ^ 2) ^ 2) x := by
      intro x hxpos
      have hxne : x ≠ 0 := ne_of_gt hxpos
      have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      exact (Real.hasDerivAt_log hxne).div hpow (pow_ne_zero 2 hxne)
    -- F is antitone on [2, N]
    have hAnti : AntitoneOn (fun x : ℝ => Real.log x / x ^ 2) (Set.Icc (2 : ℝ) (N : ℝ)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
      · apply ContinuousOn.div
        · exact Real.continuousOn_log.mono hsubset
        · exact (continuous_pow 2).continuousOn
        · intro t ht
          exact pow_ne_zero 2 (ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
      · rw [interior_Icc]
        intro x hx
        exact (hderiv x (by have := hx.1; linarith)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxpos : (0 : ℝ) < x := by have := hx.1; linarith
        have hxne : x ≠ 0 := ne_of_gt hxpos
        rw [(hderiv x hxpos).deriv]
        have hlogx : (1 : ℝ) / 2 ≤ Real.log x := by
          have h2x : (2 : ℝ) ≤ x := le_of_lt hx.1
          have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2x
          have hl2 := Real.log_two_gt_d9
          linarith
        rw [div_nonpos_iff]
        right
        constructor
        · have hxx : x⁻¹ * x ^ 2 = x := by
            rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
          rw [hxx]
          nlinarith [mul_nonneg hxpos.le (show (0 : ℝ) ≤ 2 * Real.log x - 1 by linarith)]
        · positivity
    -- Lift antitone to the nat-cast interval expected by the comparison lemma
    have hAnti2 : AntitoneOn (fun x : ℝ => Real.log x / x ^ 2)
        (Set.Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
      have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
      rw [h2]; exact hAnti
    -- Sum ≤ integral (integral test)
    have hcmp := @AntitoneOn.sum_le_integral_Ico 2 N
        (fun x : ℝ => Real.log x / x ^ 2) hN hAnti2
    simp only [Nat.cast_ofNat] at hcmp
    -- Antiderivative and integral bound
    have hmain : ∀ t ∈ Set.uIcc (2 : ℝ) (N : ℝ),
        HasDerivAt (fun s : ℝ => -((Real.log s + 1) * s⁻¹)) (Real.log t / t ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hx2N] at ht
      have ht2 : (2 : ℝ) ≤ t := (Set.mem_Icc.mp ht).1
      have htpos : (0 : ℝ) < t := by linarith
      have htne : t ≠ 0 := ne_of_gt htpos
      have hnum : HasDerivAt (fun s : ℝ => Real.log s + 1) t⁻¹ t :=
        (Real.hasDerivAt_log htne).add_const 1
      have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv htne
      have hbase : HasDerivAt (fun s : ℝ => -((Real.log s + 1) * s⁻¹))
          (-(t⁻¹ * t⁻¹ + (Real.log t + 1) * (-(t ^ 2)⁻¹))) t := (hnum.mul hinv).neg
      have hval : -(t⁻¹ * t⁻¹ + (Real.log t + 1) * (-(t ^ 2)⁻¹)) = Real.log t / t ^ 2 := by
        first
        | (field_simp; ring)
        | field_simp
      rw [hval] at hbase
      exact hbase
    have hcont : ContinuousOn (fun t : ℝ => Real.log t / t ^ 2) (Set.uIcc (2 : ℝ) (N : ℝ)) := by
      rw [Set.uIcc_of_le hx2N]
      apply ContinuousOn.div
      · exact Real.continuousOn_log.mono hsubset
      · exact (continuous_pow 2).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith))
    have hint : IntervalIntegrable (fun t : ℝ => Real.log t / t ^ 2) MeasureTheory.volume 2 (N : ℝ) :=
      hcont.intervalIntegrable
    have hibound : (∫ x in (2 : ℝ)..(N : ℝ), Real.log x / x ^ 2) ≤ (Real.log 2 + 1) / 2 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hmain hint]
      have hNlog : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
      have hterm : (0 : ℝ) ≤ (Real.log (N : ℝ) + 1) * (N : ℝ)⁻¹ :=
        mul_nonneg (by linarith) (by positivity)
      show -((Real.log (N : ℝ) + 1) * (N : ℝ)⁻¹) - -((Real.log 2 + 1) * (2 : ℝ)⁻¹)
          ≤ (Real.log 2 + 1) / 2
      have h2 : (Real.log 2 + 1) * (2 : ℝ)⁻¹ = (Real.log 2 + 1) / 2 := by ring
      linarith [hterm, h2]
    -- Reindex the target sum: Icc 2 N ↦ Ico 1 N via +1, then peel the bottom term
    have hmap : (Finset.Ico 1 N).map (addRightEmbedding 1) = Finset.Icc 2 N := by
      rw [Finset.map_add_right_Ico, Finset.Ico_add_one_right_eq_Icc]
    rw [← hmap, Finset.sum_map]
    simp only [addRightEmbedding_apply]
    rw [Finset.sum_eq_sum_Ico_succ_bot (show (1 : ℕ) < N by omega)]
    show Real.log ((1 + 1 : ℕ) : ℝ) / ((1 + 1 : ℕ) : ℝ) ^ 2
        + (∑ i ∈ Finset.Ico 2 N, Real.log ((i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) ≤ 2
    have hc : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
    rw [hc]
    have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [h4]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hSb := le_trans hcmp hibound
    linarith [hSb, hl2]
  · -- ¬ 2 ≤ N: the summation range is empty
    rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    norm_num
