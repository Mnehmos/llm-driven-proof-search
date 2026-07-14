/-
Erdős problem #858 — Chojecki 2026, "An exact frontier theorem and the asymptotic
constant for Erdős problem #858", §5 exact-constant development (Mertens' first
theorem input toward the sharp c₂).

EXPLICIT CONSTANT BOUND for the INTEGER prime-power correction over-estimate.

For all N, the partial sum of (log n)/(n(n-1)) over the integers 2 ≤ n ≤ N is
bounded by an explicit constant:

    Σ_{n=2}^{N} (log n)/(n(n-1))  ≤  2.

Role in the sharp-constant program.  The sharp Mertens-1 correction constant is
T = Σ_p (log p)/(p(p-1)) ≈ 0.7554 (prime-restricted).  Atom #62
(`erdos858_mertens1_prime_power_geometric_tail`) reduces the non-prime von
Mangoldt correction  Σ_{d≤N, ¬prime} Λ(d)/d  to this quantity via the per-base
geometric tail  Σ_{k≥2}(log p)/p^k ≤ (log p)/(p(p-1)).  Dropping the prime
restriction gives the integer over-estimate  Σ_{n≥2}(log n)/(n(n-1)) ≈ 1.2578,
which atom #62's exposition flagged as certifying the correction constant ≤ 2 but
which had NOT been discharged.  This atom discharges it.  Because the summand is
nonnegative, the same bound dominates and hence certifies the prime-restricted
correction  Σ_{p≤N, prime} (log p)/(p(p-1)) ≤ 2  (a `Finset.sum_le_sum_of_subset`
away).

Verifier-backed proof via the `proofsearch` MCP (Lean 4).

  paper ref          : Chojecki 2026, §5 (Mertens' first theorem input)
  problem_version_id : e37ff73c-74fb-4041-beb6-938422589d6f
  episode_id         : 62046e39-ad23-41e5-ac47-cc56b333375d
  outcome            : kernel_verified (termination_reason = root_proved)
  submissions used   : 1
  toolchain          : leanprover/lean4:v4.32.0-rc1 +
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: a2a5b34ada4116fabd664f345b50fe8c0a05f0ffa8e4aa3f23ea30ed8824ff7c

Method.
  (1) SHARPENED integral test.  Inline the bound  Σ_{n=2}^N (log n)/n² ≤ 5/4,
      obtained by the exact machinery of the kernel-verified
      `erdos858_tail_log_sq_bound` (HasDerivAt for log x/x², antitonicity via
      `antitoneOn_of_deriv_nonpos`, `AntitoneOn.sum_le_integral_Ico`, FTC with the
      hand-built antiderivative −(log x + 1)/x, then reindex-and-peel).  The only
      change from that verified proof is the target RHS: its internal estimate is
      the SHARP  (3/4)·log 2 + 1/2, so retargeting 2 ↦ 5/4 is free — the final
      `linarith` closes because (3/4)·log 2 + 1/2 ≤ 5/4 ⇔ log 2 ≤ 1.
  (2) n = 2 isolation.  Split  Finset.Icc 2 N = insert 2 (Finset.Icc 3 N).  The
      n = 2 term is (log 2)/(2·1) = (log 2)/2 (denominator p(p-1) = 2, not p² = 4).
  (3) Termwise domination for n ≥ 3.  Since n ≥ 3 ⟹ (n−1) ≥ (2/3)n, we get
      n(n−1) ≥ (2/3)n², hence  (log n)/(n(n−1)) ≤ (3/2)·(log n)/n².  Proved via
      `div_le_div_iff₀` (the current, non-deprecated two-sided positive-denominator
      rewrite) reducing to  log n·(2n²) ≤ 3 log n·n(n−1), closed by `nlinarith`
      with the hint  log n · n · (n−3) ≥ 0.
  (4) Assembly.  With Σ_{n≥3}(log n)/n² ≤ 5/4 − (log 2)/4 (peel n=2 from (1)),
          total ≤ (log 2)/2 + (3/2)(5/4 − (log 2)/4) = 15/8 + (log 2)/8 ≤ 2,
      using log 2 ≤ 1 (`Real.log_le_sub_one_of_pos`); closed by `linarith`.
  Boundary N ≤ 1: the range `Finset.Icc 2 N` is empty (`Finset.Icc_eq_empty`).

Key Mathlib lemmas:
  `AntitoneOn.sum_le_integral_Ico`   (Mathlib/Analysis/SumIntegralComparisons.lean)
  `antitoneOn_of_deriv_nonpos`       (Mathlib/Analysis/Calculus/Deriv/MeanValue.lean)
  `intervalIntegral.integral_eq_sub_of_hasDerivAt`  (FundThmCalculus)
  `div_le_div_iff₀`                  (Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean)
  `Real.log_two_gt_d9`, `Real.log_le_sub_one_of_pos`, `Finset.sum_le_sum`,
  `Finset.sum_insert`, `Finset.mul_sum`.
Technique mirrors the kernel-verified `Erdos858_TailLogSqBound` (which this
sharpens and consumes) and `Erdos858_Mertens1_PrimePowerGeometricTail` (atom #62,
the per-prime geometric tail this integer bound over-estimates).
-/
import Mathlib

open scoped BigOperators

/-- Erdős #858, §5 sharp-constant input: the INTEGER prime-power correction
over-estimate.  For every `N`,
`Σ_{n=2}^N (log n)/(n(n-1)) ≤ 2`.
This discharges the ≤ 2 certification flagged in atom #62
(`erdos858_mertens1_prime_power_geometric_tail`) for the Mertens-1 correction
constant `T`, and dominates the prime-restricted sum
`Σ_{p≤N, prime} (log p)/(p(p-1)) ≤ 2`. -/
theorem erdos858_integer_tail_log_over_n_pm1_le_two :
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 2 N, Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤ 2 := by
  intro N
  -- Sub-bound: Σ_{n=2}^N (log n)/n² ≤ 5/4 (integral test on the antitone tail of log x/x²).
  have h54 : (∑ n ∈ Finset.Icc 2 N, Real.log (n : ℝ) / (n : ℝ) ^ 2) ≤ 5 / 4 := by
    by_cases hN : 2 ≤ N
    · have hx2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hsubset : Set.Icc (2 : ℝ) (N : ℝ) ⊆ {t : ℝ | t ≠ 0} := fun t ht =>
        ne_of_gt (by have := (Set.mem_Icc.mp ht).1; linarith)
      have hderiv : ∀ x : ℝ, 0 < x →
          HasDerivAt (fun s : ℝ => Real.log s / s ^ 2)
            ((x⁻¹ * x ^ 2 - Real.log x * (2 * x)) / (x ^ 2) ^ 2) x := by
        intro x hxpos
        have hxne : x ≠ 0 := ne_of_gt hxpos
        have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        exact (Real.hasDerivAt_log hxne).div hpow (pow_ne_zero 2 hxne)
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
      have hAnti2 : AntitoneOn (fun x : ℝ => Real.log x / x ^ 2)
          (Set.Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
        have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
        rw [h2]; exact hAnti
      have hcmp := @AntitoneOn.sum_le_integral_Ico 2 N
          (fun x : ℝ => Real.log x / x ^ 2) hN hAnti2
      simp only [Nat.cast_ofNat] at hcmp
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
      have hmap : (Finset.Ico 1 N).map (addRightEmbedding 1) = Finset.Icc 2 N := by
        rw [Finset.map_add_right_Ico, Finset.Ico_add_one_right_eq_Icc]
      rw [← hmap, Finset.sum_map]
      simp only [addRightEmbedding_apply]
      rw [Finset.sum_eq_sum_Ico_succ_bot (show (1 : ℕ) < N by omega)]
      show Real.log ((1 + 1 : ℕ) : ℝ) / ((1 + 1 : ℕ) : ℝ) ^ 2
          + (∑ i ∈ Finset.Ico 2 N, Real.log ((i + 1 : ℕ) : ℝ) / ((i + 1 : ℕ) : ℝ) ^ 2) ≤ 5 / 4
      have hc : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
      rw [hc]
      have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [h4]
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
      have hSb := le_trans hcmp hibound
      linarith [hSb, hl2]
    · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]; norm_num
  -- Main comparison.
  by_cases hN : 2 ≤ N
  · have hInsert : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h2notin : (2 : ℕ) ∉ Finset.Icc 3 N := by
      intro h; rw [Finset.mem_Icc] at h; omega
    -- Termwise bound for n ≥ 3: log n/(n(n-1)) ≤ (3/2)(log n/n²).
    have hterm : ∀ n ∈ Finset.Icc 3 N,
        Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ (3 / 2) * (Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
      intro n hn
      have hn3 : 3 ≤ n := (Finset.mem_Icc.mp hn).1
      have ha : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
      have hd1 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hrw : (3 / 2) * (Real.log (n : ℝ) / (n : ℝ) ^ 2)
          = (3 * Real.log (n : ℝ)) / (2 * (n : ℝ) ^ 2) := by ring
      rw [hrw, div_le_div_iff₀ hd1 (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hlog (show (0 : ℝ) ≤ (n : ℝ) by linarith))
        (show (0 : ℝ) ≤ (n : ℝ) - 3 by linarith)]
    -- Split the n² sub-bound at n = 2 to bound the Icc 3 N tail.
    have hsplitnsq : (∑ n ∈ Finset.Icc 2 N, Real.log (n : ℝ) / (n : ℝ) ^ 2)
        = Real.log 2 / 4 + (∑ n ∈ Finset.Icc 3 N, Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
      rw [hInsert, Finset.sum_insert h2notin]
      congr 1 <;> norm_num
    have hb2 : (∑ n ∈ Finset.Icc 3 N, Real.log (n : ℝ) / (n : ℝ) ^ 2) ≤ 5 / 4 - Real.log 2 / 4 := by
      linarith [h54, hsplitnsq]
    have hb1 : (∑ n ∈ Finset.Icc 3 N, Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
        ≤ (3 / 2) * (∑ n ∈ Finset.Icc 3 N, Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
      calc (∑ n ∈ Finset.Icc 3 N, Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
          ≤ (∑ n ∈ Finset.Icc 3 N, (3 / 2) * (Real.log (n : ℝ) / (n : ℝ) ^ 2)) :=
            Finset.sum_le_sum hterm
        _ = (3 / 2) * (∑ n ∈ Finset.Icc 3 N, Real.log (n : ℝ) / (n : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    -- Assemble: split the target sum at n = 2.
    rw [hInsert, Finset.sum_insert h2notin]
    have h2t : Real.log ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) * (((2 : ℕ) : ℝ) - 1)) = Real.log 2 / 2 := by
      norm_num
    rw [h2t]
    linarith [hb1, hb2, hl2]
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]; norm_num
