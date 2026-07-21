/-
SolveAll #11 — dimension-two parameter arithmetic for Theorem 57.

The counterexample only needs `d = 2`.  Writing
  n ≤ (4 / τ)^2,  q = τ * sqrt (log (4 / τ)),  η = 8q,
the coordinatewise Gaussian tail thresholds for both the two-dimensional
normal perturbations and the scalar right-hand-side perturbations are at most
`η`.  The separate union bounds cost at most `6n/n^8`, which is already at
most `n⁻²` for `n ≥ 2`.
-/
import Mathlib

namespace SolveAll011.Tier3

/-- The logarithmic comparison behind both dimension-two tail thresholds. -/
theorem log_n_le_two_mul_log_four_div
    (n : ℕ) (τ : ℝ) (hn : 1 ≤ n) (hτ : 0 < τ)
    (hnupper : (n : ℝ) ≤ (4 / τ) ^ 2) :
    Real.log n ≤ 2 * Real.log (4 / τ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hratio : 0 < 4 / τ := div_pos (by norm_num) hτ
  have hlog := Real.log_le_log hnpos hnupper
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

/-- The two-dimensional row-norm threshold produced by the finite-coordinate
Gaussian union bound is dominated by the paper's `η = 8q`. -/
theorem d2_row_threshold_le_eight_q
    (n : ℕ) (τ : ℝ) (hn : 1 ≤ n) (hτ : 0 < τ) (hτ4 : τ ≤ 4)
    (hnupper : (n : ℝ) ≤ (4 / τ) ^ 2) :
    Real.sqrt 2 * (4 * τ * Real.sqrt (Real.log n)) ≤
      8 * (τ * Real.sqrt (Real.log (4 / τ))) := by
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hratio1 : 1 ≤ 4 / τ := (le_div_iff₀ hτ).2 (by nlinarith)
  have hlogratio : 0 ≤ Real.log (4 / τ) := Real.log_nonneg hratio1
  have hlogle : Real.log n ≤ 2 * Real.log (4 / τ) :=
    log_n_le_two_mul_log_four_div n τ hn hτ hnupper
  have hsqrt : Real.sqrt 2 * Real.sqrt (Real.log n) ≤
      2 * Real.sqrt (Real.log (4 / τ)) := by
    calc
      Real.sqrt 2 * Real.sqrt (Real.log n) =
          Real.sqrt (2 * Real.log n) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ Real.sqrt (4 * Real.log (4 / τ)) := by
        apply Real.sqrt_le_sqrt
        linarith
      _ = 2 * Real.sqrt (Real.log (4 / τ)) := by
        rw [show (4 : ℝ) * Real.log (4 / τ) = 4 * Real.log (4 / τ) by rfl,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  calc
    Real.sqrt 2 * (4 * τ * Real.sqrt (Real.log n)) =
        (4 * τ) * (Real.sqrt 2 * Real.sqrt (Real.log n)) := by ring
    _ ≤ (4 * τ) * (2 * Real.sqrt (Real.log (4 / τ))) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 8 * (τ * Real.sqrt (Real.log (4 / τ))) := by ring

/-- The scalar right-hand-side threshold is also dominated by the same `η`.
This lets the normal and right-hand-side tails share one roundness parameter. -/
theorem d2_scalar_threshold_le_eight_q
    (n : ℕ) (τ : ℝ) (hn : 1 ≤ n) (hτ : 0 < τ) (hτ4 : τ ≤ 4)
    (hnupper : (n : ℝ) ≤ (4 / τ) ^ 2) :
    4 * τ * Real.sqrt (Real.log n) ≤
      8 * (τ * Real.sqrt (Real.log (4 / τ))) := by
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hratio1 : 1 ≤ 4 / τ := (le_div_iff₀ hτ).2 (by nlinarith)
  have hlogratio : 0 ≤ Real.log (4 / τ) := Real.log_nonneg hratio1
  have hlogle : Real.log n ≤ 2 * Real.log (4 / τ) :=
    log_n_le_two_mul_log_four_div n τ hn hτ hnupper
  have hsqrt : Real.sqrt (Real.log n) ≤
      2 * Real.sqrt (Real.log (4 / τ)) := by
    calc
      Real.sqrt (Real.log n) ≤ Real.sqrt (2 * Real.log (4 / τ)) :=
        Real.sqrt_le_sqrt hlogle
      _ ≤ Real.sqrt (4 * Real.log (4 / τ)) := by
        apply Real.sqrt_le_sqrt
        linarith
      _ = 2 * Real.sqrt (Real.log (4 / τ)) := by
        rw [show (4 : ℝ) * Real.log (4 / τ) = 4 * Real.log (4 / τ) by rfl,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
  calc
    4 * τ * Real.sqrt (Real.log n) ≤
        (4 * τ) * (2 * Real.sqrt (Real.log (4 / τ))) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = 8 * (τ * Real.sqrt (Real.log (4 / τ))) := by ring

/-- The two row-wise union bounds, `4n/n^8` for two-dimensional normals and
`2n/n^8` for scalar right-hand sides, fit inside the target `n⁻²` failure
probability. -/
theorem six_mul_n_div_n_pow_eight_le_inv_n_sq
    (n : ℕ) (hn : 2 ≤ n) :
    6 * (n : ℝ) / (n : ℝ) ^ 8 ≤ 1 / (n : ℝ) ^ 2 := by
  let x : ℝ := n
  have hx : 2 ≤ x := by
    dsimp [x]
    exact_mod_cast hn
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hx5 : (6 : ℝ) ≤ x ^ 5 := by
    calc
      (6 : ℝ) ≤ 2 ^ 5 := by norm_num
      _ ≤ x ^ 5 := by gcongr
  apply (div_le_div_iff₀ (pow_pos hxpos 8) (pow_pos hxpos 2)).2
  have hmul : 6 * x ^ 3 ≤ x ^ 8 := by
    calc
      6 * x ^ 3 ≤ x ^ 5 * x ^ 3 :=
        mul_le_mul_of_nonneg_right hx5 (by positivity)
      _ = x ^ 8 := by ring
  dsimp [x] at hmul ⊢
  nlinarith

/-- The paper's small-noise assumption at `d = 2` implies the roundness
parameter needed by the geometric capstone is small. -/
theorem eight_q_le_one_over_650
    (q : ℝ) (hq : q ≤ 1 / 5200) : 8 * q ≤ 1 / 650 := by
  norm_num at hq ⊢
  linarith

end SolveAll011.Tier3

#print axioms SolveAll011.Tier3.log_n_le_two_mul_log_four_div
#print axioms SolveAll011.Tier3.d2_row_threshold_le_eight_q
#print axioms SolveAll011.Tier3.d2_scalar_threshold_le_eight_q
#print axioms SolveAll011.Tier3.six_mul_n_div_n_pow_eight_le_inv_n_sq
#print axioms SolveAll011.Tier3.eight_q_le_one_over_650
