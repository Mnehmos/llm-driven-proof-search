/-
Erdős Problem #858 — Proposition 5.6 (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

Semiprime-integral LOWER bound atom — the two-sided partner to the upper bound
`erdos858_I_upper_bound` (#74), for tightening α₂ and c₂.

The semiprime contribution to the density Φ is
  I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv.
The integrand g(v) = (1/v)·log((1-u-v)/v) is positive and decreasing on
[u,(1-u)/2] and vanishes at the right endpoint, so a positive lower bound needs a
sub-interval. Splitting at the midpoint m = (u+1)/4 (with u < m < (1-u)/2 for
1/4 < u < 1/3): on [u,m] the integrand is ≥ its right-endpoint value
g(m) = (4/(u+1))·log((3-5u)/(u+1)) (both factors positive and decreasing), and on
[m,(1-u)/2] it is ≥ 0. Hence
  I(u) ≥ (m - u)·g(m) = ((1-3u)/4)·(4/(u+1))·log((3-5u)/(u+1)).
Together with #74 this brackets I(u) two-sidedly; the Meissel–Mertens constant
cancels in the interval form, so no PNT is needed.

Proof: `intervalIntegral.integral_add_adjacent_intervals` splits I at m; the left
part is bounded below by `intervalIntegral.integral_mono_on` comparing g to the
constant g(m) (pointwise `g(m) ≤ g(v)` via `mul_le_mul`: `4/(u+1) ≤ 1/v` and
`log((3-5u)/(u+1)) ≤ log((1-u-v)/v)`, both by `div_le_div_iff₀`, the log-ratio
reduced by `nlinarith` to `4(1-u)((u+1)/4 - v) ≥ 0`); the right part is `≥ 0` by
`intervalIntegral.integral_nonneg` (integrand `≥ 0`). Sub-interval integrability
via `(hcont.mono (Set.Icc_subset_Icc_right/left)).intervalIntegrable_of_Icc`,
continuity reusing the #74 pattern.

Kernel-verified via the proofsearch MCP:
  episode 3dc5b81d-1f27-4382-b52c-9d9702ab209a,
  problem_version_id 38f83ae7-3155-4ff1-8984-0e59c9407696.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 792930193eeeed5e62380672657b9d4ec40758cb88a160887e2ec03f77844ada.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6 semiprime-integral LOWER bound: on `1/4 < u < 1/3`,
`I(u) = ∫_u^{(1-u)/2} (1/v)·log((1-u-v)/v) dv` is at least
`((1-3u)/4)·(4/(u+1))·log((3-5u)/(u+1))` (the length of the left half `[u,(u+1)/4]`
times the integrand's value at the midpoint). Two-sided partner to
`erdos858_I_upper_bound`; used to tighten α₂ and c₂. -/
theorem erdos858_I_lower_bound :
    ∀ (u : ℝ), 1/4 < u → u < 1/3 →
      ((1 - 3*u)/4) * ((4/(u+1)) * Real.log ((3 - 5*u)/(u+1)))
        ≤ ∫ v in u..(1 - u)/2, (1/v) * Real.log ((1 - u - v)/v) := by
  intro u hu1 hu2
  have hu0 : (0:ℝ) < u := by linarith
  have hu1pos : (0:ℝ) < u + 1 := by linarith
  have hum : u ≤ (u+1)/4 := by linarith
  have hmb : (u+1)/4 ≤ (1-u)/2 := by linarith
  have hab : u ≤ (1-u)/2 := by linarith
  have hcontIcc : ContinuousOn (fun v => (1/v) * Real.log ((1 - u - v)/v)) (Set.Icc u ((1-u)/2)) := by
    have c1 : ContinuousOn (fun v : ℝ => 1/v) (Set.Icc u ((1-u)/2)) := by
      apply ContinuousOn.div₀
      · fun_prop
      · fun_prop
      · intro v hv; exact ne_of_gt (lt_of_lt_of_le hu0 hv.1)
    have c2 : ContinuousOn (fun v : ℝ => Real.log ((1 - u - v)/v)) (Set.Icc u ((1-u)/2)) := by
      apply ContinuousOn.log
      · apply ContinuousOn.div₀
        · fun_prop
        · fun_prop
        · intro v hv; exact ne_of_gt (lt_of_lt_of_le hu0 hv.1)
      · intro v hv
        have h1 : (0:ℝ) < 1 - u - v := by linarith [hv.2]
        exact ne_of_gt (div_pos h1 (lt_of_lt_of_le hu0 hv.1))
    exact c1.mul c2
  have hgi_um : IntervalIntegrable (fun v => (1/v) * Real.log ((1 - u - v)/v)) MeasureTheory.volume u ((u+1)/4) :=
    (hcontIcc.mono (Set.Icc_subset_Icc_right hmb)).intervalIntegrable_of_Icc hum
  have hgi_mb : IntervalIntegrable (fun v => (1/v) * Real.log ((1 - u - v)/v)) MeasureTheory.volume ((u+1)/4) ((1-u)/2) :=
    (hcontIcc.mono (Set.Icc_subset_Icc_left hum)).intervalIntegrable_of_Icc hmb
  have hci : IntervalIntegrable (fun _ : ℝ => (4/(u+1)) * Real.log ((3 - 5*u)/(u+1))) MeasureTheory.volume u ((u+1)/4) := intervalIntegrable_const
  have hpoint : ∀ v ∈ Set.Icc u ((u+1)/4), (4/(u+1)) * Real.log ((3 - 5*u)/(u+1)) ≤ (1/v) * Real.log ((1 - u - v)/v) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hvpos : (0:ℝ) < v := lt_of_lt_of_le hu0 hv1
    have hcpos : (0:ℝ) < (3 - 5*u)/(u+1) := by apply div_pos <;> linarith
    have hinv : 4/(u+1) ≤ 1/v := by rw [div_le_div_iff₀ hu1pos hvpos]; linarith
    have hratio : (3 - 5*u)/(u+1) ≤ (1 - u - v)/v := by
      rw [div_le_div_iff₀ hu1pos hvpos]
      nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - u by linarith) (show (0:ℝ) ≤ (u+1)/4 - v by linarith)]
    have hlog_le : Real.log ((3 - 5*u)/(u+1)) ≤ Real.log ((1 - u - v)/v) := Real.log_le_log hcpos hratio
    have hlog_nn : 0 ≤ Real.log ((3 - 5*u)/(u+1)) := by apply Real.log_nonneg; rw [one_le_div hu1pos]; linarith
    have hinv_nn : (0:ℝ) ≤ 1/v := le_of_lt (one_div_pos.mpr hvpos)
    exact mul_le_mul hinv hlog_le hlog_nn hinv_nn
  have hsplit : (∫ v in u..(1-u)/2, (1/v) * Real.log ((1 - u - v)/v))
      = (∫ v in u..(u+1)/4, (1/v) * Real.log ((1 - u - v)/v)) + (∫ v in (u+1)/4..(1-u)/2, (1/v) * Real.log ((1 - u - v)/v)) :=
    (intervalIntegral.integral_add_adjacent_intervals hgi_um hgi_mb).symm
  have hlow : ((1 - 3*u)/4) * ((4/(u+1)) * Real.log ((3 - 5*u)/(u+1))) ≤ ∫ v in u..(u+1)/4, (1/v) * Real.log ((1 - u - v)/v) := by
    calc ((1 - 3*u)/4) * ((4/(u+1)) * Real.log ((3 - 5*u)/(u+1)))
        = ((u+1)/4 - u) * ((4/(u+1)) * Real.log ((3 - 5*u)/(u+1))) := by ring
      _ = ∫ _ in u..(u+1)/4, (4/(u+1)) * Real.log ((3 - 5*u)/(u+1)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ ∫ v in u..(u+1)/4, (1/v) * Real.log ((1 - u - v)/v) := intervalIntegral.integral_mono_on hum hci hgi_um hpoint
  have hrest : (0:ℝ) ≤ ∫ v in (u+1)/4..(1-u)/2, (1/v) * Real.log ((1 - u - v)/v) := by
    apply intervalIntegral.integral_nonneg hmb
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hvpos : (0:ℝ) < v := lt_of_lt_of_le (by linarith) hv1
    have hval : (1:ℝ) ≤ (1 - u - v)/v := by rw [le_div_iff₀ hvpos]; linarith
    have hlog : 0 ≤ Real.log ((1 - u - v)/v) := Real.log_nonneg hval
    exact mul_nonneg (le_of_lt (one_div_pos.mpr hvpos)) hlog
  rw [hsplit]
  linarith

end Erdos858
