/-
Erdős Problem #858 — toward the constant c₂ (Chojecki 2026, "An exact frontier
theorem and the asymptotic constant for Erdős problem #858").

c₂ integral lower bound on [1/3, 1/2] — improving c₂ ≥ 1/2 toward 0.6187.

The constant is c₂ = 1/2 + ∫_{α₂}^{1/2}(1 − Φ(u)) du. On [1/3, 1/2] the semiprime
term of Φ vanishes, so Φ(u) = log((1-u)/u), which is decreasing with maximum
log 2 at u = 1/3 (since (1-u)/u ≤ 2 ⟺ u ≥ 1/3). Hence 1 − Φ(u) ≥ 1 − log 2 > 0
on [1/3, 1/2], and integrating,
  ∫_{1/3}^{1/2} (1 − log((1-u)/u)) du ≥ (1/2 − 1/3)(1 − log 2) = (1/6)(1 − log 2)
  ≈ 0.0511.
Since α₂ < 1/3 and 1 − Φ ≥ 0 on [α₂, 1/3], this bounds the c₂ integral from below,
giving **c₂ ≥ 1/2 + (1/6)(1 − log 2) ≈ 0.551** — a genuine improvement on the
trivial `c₂ ≥ 1/2` (`erdos858_c2_lower_bound`, #63) toward the true
`c₂ = 0.6187712…`. Pure real analysis, no PNT.

Proof: `intervalIntegral.integral_mono_on` compares the integrand
`g(u) = 1 − log((1-u)/u)` to the constant `1 − log 2` on `Icc (1/3) (1/2)`
(pointwise via `(1-u)/u ≤ 2` on that range and `Real.log_le_log`); the constant
integral is `(1/2 − 1/3) • (1 − log 2) = (1/6)(1 − log 2)` via
`intervalIntegral.integral_const`. Integrability of `g` via
`ContinuousOn.intervalIntegrable` (`ContinuousOn.sub`/`.log`/`.div₀`, log argument
`(1-u)/u > 0` on `[1/3,1/2]`). Same shape as the I-upper-bound atom #74.

Kernel-verified via the proofsearch MCP:
  episode 9cb3cea3-14ad-4412-9fed-82ccb3c16210,
  problem_version_id d065db58-f701-427a-ad3b-aad35722d16e.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f847f2e90ff8172f10d4dd118e5d84235f24a1995cccc30966763491102bdd7b.
-/
import Mathlib

namespace Erdos858

/-- c₂ integral lower bound: `∫_{1/3}^{1/2}(1 − log((1-u)/u)) du ≥ (1/6)(1 − log 2)`.
On `[1/3,1/2]` the density prime term `log((1-u)/u) ≤ log 2`, so `1 − Φ ≥ 1 − log 2`;
integrating over the length-`1/6` interval gives the bound. With `c₂ = 1/2 +
∫_{α₂}^{1/2}(1 − Φ)` (and `1 − Φ ≥ 0` on `[α₂,1/3]`) this yields
`c₂ ≥ 1/2 + (1/6)(1 − log 2) ≈ 0.551`. -/
theorem erdos858_c2_integral_lower_half :
    (1/6 : ℝ) * (1 - Real.log 2) ≤ ∫ u in (1/3:ℝ)..(1/2), (1 - Real.log ((1 - u) / u)) := by
  have hab : (1/3:ℝ) ≤ 1/2 := by norm_num
  have hcont : ContinuousOn (fun u => 1 - Real.log ((1 - u) / u)) (Set.uIcc (1/3:ℝ) (1/2)) := by
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.log
    · apply ContinuousOn.div₀
      · fun_prop
      · fun_prop
      · intro u hu; exact ne_of_gt (lt_of_lt_of_le (by norm_num) hu.1)
    · intro u hu
      have h2 : (0:ℝ) < u := lt_of_lt_of_le (by norm_num) hu.1
      have h1 : (0:ℝ) < 1 - u := by linarith [hu.2]
      exact ne_of_gt (div_pos h1 h2)
  have hgi : IntervalIntegrable (fun u => 1 - Real.log ((1 - u) / u)) MeasureTheory.volume (1/3) (1/2) := hcont.intervalIntegrable
  have hci : IntervalIntegrable (fun _ : ℝ => 1 - Real.log 2) MeasureTheory.volume (1/3) (1/2) := intervalIntegrable_const
  have hpoint : ∀ u ∈ Set.Icc (1/3:ℝ) (1/2), (1 - Real.log 2) ≤ 1 - Real.log ((1 - u) / u) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hupos : (0:ℝ) < u := lt_of_lt_of_le (by norm_num) hu1
    have hrpos : (0:ℝ) < (1 - u)/u := div_pos (by linarith) hupos
    have hratio : (1 - u) / u ≤ 2 := by rw [div_le_iff₀ hupos]; linarith
    have hlog : Real.log ((1 - u)/u) ≤ Real.log 2 := Real.log_le_log hrpos hratio
    linarith
  calc (1/6 : ℝ) * (1 - Real.log 2)
      = (1/2 - 1/3) * (1 - Real.log 2) := by norm_num
    _ = ∫ _ in (1/3:ℝ)..(1/2), (1 - Real.log 2) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ ∫ u in (1/3:ℝ)..(1/2), (1 - Real.log ((1 - u) / u)) := intervalIntegral.integral_mono_on hab hci hgi hpoint

end Erdos858
