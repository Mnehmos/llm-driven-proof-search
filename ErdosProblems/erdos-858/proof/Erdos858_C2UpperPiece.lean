/-
Erdős Problem #858 — toward the exact constant c₂ (Chojecki 2026, "An exact
frontier theorem and the asymptotic constant for Erdős problem #858").

c₂ upper-bound piece on [a, 1/3] — the ingredient completing the two-sided c₂
bracket c₂ ∈ [0.610, 0.633] around the true 0.6187712….

On [a, 1/3] with 1/4 ≤ a, the density prime term log((1-u)/u) ≥ log 2 (since
(1-u)/u ≥ 2 ⟺ u ≤ 1/3), so 1 - log((1-u)/u) ≤ 1 - log 2, and integrating,
  ∫_a^{1/3} (1 - log((1-u)/u)) du ≤ (1/3 - a)(1 - log 2).
Because the semiprime term I(u) ≥ 0, the true density satisfies 1 - Φ ≤
1 - log((1-u)/u) here, so this bounds the c₂ integral's [α₂, 1/3] piece. Together
with the exact [1/3, 1/2] piece (`erdos858_c2_exact_integral_half`, #84, =
1/6 - (5/3)log 2 + log 3 ≈ 0.110) and α₂ > 0.26, this yields
  c₂ = 1/2 + ∫_{α₂}^{1/2}(1-Φ) ≤ 0.633,
completing the two-sided bracket **c₂ ∈ [0.610, 0.633]** around the true value.
Pure real analysis, no PNT.

Proof: `intervalIntegral.integral_mono_on` comparing the integrand to the constant
1 - log 2 from above (pointwise via `(1-u)/u ≥ 2` and `Real.log_le_log`), then
`rw [intervalIntegral.integral_const, smul_eq_mul] at hmono`. NOTE: with a variable
integration endpoint, the integrability hypothesis MUST carry an explicit measure
annotation (`ContinuousOn.intervalIntegrable` has an implicit `μ`); leaving it
implicit makes `IsLocallyFiniteMeasure` unresolvable.

Kernel-verified via the proofsearch MCP:
  episode a866c50b-544e-4b8c-bf1e-7e40073116b8,
  problem_version_id e673aff4-e344-4521-9028-2e0483fb9c7b.
Outcome: kernel_verified / root_kernel_verified (4th submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c91963f3f52c5179a9f47249b5a8b6de717a6ccd4decf4d7f9adec6b789f2f4c.
-/
import Mathlib

namespace Erdos858

/-- c₂ upper-bound piece: for `1/4 ≤ a ≤ 1/3`,
`∫_a^{1/3}(1 - log((1-u)/u)) du ≤ (1/3 - a)(1 - log 2)` (the prime term
`log((1-u)/u) ≥ log 2` on `[a,1/3]`). With the exact `[1/3,1/2]` piece (#84) and
`α₂ > 0.26` this gives `c₂ ≤ 0.633`, completing the bracket `c₂ ∈ [0.610, 0.633]`. -/
theorem erdos858_c2_upper_piece :
    ∀ a : ℝ, 1/4 ≤ a → a ≤ 1/3 →
      (∫ u in a..(1/3), (1 - Real.log ((1 - u) / u))) ≤ (1/3 - a) * (1 - Real.log 2) := by
  intro a ha1 ha2
  have hcont : ContinuousOn (fun u => 1 - Real.log ((1 - u) / u)) (Set.uIcc a (1/3)) := by
    rw [Set.uIcc_of_le ha2]
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.log
    · apply ContinuousOn.div₀
      · fun_prop
      · fun_prop
      · intro u hu; exact ne_of_gt (lt_of_lt_of_le (by norm_num) (le_trans ha1 hu.1))
    · intro u hu
      have hup : (0:ℝ) < u := lt_of_lt_of_le (by norm_num) (le_trans ha1 hu.1)
      have h1 : (0:ℝ) < 1 - u := by linarith [hu.2]
      exact ne_of_gt (div_pos h1 hup)
  have hgi : IntervalIntegrable (fun u => 1 - Real.log ((1 - u) / u)) MeasureTheory.volume a (1/3) := hcont.intervalIntegrable
  have hci : IntervalIntegrable (fun _ : ℝ => 1 - Real.log 2) MeasureTheory.volume a (1/3) := intervalIntegrable_const
  have hpoint : ∀ u ∈ Set.Icc a (1/3), 1 - Real.log ((1 - u) / u) ≤ 1 - Real.log 2 := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hup : (0:ℝ) < u := lt_of_lt_of_le (by norm_num) (le_trans ha1 hu1)
    have h2le : (2:ℝ) ≤ (1 - u) / u := by rw [le_div_iff₀ hup]; linarith [hu2]
    have hlog : Real.log 2 ≤ Real.log ((1 - u) / u) := Real.log_le_log (by norm_num) h2le
    linarith
  have hmono := intervalIntegral.integral_mono_on ha2 hgi hci hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  exact hmono

end Erdos858
