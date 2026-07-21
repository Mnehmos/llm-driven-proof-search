/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 4 (Chojecki 2026).

`FTC for the Mertens main integral`: for `2 ≤ a ≤ b`,

  `∫_{a..b} (log t)⁻¹·t⁻¹ dt  =  log(log b) − log(log a)`.

Antiderivative `log ∘ log` (`HasDerivAt.comp` of two `Real.hasDerivAt_log`
instances). This is the main term producing `loglog` in the o(1)-Mertens
assembly. On `(N^s, N^t]` it evaluates EXACTLY (for every `N` with `N^s ≥ 2`)
to `log(t·log N) − log(s·log N) = log t − log s` — the prime block mass value
of the §5.3 transfer, with no asymptotics needed at this step.

Kernel-verified via the proofsearch MCP:
  episode 24bdcc62-e2a4-4966-a788-58e5d9a9ff87,
  problem_version_id 06f172f1-9f56-45d0-b85c-646c47289ba6.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a1daa06c518a87810b518e4846a196b559d6038195e176cfe4c48e4ca7dcee82.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 4 (main FTC): for `2 ≤ a ≤ b`,
`∫_{a..b} (log t)⁻¹·t⁻¹ = loglog b − loglog a` — the loglog main term.
Antiderivative `log∘log` via `integral_eq_sub_of_hasDerivAt`. -/
theorem erdos858_mertens_main_ftc :
    ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (Real.log t)⁻¹ * t⁻¹ = Real.log (Real.log b) - Real.log (Real.log a) := by
  intro a b ha hab
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hmem : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans ha ((huIcc ▸ ht : t ∈ Set.Icc a b)).1
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => Real.log (Real.log u)) ((Real.log t)⁻¹ * t⁻¹) t := fun t ht => (Real.hasDerivAt_log (ne_of_gt (Real.log_pos (by linarith [hmem t ht] : (1:ℝ) < t)))).comp t (Real.hasDerivAt_log (ne_of_gt (by linarith [hmem t ht] : (0:ℝ) < t)))
  have hsubne : ∀ t ∈ Set.uIcc a b, t ∈ ({0}ᶜ : Set ℝ) := fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (by linarith [hmem t ht])
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹ * t⁻¹) (Set.uIcc a b) := ContinuousOn.mul (ContinuousOn.inv₀ (Real.continuousOn_log.mono hsubne) (fun t ht => ne_of_gt (Real.log_pos (by linarith [hmem t ht] : (1:ℝ) < t)))) (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (by linarith [hmem t ht] : (0:ℝ) < t)))
  have hint : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹ * t⁻¹) MeasureTheory.volume a b := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]

end Erdos858
