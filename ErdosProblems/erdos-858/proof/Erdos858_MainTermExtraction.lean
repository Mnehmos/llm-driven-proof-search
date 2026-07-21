/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 10 (Chojecki 2026).

`main-term extraction from the interval Abel integral` (generic in `A`): given
the loglog FTC (#120, hypothesis), for any `A : ℝ → ℝ` whose Abel quotient
`A(t)/(t·log²t)` is integrable on `(a,b]` (`2 ≤ a ≤ b`),

  `∫_{(a,b]} A(t)/(t·log²t)
     = (loglog b − loglog a)  +  ∫_{(a,b]} (A(t) − log t)/(t·log²t)`.

Proof: pointwise `(A−log)/(t·log²t) = A/(t·log²t) − (log t)⁻¹·t⁻¹` on `(a,b]`
(field identity with `log t ≠ 0`, `t ≠ 0` — `field_simp` closes it outright),
`setIntegral_congr_fun` + `MeasureTheory.integral_sub` (main part integrable by
the #120 continuity chain), and #120 evaluates the main integral via
`intervalIntegral.integral_of_le`.

Chained with the interval Abel identity (#125) at `A` = the prime log-weight
sum and the dominated tail bound (#123) for the remainder (`|A − log| ≤ C`
from the Mertens-1 stack), this completes the DETERMINISTIC core of interval
Mertens: for all `2 ≤ m ≤ n`,

  `Σ_{m<p≤n} 1/p = [A(n)/log n − A(m)/log m] + (loglog n − loglog m) + E`,
  `|E| ≤ C·(1/log m − 1/log n)`.

The `N → ∞` limit at `m = ⌊N^s⌋`, `n = ⌊N^t⌋` then yields the §5.3 prime
block masses `Σ_{N^s<p≤N^t} 1/p → log(t/s)`.

Kernel-verified via the proofsearch MCP:
  episode 00622a74-82d6-46b9-b098-d02b0e30b2d5,
  problem_version_id c71a944b-f0b9-4bbb-8f41-d295d379aa3c.
Outcome: kernel_verified / root_kernel_verified (2nd submission — the trailing
`ring` after `field_simp` hit "no goals"; `field_simp` alone closes the per-t
identity, the recurring #89 lesson).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash fda61230088df0e69eeddfe7b26f5d4783239893559ee5f7b848246882666134.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 10 (main-term extraction, generic `A`): if the Abel
quotient is integrable on `(a,b]`, `∫ A/(t·log²t) = (loglog b − loglog a) +
∫ (A − log)/(t·log²t)`, via #120 (hypothesis). -/
theorem erdos858_main_term_extraction :
    (∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, (Real.log t)⁻¹ * t⁻¹ = Real.log (Real.log b) - Real.log (Real.log a)) →
      ∀ (A : ℝ → ℝ) (a b : ℝ), 2 ≤ a → a ≤ b →
        MeasureTheory.IntegrableOn (fun t : ℝ => A t / (t * Real.log t ^ 2)) (Set.Ioc a b) MeasureTheory.volume →
        ∫ t in Set.Ioc a b, A t / (t * Real.log t ^ 2)
          = (Real.log (Real.log b) - Real.log (Real.log a)) + ∫ t in Set.Ioc a b, (A t - Real.log t) / (t * Real.log t ^ 2) := by
  intro h120 A a b ha hab hAint
  have hmem : ∀ t ∈ Set.Icc a b, 2 ≤ t := fun t ht => le_trans ha ht.1
  have hsubne : ∀ t ∈ Set.Icc a b, t ∈ ({0}ᶜ : Set ℝ) := fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (by linarith [hmem t ht])
  have hcontM : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹ * t⁻¹) (Set.Icc a b) := ContinuousOn.mul (ContinuousOn.inv₀ (Real.continuousOn_log.mono hsubne) (fun t ht => ne_of_gt (Real.log_pos (by linarith [hmem t ht] : (1:ℝ) < t)))) (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (by linarith [hmem t ht] : (0:ℝ) < t)))
  have hMint : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.log t)⁻¹ * t⁻¹) (Set.Ioc a b) MeasureTheory.volume := hcontM.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsplit1 : (∫ t in Set.Ioc a b, (A t - Real.log t) / (t * Real.log t ^ 2)) = ∫ t in Set.Ioc a b, (A t / (t * Real.log t ^ 2) - (Real.log t)⁻¹ * t⁻¹) := MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by have h2t : (2:ℝ) ≤ t := le_trans ha (le_of_lt ht.1); have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith)); have htne : t ≠ 0 := ne_of_gt (by linarith); field_simp)
  have hsplit2 : (∫ t in Set.Ioc a b, (A t / (t * Real.log t ^ 2) - (Real.log t)⁻¹ * t⁻¹)) = (∫ t in Set.Ioc a b, A t / (t * Real.log t ^ 2)) - ∫ t in Set.Ioc a b, (Real.log t)⁻¹ * t⁻¹ := MeasureTheory.integral_sub hAint hMint
  have h4 : (∫ t in Set.Ioc a b, (Real.log t)⁻¹ * t⁻¹) = Real.log (Real.log b) - Real.log (Real.log a) := by rw [← intervalIntegral.integral_of_le hab]; exact h120 a b ha hab
  linarith [hsplit1, hsplit2, h4]

end Erdos858
