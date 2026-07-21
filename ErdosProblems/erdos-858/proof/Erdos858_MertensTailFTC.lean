/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 3 (Chojecki 2026).

`FTC for the Mertens tail integral`: for `2 ≤ a ≤ b`,

  `∫_{a..b} t⁻¹/log²t dt  =  1/log a − 1/log b`.

The antiderivative is `−1/log t`, whose derivative `+t⁻¹/log²t` is the negation
of the derivative computed in #117 (`HasDerivAt.inv` on `Real.hasDerivAt_log`,
then `.neg`, normalized via `neg_div` + `neg_neg`).

This is the exact quantitative control of the remainder tail in the o(1)-Mertens
assembly: with `A(t) = log t + R(t)`, `|R| ≤ C` (the verified Mertens-1 stack),

  `|∫_{(a,b]} R(t)/(t log²t) dt| ≤ C·(1/log a − 1/log b) ≤ C/log a → 0`

along `a = N^s → ∞` — the entire o(1) of Mertens' second theorem in one bound.

Kernel-verified via the proofsearch MCP:
  episode d770e27b-7f86-41c8-ab6e-c671c1068e5e,
  problem_version_id d077d552-4112-4cd2-90ed-0b0a6f09c2b8.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash ca79be06688a72cea6ea4b1a485e90d73404baa72aafa08842f064b8ebdbd18c.

**Lean lesson**: `HasDerivAt.neg` on an `.inv` output gives `-((-t⁻¹)/L²)` —
the two negations are NOT adjacent (the outer neg wraps the whole division), so
normalize with `neg_div` BEFORE `neg_neg`. The combinators also produce
POINTFREE Pi-instance functions (`-Real.log⁻¹`) in displays; defeq handles them
against ascribed lambda forms.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 3 (tail FTC): for `2 ≤ a ≤ b`,
`∫_{a..b} t⁻¹/log²t = 1/log a − 1/log b` — the exact tail control behind the
o(1) in Mertens' second theorem. Antiderivative `−1/log t` via
`integral_eq_sub_of_hasDerivAt`. -/
theorem erdos858_mertens_tail_ftc :
    ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      ∫ t in a..b, t⁻¹ / Real.log t ^ 2 = (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  intro a b ha hab
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hmem : ∀ t ∈ Set.uIcc a b, 2 ≤ t := fun t ht => le_trans ha ((huIcc ▸ ht : t ∈ Set.Icc a b)).1
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun u : ℝ => -(Real.log u)⁻¹) (t⁻¹ / Real.log t ^ 2) t := fun t ht => by have hd := ((Real.hasDerivAt_log (ne_of_gt (by linarith [hmem t ht] : (0:ℝ) < t))).inv (ne_of_gt (Real.log_pos (by linarith [hmem t ht] : (1:ℝ) < t)))).neg; rwa [neg_div, neg_neg] at hd
  have hsubne : ∀ t ∈ Set.uIcc a b, t ∈ ({0}ᶜ : Set ℝ) := fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (by linarith [hmem t ht])
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.uIcc a b) := ContinuousOn.div (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (by linarith [hmem t ht] : (0:ℝ) < t))) (ContinuousOn.pow (Real.continuousOn_log.mono hsubne) 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [hmem t ht] : (1:ℝ) < t))))
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) MeasureTheory.volume a b := hcont.intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc]
  ring

end Erdos858
