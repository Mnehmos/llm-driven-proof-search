/-
Erdős Problem #858 — Theorem 1.2 asymptotic constant: the lower-bound half c₂ ≥ 1/2.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for Erdős
problem #858", Theorem 1.2 / §5.)

The paper defines the sharp constant

  c₂ = 1/2 + ∫_{α₂}^{1/2} (1 − Φ(u)) du,

where Φ(u) = log((1−u)/u) + I(u) and α₂ ∈ (1/4, 1/3) is the unique root of Φ = 1
(Proposition 5.6, kernel-verified in Erdos858_Prop56_Alpha2Unique). On [α₂, 1/2]
the function Φ is decreasing with Φ(α₂) = 1, so Φ(u) ≤ 1 throughout; hence the
integrand 1 − Φ(u) is pointwise ≥ 0, the defining integral is ≥ 0, and c₂ ≥ 1/2.
This snapshot is the c₂ ≥ 1/2 half of the constant in Theorem 1.2.

Conditional clean atom. The hypotheses abstract the two structural inputs the
companion snapshots supply for this Φ and this α₂:
  (i)  α₂ ≤ 1/2                              (α₂ ∈ (1/4,1/3) ⊂ [·, 1/2]);
  (ii) ∀ u ∈ [α₂, 1/2], Φ(u) ≤ 1            (Φ decreasing with Φ(α₂) = 1);
and, purely for faithfulness to the paper's integral setup, integrability of the
integrand on [α₂, 1/2]. Given (i) and (ii), the theorem discharges the entire
analytic content of the lower bound: nonnegativity of the interval integral of a
pointwise-nonnegative integrand.

Kernel-verified via the proofsearch MCP:
  episode bfc78b8d-e535-42d1-a378-222f83417b4b,
  problem_version_id 32b338fd-917f-408f-9931-5ca4777cef46.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f978e16b404433efb8b37268fb9f2d77471ab560095a3ef48c5ca9986c17f991.

Lean note (the mechanism the pin provides):
NONNEGATIVITY — `intervalIntegral.integral_nonneg`
(Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:1333):
  (hab : a ≤ b) (hf : ∀ u, u ∈ Set.Icc a b → 0 ≤ f u) : 0 ≤ ∫ u in a..b, f u ∂μ.
It requires NO `IntervalIntegrable` hypothesis and NO measure typeclass beyond a
bare `Measure ℝ` (it routes through `integral_nonneg_of_ae_restrict`, and a
non-integrable integrand integrates to 0, which is still ≥ 0). So the third
hypothesis of this atom is genuinely unused (bound as `_hint`). After
`apply intervalIntegral.integral_nonneg hab; intro u hu`, the goal is
`0 ≤ (fun u => 1 - Φ u) u`; a `show (0:ℝ) ≤ 1 - Φ u` beta-reduces the
lambda-applied integrand so `linarith [hle u hu]` closes it from `Φ u ≤ 1`. The
outer `linarith` lifts `0 ≤ ∫` to `1/2 ≤ 1/2 + ∫`.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2, lower-bound half of the asymptotic constant: `c₂ ≥ 1/2`. For any
real `α₂ ≤ 1/2` and any `Φ : ℝ → ℝ` with `Φ(u) ≤ 1` on `[α₂, 1/2]`, the defining
integral `∫_{α₂}^{1/2}(1 − Φ)` is nonnegative, hence
`1/2 ≤ 1/2 + ∫_{α₂}^{1/2}(1 − Φ) = c₂`. Integrability is taken as a hypothesis for
faithfulness to the paper's setup but is not needed by the proof: nonnegativity of
the interval integral follows from pointwise nonnegativity of the integrand alone
(`intervalIntegral.integral_nonneg`). -/
theorem erdos858_c2_lower_bound :
    ∀ (alpha2 : ℝ) (Phi : ℝ → ℝ),
      alpha2 ≤ 1 / 2 →
      (∀ u ∈ Set.Icc alpha2 (1 / 2 : ℝ), Phi u ≤ 1) →
      IntervalIntegrable (fun u => 1 - Phi u) MeasureTheory.volume alpha2 (1 / 2) →
      (1 : ℝ) / 2 ≤ 1 / 2 + ∫ u in alpha2..(1 / 2), (1 - Phi u) := by
  intro alpha2 Phi hab hle _hint
  have hnn : (0 : ℝ) ≤ ∫ u in alpha2..(1 / 2), (1 - Phi u) := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    show (0 : ℝ) ≤ 1 - Phi u
    linarith [hle u hu]
  linarith

end Erdos858
