/-
Erdős Problem #858 — exponent window for the critical exponent α₂: the two strict
bounds 1/4 < α₂ < 1/3 read off from the Proposition 5.6 root membership.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for Erdős
problem #858", Proposition 5.6 / Theorem 1.2.)

Proposition 5.6 (kernel-verified as Erdos858_Prop56_Alpha2Unique, atom #61)
establishes that the limiting prime+semiprime density Φ(u) = log((1−u)/u) + I(u)
has a UNIQUE root α₂ of Φ = 1 lying in the open interval (1/4, 1/3):
    ∃! a, a ∈ Set.Ioo (1/4) (1/3) ∧ Φ a = 1.
This α₂ = 0.28043830… pins the frontier exponent K*(N) = N^{α₂ + o(1)} in Theorem
1.2 and enters the sharp constant c₂ = 1/2 + ∫_{α₂}^{1/2}(1 − Φ) = 0.6187712….

This atom is the trivial-but-faithful extraction that pins the exponent window:
from the `Set.Ioo (1/4) (1/3)` membership delivered by #61, it reads off the two
strict bounds `1/4 < α₂` and `α₂ < 1/3`. These are exactly the bounds consumed
downstream:
  • `α₂ < 1/3 < 1/2` feeds the nonnegative defining integral in the c₂ lower bound
    (Erdos858_C2LowerBound needs α₂ ≤ 1/2);
  • `1/4 < α₂` forces the localized integral `J = ∫_{α₂}^{1/2}(1 − Φ) < 1/4` in the
    two-sided bracket (Erdos858_C2Window needs `1/4 < α₂`), giving `c₂ < 3/4`.
Membership in a `Set.Ioo` unfolds definitionally to the conjunction of the two
strict inequalities, so no analytic content is involved — this is bookkeeping that
surfaces #61's interval as a usable exponent window.

Kernel-verified via the proofsearch MCP:
  episode 9cc97fb4-1679-4a2d-86e3-d6c524343bf2,
  problem_version_id e1fc26d4-bb1f-4670-9f24-397355665bd8.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c7747f2c6cc5582572a67b26deba24ab2678ff38e9894e047af8b29096ba2f0a.

Lean note: `Set.mem_Ioo` holds definitionally, so after `intro alpha2 h` the
membership `h : alpha2 ∈ Set.Ioo (1/4) (1/3)` has components `h.1 : 1/4 < alpha2`
and `h.2 : alpha2 < 1/3`; the goal `1/4 < alpha2 ∧ alpha2 < 1/3` is discharged by
the anonymous constructor `⟨h.1, h.2⟩`.
-/
import Mathlib

namespace Erdos858

/-- Exponent window for the critical exponent α₂. From the Proposition 5.6 (#61)
root membership `α₂ ∈ Ioo (1/4) (1/3)`, the two strict bounds `1/4 < α₂` and
`α₂ < 1/3` hold. These pin the frontier exponent window `K*(N) = N^{α₂+o(1)}` and
supply the inequalities the c₂ lower bound (`α₂ < 1/2`) and c₂ window
(`1/4 < α₂ ⇒ J < 1/4`) consume. Pure projection of `Set.Ioo` membership. -/
theorem erdos858_alpha2_window :
    ∀ (alpha2 : ℝ), alpha2 ∈ Set.Ioo (1/4 : ℝ) (1/3) →
      1/4 < alpha2 ∧ alpha2 < 1/3 := by
  intro alpha2 h
  exact ⟨h.1, h.2⟩

end Erdos858
