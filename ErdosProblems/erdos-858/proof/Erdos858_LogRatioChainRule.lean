/-
Erdős Problem #858 — semiprime uniform Riemann-sum upgrade, atom 1 (Chojecki 2026).

**NEW STRATEGIC DIRECTION for the sole remaining research-grade wall of Theorem
1.2** (Lemma 5.3's semiprime block `Q_N(a) → I(u)`, upgraded to hold uniformly
in `u`, needed by row 5.5 / row 5.8's `tail(N)/log N → I` limit and by the K*
localization's decreasing half): rather than re-deriving Lemma 5.3's entire
mesh/diagonal-squeeze Riemann-sum discretization tree (`hW`/`hR`/`herr`, ~10
atoms) in explicit-rate form, Abel-sum the semiprime integrand `g` DIRECTLY
against the now-uniform prime-reciprocal partial sums via Mathlib's
`sum_mul_eq_sub_sub_integral_mul` — confirmed GENERIC in the smooth weight
function (not hardcoded to `f = 1/log t`, as `erdos858_abel_log_inverse_identity`
specialized it to). The unknown Meissel–Mertens constant `M` cancels via the
FTC (`∫f' = f(B) − f(a)` exactly) the same way it did for the prime-only
Mertens-1 chain this session — so no sharp Mertens constant is needed here
either, just like Lemma 5.3's original construction.

This atom is the CHAIN-RULE prerequisite: for `f(t) := g(log t / c)` (the
weight the Abel identity will need, where `c = log N` and `g` is the
semiprime integrand), derive `f`'s derivative from `g`'s. Composes
`Real.hasDerivAt_log.div_const` with a supplied `HasDerivAt g gv' (log t/c)`
via `HasDerivAt.comp` — the same composition pattern already used successfully
for the rpow-exponent derivative in Lemma 5.3's own construction (#147).

Kernel-verified via the proofsearch MCP:
  episode 1c439a29-14f2-41f6-9458-9341d3a6efb9,
  problem_version_id d3d29426-74cc-4d45-94fc-9ce3a2f3032a.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a78d27b2823fb6f3364432e783b3a9a171c9400e58a2b328392fb35a4de6a2e9.
-/
import Mathlib

namespace Erdos858

/-- Chain-rule derivative for `f(t) := g(log t / c)`, the weight the semiprime
uniform Abel-summation identity will need. `HasDerivAt.comp` of
`Real.hasDerivAt_log.div_const` with a supplied derivative of `g` at `log t/c`. -/
theorem erdos858_log_ratio_chain_rule :
    ∀ (g : ℝ → ℝ) (gv' t c : ℝ), 0 < t → c ≠ 0 →
      HasDerivAt g gv' (Real.log t / c) →
      HasDerivAt (fun u : ℝ => g (Real.log u / c)) (gv' * ((t:ℝ)⁻¹ / c)) t := by
  intro g gv' t c ht hc hg
  have hf : HasDerivAt (fun u : ℝ => Real.log u / c) ((t:ℝ)⁻¹ / c) t := (Real.hasDerivAt_log (ne_of_gt ht)).div_const c
  exact hg.comp t hf

end Erdos858
