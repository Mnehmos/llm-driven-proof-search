/-
Erdős Problem #858 — semiprime uniform Riemann-sum upgrade, ASSEMBLY STEP (c)
(Chojecki 2026).

**THE FULL EXPLICIT BOUND**: combines the deterministic-part capstone
(`erdos858_deterministic_part_capstone`) and the generic error bound
(`erdos858_ratio_weight_error_bound`) with a boundary triangle inequality
(using bounds `|g|≤M` and `|C−loglog|≤K` at the two endpoints, the SAME `K`
the error bound uses throughout the range) into ONE fully explicit bound:

  `|Σ_{k∈(⌊a⌋,⌊x⌋]} g(logk/logN)·cw(k) − ∫_{loga/logN}^{logx/logN} g(v)/v dv|`
    `≤ 2·M·K + K · ∫_{Ioc a x} |gd(logt/logN)·(t⁻¹/logN)| dt`.

**This completes the ENTIRE "pure bounding" half of the semiprime-wall
assembly plan** (see the `erdos-858-campaign-state` memory PART 7): given
ANY bound `M` on the (differentiable) weight `g` at the range endpoints and
ANY UNIFORM bound `K` on how far the partial-sum `C` deviates from `loglog`,
the semiprime Abel sum is within an EXPLICIT, COMPUTABLE distance of the
paper's target integral `∫g(v)/v dv`. Remaining for the literal uniform
Lemma 5.3/5.5 result: (d) discharge `K` via the corpus's EXISTING qualitative
Mertens-2 capstone (`erdos858_mertens2_capstone`, applied pointwise — `K` is
already a FIXED constant independent of the range, since that capstone's
bound doesn't grow with `x`, so no NEW uniformity work is needed here, unlike
Lemma 5.3's original mesh-based route); (e) discharge `M` and specialize
`g,gd` to the paper's actual `G(u,v)=log((1−u−v)/v)` and its derivative.

Proof: `mul_le_mul` for the two boundary product bounds (`|g|≤M`,`|C−loglog|≤K`
⟹ `|g·(C−loglog)|≤M·K`), then `abs_le`+`linarith` for the final triangle-
inequality assembly — same technique `erdos858_mertens2_capstone` used
(`abs_add` is NOT in this pin). One implementation lesson: `rw [hDET, abs_le]
at *` already rewrites the GOAL too (`*` includes it) — a subsequent
standalone `rw [abs_le]` on the goal then finds nothing left to match
(`rewrite` failed, "no occurrence of |?m|≤?m'"); go straight to `constructor`.

Kernel-verified via the proofsearch MCP:
  episode 08431ff6-0194-438d-93c2-d8b21b5339c0,
  problem_version_id 2d97f098-d618-4a78-b3e0-0f59ad027516.
Outcome: kernel_verified / root_proved (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash e8a8e933f4044bfe64e56a64d0be032cf4244deac80eb05b8614563e5899a8ba.
-/
import Mathlib

namespace Erdos858

/-- THE FULL EXPLICIT BOUND: combines the deterministic-part capstone and the
generic error bound with a boundary triangle inequality into
`|Σg·cw − ∫g/v dv| ≤ 2MK + K·∫|gd|`, given `|g|≤M` and `|C−loglog|≤K` at the
endpoints (same `K` as the error-bound's uniform pointwise hypothesis). -/
theorem erdos858_ratio_weight_full_bound :
    ∀ (cw : ℕ → ℝ) (g gd : ℝ → ℝ) (logN a x K M : ℝ),
      0 ≤ K → 0 ≤ M →
      (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, g (Real.log (k:ℝ) / logN) * cw k) - (∫ v in (Real.log a / logN)..(Real.log x / logN), g v / v)
        = g (Real.log x / logN) * ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, cw k) - Real.log (Real.log x))
          - g (Real.log a / logN) * ((∑ k ∈ Finset.Icc 0 ⌊a⌋₊, cw k) - Real.log (Real.log a))
          - (∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cw k))
          + (∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * Real.log (Real.log t)) →
      |(∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cw k))
        - (∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * Real.log (Real.log t))|
        ≤ K * ∫ t in Set.Ioc a x, |gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)| →
      |g (Real.log x / logN)| ≤ M →
      |g (Real.log a / logN)| ≤ M →
      |(∑ k ∈ Finset.Icc 0 ⌊x⌋₊, cw k) - Real.log (Real.log x)| ≤ K →
      |(∑ k ∈ Finset.Icc 0 ⌊a⌋₊, cw k) - Real.log (Real.log a)| ≤ K →
      |(∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, g (Real.log (k:ℝ) / logN) * cw k) - (∫ v in (Real.log a / logN)..(Real.log x / logN), g v / v)|
        ≤ 2 * M * K + K * ∫ t in Set.Ioc a x, |gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)| := by
  intro cw g gd logN a x K M hK hM hDET hERR hMx hMa hKx hKa
  have h1 : |g (Real.log x / logN) * ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, cw k) - Real.log (Real.log x))| ≤ M * K := by
    rw [abs_mul]
    exact mul_le_mul hMx hKx (abs_nonneg _) hM
  have h2 : |g (Real.log a / logN) * ((∑ k ∈ Finset.Icc 0 ⌊a⌋₊, cw k) - Real.log (Real.log a))| ≤ M * K := by
    rw [abs_mul]
    exact mul_le_mul hMa hKa (abs_nonneg _) hM
  rw [hDET, abs_le] at *
  constructor
  · linarith [h1.1, h1.2, h2.1, h2.2, hERR.1, hERR.2]
  · linarith [h1.1, h1.2, h2.1, h2.2, hERR.1, hERR.2]

end Erdos858
