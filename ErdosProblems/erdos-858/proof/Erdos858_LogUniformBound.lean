/-
Erdős Problem #858 — toward UNIFORM interval Mertens, building block 2
(Chojecki 2026).

**Standalone log-perturbation bound**: if `R` is within `δ` of `x` (with
`x≥a>0` and `δ≤a/2`), then `Real.log R` is within `2δ/a` of `Real.log x`.
Pure real-analysis, no `N`/floor/`rpow` dependency — a general-purpose
"log is Lipschitz-ish away from 0, with an explicit uniform constant"
fact. This is the key ingredient for upgrading the campaign's per-fixed-x
`loglog` limits (`erdos858_loglog_floor_limit`) to genuinely uniform-in-x
bounds: applying it at `R := log⌊N^x⌋/logN` (already uniformly close to `x`
via `erdos858_uniform_floor_log_ratio`) bounds
`loglog⌊N^x⌋ − loglogN − logx = log R − log x` uniformly in `x`.

Proof: `log(x/R) ≤ x/R − 1` and `log(R/x) ≤ R/x − 1` (`Real.log_le_sub_one_of_pos`,
applied both ways to sandwich `logR−logx` from both sides), each converted via
`Real.log_div` into `logx−logR≤x/R−1` / `logR−logx≤R/x−1`; the RHS in each case
reduces to `(x−R)/R` / `(R−x)/x` (`div_sub_one`), bounded by `2δ/a` via
cross-multiplication (`div_le_div_iff₀`) + `nlinarith` on the chained facts
`|R−x|≤δ`, `a/2≤x−δ≤R`.

Kernel-verified via the proofsearch MCP:
  episode d353cc69-ef80-43bc-b670-2bbbc50470e8,
  problem_version_id ab7d0e75-7e22-41d0-9687-0710a2424aa8.
Outcome: kernel_verified / root_proved (2nd submission — 1st hit "Unknown
identifier `div_le_div_iff`"; this pin uses the GroupWithZero-generalized
`div_le_div_iff₀` naming convention instead, matching the previously-banked
`div_le_iff₀`/`div_lt_iff₀` pattern).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 208c227d9c3efcb46709ac3211f9a553fa5a8fd0b650b6dbbc45fce474ec77ba.
-/
import Mathlib

namespace Erdos858

/-- Log-perturbation bound: `|R-x|≤δ`, `x≥a>0`, `δ≤a/2` ⟹ `|logR-logx|≤2δ/a`.
Standalone real-analysis, the key ingredient for uniform-in-x loglog bounds.
Two applications of `log y≤y-1` (at `x/R` and `R/x`) sandwich `logR-logx`. -/
theorem erdos858_log_uniform_bound :
    ∀ (a δ R x : ℝ), 0 < a → a ≤ x → 0 ≤ δ → δ ≤ a/2 → |R - x| ≤ δ →
      |Real.log R - Real.log x| ≤ 2*δ/a := by
  intro a δ R x ha hax hδ0 hδa habs
  have hxpos : 0 < x := lt_of_lt_of_le ha hax
  obtain ⟨hRlo, hRhi⟩ := abs_le.mp habs
  have hxmhalf : a/2 ≤ x - δ := (by linarith)
  have hRpos : 0 < R := (by linarith)
  have hxmdpos : 0 < x - δ := (by linarith)
  rw [abs_le]
  constructor
  · have h1 : Real.log (x/R) ≤ x/R - 1 := Real.log_le_sub_one_of_pos (div_pos hxpos hRpos)
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hRpos)] at h1
    have h2 : x/R - 1 ≤ 2*δ/a := (by
      rw [div_sub_one (ne_of_gt hRpos), div_le_div_iff₀ hRpos ha]
      nlinarith [hRlo, hxmhalf, mul_le_mul_of_nonneg_right hxmhalf (by norm_num : (0:ℝ) ≤ 2)])
    linarith [h1, h2]
  · have h1 : Real.log (R/x) ≤ R/x - 1 := Real.log_le_sub_one_of_pos (div_pos hRpos hxpos)
    rw [Real.log_div (ne_of_gt hRpos) (ne_of_gt hxpos)] at h1
    have h2 : R/x - 1 ≤ 2*δ/a := (by
      rw [div_sub_one (ne_of_gt hxpos), div_le_div_iff₀ hxpos ha]
      nlinarith [hRhi])
    linarith [h1, h2]

end Erdos858
