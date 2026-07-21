/-
Erdős Problem #858 — semiprime uniform Riemann-sum upgrade, ASSEMBLY STEP (a)
(Chojecki 2026).

**Combines atoms 2 (`erdos858_abel_log_ratio_weight_identity`), 3
(`erdos858_loglog_ibp_ratio_weight`), 4 (`erdos858_ratio_weight_change_of_variables`)**
into ONE capstone isolating EXACTLY the error term between the semiprime
Abel sum and the paper's target integral `∫g(v)/v dv`:

  `Σ_{k∈(⌊a⌋,⌊x⌋]} g(logk/logN)·cw(k) − ∫_{loga/logN}^{logx/logN} g(v)/v dv`
    `= g(logx/logN)·(C(x) − loglog x) − g(loga/logN)·(C(a) − loglog a)`
      `− ∫_{Ioc a x} gd(logt/logN)·(t⁻¹/logN)·C(t) dt`
      `+ ∫_{Ioc a x} gd(logt/logN)·(t⁻¹/logN)·loglog(t) dt`,

where `C(y) := Σ_{k≤⌊y⌋}cw(k)`. This reduces ALL remaining work toward the
literal uniform semiprime bound to a PURE BOUNDING exercise: once `C(t)` is
instantiated at the actual prime-reciprocal partial sum, `C(t) − loglog(t)` is
EXACTLY the quantity the corpus's EXISTING qualitative Mertens-2 capstone
already bounds (`|Σ_{p≤x}1/p − loglogx| ≤ [explicit K]`, no unknown constant)
— see the `erdos-858-campaign-state` memory PART 7 for the remaining steps
(explicit error bound, then specialization to the paper's actual
`G(u,v)=log((1−u−v)/v)`).

Design choice: the two error-integrals are kept as SEPARATE terms (not
combined into one integral of a difference `C(t)−loglog(t)`), avoiding any
need for `integral_sub`/extra integrability side conditions — once both
integrals are opaque real-valued atoms, the whole identity is pure
commutative-ring algebra, closed by `ring` after substituting atoms 2+3+4's
conclusions directly (no `linarith`-atom-matching bookkeeping needed, since
`ring` fully normalizes commutativity/distributivity, unlike `linarith`).

Kernel-verified via the proofsearch MCP:
  episode 88e36c96-dc74-4d99-b121-0cd84e01b56f,
  problem_version_id 454ded76-0737-4a83-b644-0a3721c3a2df.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 42eb88cfbd6c415c9378bb05b149d607bf2cf624bbf71666ead92974bed144de.
-/
import Mathlib

namespace Erdos858

/-- Assembly step (a): combines the Abel identity (atom 2), the loglog IBP
identity (atom 3), and the change-of-variables identity (atom 4) to isolate
exactly the error term `Σg·cw − ∫g/v dv = [boundary error] − ∫gd·C + ∫gd·loglog`. -/
theorem erdos858_deterministic_part_capstone :
    (∀ (cw : ℕ → ℝ) (g gd : ℝ → ℝ) (logN a x : ℝ),
      0 < logN → 0 < a → a ≤ x →
      (∀ v ∈ Set.Icc (Real.log a / logN) (Real.log x / logN), HasDerivAt g (gd v) v) →
      ContinuousOn gd (Set.Icc (Real.log a / logN) (Real.log x / logN)) →
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, g (Real.log (k:ℝ) / logN) * cw k
        = g (Real.log x / logN) * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, cw k)
          - g (Real.log a / logN) * (∑ k ∈ Finset.Icc 0 ⌊a⌋₊, cw k)
          - ∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cw k)) →
    (∀ (g gd : ℝ → ℝ) (logN a B : ℝ), 0 < logN → 2 ≤ a → a ≤ B →
      (∀ v ∈ Set.Icc (Real.log a / logN) (Real.log B / logN), HasDerivAt g (gd v) v) →
      ContinuousOn gd (Set.Icc (Real.log a / logN) (Real.log B / logN)) →
      (∫ t in a..B, Real.log (Real.log t) * (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)))
        = Real.log (Real.log B) * g (Real.log B / logN) - Real.log (Real.log a) * g (Real.log a / logN)
          - ∫ t in a..B, (1 / (t * Real.log t)) * g (Real.log t / logN)) →
    (∀ (g gd : ℝ → ℝ) (logN a B : ℝ), 0 < logN → 2 ≤ a → a ≤ B →
      (∀ v ∈ Set.Icc (Real.log a / logN) (Real.log B / logN), HasDerivAt g (gd v) v) →
      (∫ t in a..B, g (Real.log t / logN) / (t * Real.log t))
        = ∫ v in (Real.log a / logN)..(Real.log B / logN), g v / v) →
    ∀ (cw : ℕ → ℝ) (g gd : ℝ → ℝ) (logN a x : ℝ),
      0 < logN → 2 ≤ a → a ≤ x →
      (∀ v ∈ Set.Icc (Real.log a / logN) (Real.log x / logN), HasDerivAt g (gd v) v) →
      ContinuousOn gd (Set.Icc (Real.log a / logN) (Real.log x / logN)) →
      (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊x⌋₊, g (Real.log (k:ℝ) / logN) * cw k)
        - (∫ v in (Real.log a / logN)..(Real.log x / logN), g v / v)
        = g (Real.log x / logN) * ((∑ k ∈ Finset.Icc 0 ⌊x⌋₊, cw k) - Real.log (Real.log x))
          - g (Real.log a / logN) * ((∑ k ∈ Finset.Icc 0 ⌊a⌋₊, cw k) - Real.log (Real.log a))
          - (∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cw k))
          + (∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * Real.log (Real.log t)) := by
  intro habel hibp hcov cw g gd logN a x hlogN ha hax hgderiv hgdcont
  have hAbel := habel cw g gd logN a x hlogN (by linarith : (0:ℝ) < a) hax hgderiv hgdcont
  have hIBP := hibp g gd logN a x hlogN ha hax hgderiv hgdcont
  have hCOV := hcov g gd logN a x hlogN ha hax hgderiv
  have hbridge : (∫ t in a..x, (1 / (t * Real.log t)) * g (Real.log t / logN)) = ∫ t in a..x, g (Real.log t / logN) / (t * Real.log t) := intervalIntegral.integral_congr (fun t _ => by ring)
  rw [hbridge, hCOV] at hIBP
  have hswap : (∫ t in a..x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * Real.log (Real.log t)) = ∫ t in a..x, Real.log (Real.log t) * (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) := intervalIntegral.integral_congr (fun t _ => by ring)
  have hDET2 : (∫ t in a..x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * Real.log (Real.log t)) = Real.log (Real.log x) * g (Real.log x / logN) - Real.log (Real.log a) * g (Real.log a / logN) - ∫ v in (Real.log a / logN)..(Real.log x / logN), g v / v := by rw [hswap]; exact hIBP
  have hDET_set : (∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * Real.log (Real.log t)) = Real.log (Real.log x) * g (Real.log x / logN) - Real.log (Real.log a) * g (Real.log a / logN) - ∫ v in (Real.log a / logN)..(Real.log x / logN), g v / v := by
    rw [← intervalIntegral.integral_of_le hax]
    exact hDET2
  have hIntv : (∫ v in (Real.log a / logN)..(Real.log x / logN), g v / v) = Real.log (Real.log x) * g (Real.log x / logN) - Real.log (Real.log a) * g (Real.log a / logN) - ∫ t in Set.Ioc a x, (gd (Real.log t / logN) * ((t:ℝ)⁻¹ / logN)) * Real.log (Real.log t) := by linarith [hDET_set]
  rw [hAbel, hIntv]
  ring

end Erdos858
