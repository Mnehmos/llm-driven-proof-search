/-
Erdős Problem #858 — Theorem 1.2 assembly, A6 pullback continuity (Chojecki 2026).

`affine pullback preserves continuity`: for `f` continuous on `[s,t]` with `s ≤ t`,
the pullback

  `g(x) = f(s + x·(t−s))·(t−s)`

is continuous on `[0,1]`. This is the continuity input needed to instantiate the
durable equispaced-Riemann-sum theorem (#97,
`erdos858_left_uniform_sum_tendsto_intervalIntegral`) at `g`, producing the A6-hR
hypothesis `(1/K)·Σ_{j<K} g(j/K) → ∫₀¹ g` — the interval log-harmonic transfer's
Riemann step. `∫₀¹ g = ∫_s^t f` by the affine change of variables (#165).

Proof: the affine map `x ↦ s + x(t−s)` is continuous
(`(continuous_const.add (continuous_id.mul continuous_const)).continuousOn`) and maps
`[0,1]` into `[s,t]` (`Set.MapsTo`, endpoints by `mul_nonneg`/`sub_nonneg` +
`nlinarith`), so `f ∘ affine` is `ContinuousOn [0,1]` (`ContinuousOn.comp`); multiply
by the constant `(t−s)` (`ContinuousOn.mul continuousOn_const`).

Kernel-verified via the proofsearch MCP:
  episode a66a53be-af9c-4226-839c-46666acabd15,
  problem_version_id a2af624b-c6ad-4b66-8882-866961128714.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 10edfde3784304a084960b47de3fa4728385bb52c95d8826455a9e676b60eedd.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 A6 pullback continuity: `f` continuous on `[s,t]` (`s ≤ t`) ⟹
`g(x) = f(s+x(t−s))·(t−s)` continuous on `[0,1]`. The continuity input for
instantiating the durable Riemann-sum engine #97 at the pullback `g`.
`ContinuousOn.comp` (affine `MapsTo [0,1]→[s,t]`) + `ContinuousOn.mul continuousOn_const`. -/
theorem erdos858_thm12_a6_pullback_continuity :
    ∀ (f : ℝ → ℝ) (s t : ℝ), s ≤ t → ContinuousOn f (Set.Icc s t) →
      ContinuousOn (fun x => f (s + x*(t-s)) * (t-s)) (Set.Icc (0:ℝ) 1) := by
  intro f s t hst hf
  have hts : (0:ℝ) ≤ t - s := by linarith
  have haff : ContinuousOn (fun x : ℝ => s + x*(t-s)) (Set.Icc (0:ℝ) 1) := (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
  have hmaps : Set.MapsTo (fun x : ℝ => s + x*(t-s)) (Set.Icc (0:ℝ) 1) (Set.Icc s t) := by intro x hx; exact Set.mem_Icc.mpr ⟨by nlinarith [mul_nonneg hx.1 hts], by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hts]⟩
  have hcomp : ContinuousOn (fun x => f (s + x*(t-s))) (Set.Icc (0:ℝ) 1) := hf.comp haff hmaps
  exact hcomp.mul continuousOn_const

end Erdos858
