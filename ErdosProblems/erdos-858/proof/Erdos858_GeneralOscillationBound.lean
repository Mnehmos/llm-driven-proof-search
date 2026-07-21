/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 2 (Chojecki 2026).

`general oscillation bound` (subsumes #106): for `G : ℝ → ℝ` with a δ-ε modulus
of continuity, and reals `v ≤ w` with `w − v ≤ δ`, if `v < u ≤ w` then
`|G u − G v| ≤ ε`. Trivial: `|u − v| ≤ w − v ≤ δ`, then the modulus.

Serves the §5.3 prime-harmonic transfer's geometric blocks `(v_j, v_{j+1}]`,
whose width `w − v = v_{j+1} − v_j` is controlled by `K` (unlike the fixed
`1/K` width of #106, which this generalizes).

Kernel-verified via the proofsearch MCP:
  episode 328f8af5-a97a-41eb-b3a6-f693cc639a5b,
  problem_version_id d51e176c-c7b8-46e2-a139-3fd3e8ae7955.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4aa23a7251ade81953267ebd75db715f5e0aad3db771ccd57ed1dc0134c1df78.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 2 (general oscillation bound): a δ-ε modulus for `G`,
`v ≤ w`, `w − v ≤ δ`, and `v < u ≤ w` give `|G u − G v| ≤ ε`. Subsumes #106
for arbitrary block endpoints. -/
theorem erdos858_general_oscillation_bound :
    ∀ (G : ℝ → ℝ) (δ ε v w : ℝ),
      (∀ x y : ℝ, |x - y| ≤ δ → |G x - G y| ≤ ε) →
      v ≤ w → w - v ≤ δ →
      ∀ u : ℝ, v < u → u ≤ w → |G u - G v| ≤ ε := by
  intro G δ ε v w hmod hvw hwv u hvu huw
  have hbound : |u - v| ≤ δ := by rw [abs_le]; refine ⟨by linarith, by linarith⟩
  exact hmod u v hbound

end Erdos858
