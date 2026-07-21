/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, herr atom A (Chojecki 2026).

`geometric mesh vanishing`: from the geometric mesh limit (#134, `r^{1/K} → 1`),
for `0 < s ≤ t` and any `δ > 0`, eventually in `K` the mesh factor
`t·((t/s)^{1/K} − 1) ≤ δ`.

Combined with the geometric block width bound (#135, every block width
`v_{j+1} − v_j ≤ t·((t/s)^{1/K} − 1)`), this gives: eventually in `K`, ALL
geometric block widths fall below `δ` — the refinement condition that drives the
`herr` aggregation of the §5.3 prime-harmonic transfer (as `K → ∞` the grid
refines, the `G`-modulus at width `δ` shrinks, and the transfer error → 0).

Proof: `t·((t/s)^{1/K} − 1) → t·(1 − 1) = 0` via #134 + `Tendsto.sub_const 1` +
`Tendsto.const_mul t` (`simpa` clears `1 − 1` and `t·0`); then
`Tendsto.eventually_le_const hδ` (limit `0 < δ`) yields the eventual bound — the
same `eventually_le_const` device as the mass bound in #140.

Kernel-verified via the proofsearch MCP:
  episode 5d2e5230-4c5b-4404-8a8b-421388d7a167,
  problem_version_id 19adbe92-d837-4b7b-a57b-76bd109172b0.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bf891e95fee98f7550f16c3b5628c3f900601c1445031e0b63b7d25fde876adc.
-/
import Mathlib

namespace Erdos858

/-- §5.3 herr atom A (geometric mesh vanishing): from #134 (`r^{1/K} → 1`), for
`0 < s ≤ t` and any `δ > 0`, `∀ᶠ K, t·((t/s)^{1/K} − 1) ≤ δ`. With #135 (width ≤
this factor), eventually every block width is below `δ`. Proof: the factor → 0
(`sub_const` + `const_mul`), then `eventually_le_const`. -/
theorem erdos858_geometric_mesh_vanish :
    ∀ (s t : ℝ), 0 < s → s ≤ t →
      (∀ r : ℝ, 0 < r → Filter.Tendsto (fun K : ℕ => r ^ ((1:ℝ) / (K:ℝ))) Filter.atTop (nhds 1)) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ K : ℕ in Filter.atTop, t * ((t/s) ^ ((1:ℝ)/(K:ℝ)) - 1) ≤ δ := by
  intro s t hs hst h134 δ hδ
  have hbase : (0:ℝ) < t/s := div_pos (by linarith) hs
  have hsub : Filter.Tendsto (fun K : ℕ => (t/s) ^ ((1:ℝ)/(K:ℝ)) - 1) Filter.atTop (nhds 0) := by simpa using (h134 (t/s) hbase).sub_const 1
  have hmul : Filter.Tendsto (fun K : ℕ => t * ((t/s) ^ ((1:ℝ)/(K:ℝ)) - 1)) Filter.atTop (nhds 0) := by simpa using hsub.const_mul t
  exact hmul.eventually_le_const hδ

end Erdos858
