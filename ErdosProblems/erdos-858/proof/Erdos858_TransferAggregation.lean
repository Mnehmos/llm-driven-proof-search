/-
Erdős Problem #858 — §5.4 log-harmonic transfer, rung 4 (Chojecki 2026).

`weighted approximation aggregation` (transfer error): for a fixed `K`, block sums
`S : ℕ → ℝ`, weights `w : ℕ → ℝ`, block masses `m : ℕ → ℝ` and a tolerance `ε`, if
each block satisfies the per-block bound `|S j − w j · m j| ≤ ε · m j`, then
  `|Σ_{j<K} S j − Σ_{j<K} w j · m j|  ≤  ε · Σ_{j<K} m j`.

In the transfer, `S j = Σ_{a in block j} f(u_a)/a` is the true partial sum over
block `j`, `w j = f(j/K)` the block weight, and `m j =` the log-scale block mass;
the per-block hypothesis is the uniform-continuity estimate
`|Σ_{a in block j} (f(u_a) − f(j/K))/a| ≤ ε · (block mass)`. Aggregating gives the
global error between the true normalized sum and the weighted step-sum, bounded by
`ε · (total mass)` — the analytic heart of the transfer (the harmonic analogue of
the block-variation ⟹ fixed-K error step #96 in the pure Riemann-sum theorem).

Proof: rewrite the difference of sums as a single sum (`Finset.sum_sub_distrib`,
applied as an explicit term), then `|Σ (S−wm)| ≤ Σ|S−wm| ≤ Σ ε·m = ε·Σm` via the
Finset triangle inequality (`Finset.abs_sum_le_sum_abs`), monotonicity
(`Finset.sum_le_sum`), and `Finset.mul_sum`. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 0603e58f-3bcc-4e3a-ae25-2c2b015c7829,
  problem_version_id 9cbfdb3b-177a-4dac-a112-01b8225332ca.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7cebca510ea59fcfdb61cb93796ade655bbe365c759b5ff841d4f3a2197c8599.
-/
import Mathlib

namespace Erdos858

/-- Log-harmonic transfer rung 4 (weighted approximation aggregation / transfer
error): per-block bounds `|S j − w j · m j| ≤ ε · m j` aggregate to
`|Σ_{j<K} S j − Σ_{j<K} w j · m j| ≤ ε · Σ_{j<K} m j`. The analytic heart of the
transfer — the harmonic analogue of the block-variation ⟹ fixed-K error step (#96).
Proof: `Finset.sum_sub_distrib` + Finset triangle inequality + `mul_sum`. -/
theorem erdos858_transfer_aggregation :
    ∀ (K : ℕ) (S w m : ℕ → ℝ) (ε : ℝ),
      (∀ j ∈ Finset.range K, |S j - w j * m j| ≤ ε * m j) →
      |(∑ j ∈ Finset.range K, S j) - (∑ j ∈ Finset.range K, w j * m j)| ≤ ε * (∑ j ∈ Finset.range K, m j) := by
  intro K S w m ε hbound
  have h1 : (∑ j ∈ Finset.range K, S j) - ∑ j ∈ Finset.range K, w j * m j = ∑ j ∈ Finset.range K, (S j - w j * m j) := (Finset.sum_sub_distrib S (fun j => w j * m j)).symm
  rw [h1]
  calc |∑ j ∈ Finset.range K, (S j - w j * m j)| ≤ ∑ j ∈ Finset.range K, |S j - w j * m j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range K, ε * m j := Finset.sum_le_sum hbound
    _ = ε * ∑ j ∈ Finset.range K, m j := by simp only [Finset.mul_sum]

end Erdos858
