/-
Erdős Problem #858 — Theorem 1.2 assembly, divide-bound helper (Chojecki 2026).

Generic divide-through helper: from `|A−W| ≤ ε·mass` and `L>0`, conclude
`|A/L − W/L| ≤ ε·(mass/L)`. Reusable algebraic bridge normalizing an
absolute-difference bound by a positive quantity (here, `log N`) — converts the A6
aggregation core's raw bound into the `log N`-normalized form A6-herr requires.

Proof: `A/L−W/L=(A−W)/L` (`ring`), `abs_div`+`abs_of_pos`, then
`ε·(mass/L)−|A−W|/L=(ε·mass−|A−W|)/L` (`ring`) is nonneg (`div_nonneg`), closed by
`linarith`. Pure algebra — avoids any uncertain `div_le_div_*` lemma name.

Kernel-verified via the proofsearch MCP:
  episode 9fba3980-92ce-4a2f-86dc-16d85dfd09ea,
  problem_version_id 1ea3487b-87c5-43a6-ac3b-c66b5e9f8980.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f5e985360942bb2c37769d97698b3ca40770d0184cb5fbc88ba618dc17de02af.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 divide-bound helper: `|A−W|≤ε·mass`, `L>0` ⟹ `|A/L−W/L|≤ε·(mass/L)`.
Pure algebra (`ring`+`div_nonneg`+`linarith`), no uncertain lemma names. -/
theorem erdos858_thm12_divide_bound :
    ∀ (A W mass L ε : ℝ), 0 < L → |A - W| ≤ ε * mass → |A/L - W/L| ≤ ε * (mass/L) := by
  intro A W mass L ε hL hb
  have heq : A/L - W/L = (A-W)/L := by ring
  rw [heq, abs_div, abs_of_pos hL]
  have hsub : ε*(mass/L) - |A-W|/L = (ε*mass-|A-W|)/L := by ring
  have hnn : (0:ℝ) ≤ (ε*mass-|A-W|)/L := div_nonneg (by linarith) hL.le
  linarith [hsub, hnn]

end Erdos858
