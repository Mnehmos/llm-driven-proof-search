/-
Erdős Problem #858 — Theorem 1.2 assembly, increment sign bridge (Chojecki 2026).

`frontier increment sign`: the sign of the sweep increment is governed by
`R_N(a)` vs `1`. Given the Prop 5.1 increment
  `S_N(a) − S_N(a−1) = (R_N(a) − 1)/a`   and   `0 < a`,
  - `R_N(a) > 1 ⟹ S_N(a−1) < S_N(a)`  (sweep increasing);
  - `R_N(a) < 1 ⟹ S_N(a) < S_N(a−1)`  (sweep decreasing).

This is the glue turning Lemma 5.5 (`R_N(a) → Φ(u)`) + Prop 5.6 (`Φ(u) > 1` for
`u < α₂`, `< 1` for `u > α₂`) into the monotonicity hypotheses of the K*
localization capstone (`erdos858_thm12_kstar_localization`), giving
`K*(N) = N^{α₂+o(1)}`.

Proof: `increment = (R_N−1)/a`, whose sign matches `R_N − 1` since `a > 0`
(`div_pos` / `div_neg_of_neg_of_pos`); `linarith`.

Kernel-verified via the proofsearch MCP:
  episode c1a6317c-dd7b-4dcc-ba1d-a7c8f0b514ce,
  problem_version_id a1d93b05-57eb-41a2-94fc-9000f0da6ade.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7a3a40e531ca6cdfd8f16d285e7d2b647c0fcad517aa6374dde405d5e04c0281.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 increment sign bridge: from the Prop 5.1 increment
`S_N(a)−S_N(a−1)=(R_N(a)−1)/a` (`a>0`), `R_N(a)>1 ⟹` sweep increasing and
`R_N(a)<1 ⟹` sweep decreasing — the glue between Lemma 5.5 / Prop 5.6 and the K*
localization. `div_pos`/`div_neg_of_neg_of_pos` + `linarith`. -/
theorem erdos858_thm12_increment_sign :
    ∀ (SN RN : ℕ → ℝ) (a : ℕ),
      0 < (a:ℝ) →
      SN a - SN (a-1) = (RN a - 1)/(a:ℝ) →
      (1 < RN a → SN (a-1) < SN a) ∧ (RN a < 1 → SN a < SN (a-1)) := by
  intro SN RN a ha hInc
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · have h : 0 < SN a - SN (a-1) := (by rw [hInc]; exact div_pos (by linarith) ha); linarith
  · have h : SN a - SN (a-1) < 0 := (by rw [hInc]; exact div_neg_of_neg_of_pos (by linarith) ha); linarith

end Erdos858
