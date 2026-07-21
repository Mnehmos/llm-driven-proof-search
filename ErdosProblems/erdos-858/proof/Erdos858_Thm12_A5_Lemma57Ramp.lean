/-
Erdős Problem #858 — Theorem 1.2 assembly, atom A5 (Chojecki 2026).

`Lemma 5.7 (prime-only lower ramp), core`: on the low frontier the frontier sweep
`S_N` is strictly increasing, so every maximizing cutoff satisfies `K* ≥ N^{α−ε}`
(the K*-lower-bound localization). Given
  - the Prop 3.2 increment  `S_N(a) − S_N(a−1) = C_N(a) − 1/a`;
  - the prime-child lower bound  `C_N(a) ≥ P_N(a)/a`  (each prime `a<p≤N/a` gives
    the child `ap` contributing `1/(ap)`);
  - the interval-Mertens bound  `P_N(a) ≥ 1 + δ`  (holds for `a ≤ N^{α−ε}`, `α =
    1/(e+1)`, since `log((1−α)/α) = 1` because `(1−α)/α = e`),
we get
  `S_N(a) − S_N(a−1) = C_N(a) − 1/a ≥ P_N(a)/a − 1/a = (P_N(a)−1)/a ≥ δ/a > 0`.

Proof: `rw [increment]`; `(1+δ)/a ≤ P_N(a)/a ≤ C_N(a)` (`gcongr` on the div, `le_trans`);
`0 < (1+δ)/a − 1/a = δ/a` (`div_sub_div_same` + `div_pos`); `linarith`.

Kernel-verified via the proofsearch MCP:
  episode d81b9cbf-b6b0-4709-90bc-7ed076c866b0,
  problem_version_id 4b1dfd61-cd9d-4beb-94d2-daf29aa8eefb.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bd3c300524db57c07059d3df5f11e47f5a9d0becd42569fa24420793439b2a8e.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 atom A5 (Lemma 5.7 core): from the Prop 3.2 increment
`S_N(a)−S_N(a−1)=C_N(a)−1/a`, `C_N(a)≥P_N(a)/a`, and `P_N(a)≥1+δ`, the sweep
strictly increases: `0 < S_N(a)−S_N(a−1)`. The K*-lower-bound ramp. -/
theorem erdos858_thm12_lemma57_ramp :
    ∀ (SN CN PN : ℕ → ℝ) (a : ℕ) (δ : ℝ),
      0 < δ → 0 < (a:ℝ) →
      1 + δ ≤ PN a →
      PN a / (a:ℝ) ≤ CN a →
      SN a - SN (a-1) = CN a - 1/(a:ℝ) →
      0 < SN a - SN (a-1) := by
  intro SN CN PN a δ hδ ha hPN hCN hInc
  rw [hInc]
  have h1 : (1+δ)/(a:ℝ) ≤ CN a := le_trans (by gcongr) hCN
  have h2 : 0 < (1+δ)/(a:ℝ) - 1/(a:ℝ) := by rw [div_sub_div_same]; exact div_pos (by linarith) ha
  linarith [h1, h2]

end Erdos858
