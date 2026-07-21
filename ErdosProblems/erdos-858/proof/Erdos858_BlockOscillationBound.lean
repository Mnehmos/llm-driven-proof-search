/-
Erdős Problem #858 — §5.4 log-harmonic transfer, concrete assembly atom 4 (Chojecki 2026).

`block oscillation bound from modulus of continuity`: for a function `f : ℝ→ℝ`
with a δ-ε modulus of continuity (`∀ x y, |x-y|≤δ → |f x - f y|≤ε`), a fixed
`K>0`, and `1/K≤δ`, if `u` satisfies `j/K < u ≤ (j+1)/K` — the exact
block-membership conclusion of #104 — then `|f u - f(j/K)| ≤ ε`.

This combines the exact (non-asymptotic) block-membership bound (#104) with a
modulus of continuity to produce the per-element oscillation bound that #105
(weighted pointwise-to-sum) needs as its hypothesis: instantiate `u = log a/log N`
(from #104 applied at `a` in block `j`) to get `|f(u_a) - f(j/K)| ≤ ε` for every
`a` in the block, completing the concrete instantiation chain toward the full
log-harmonic Riemann theorem.

Proof: `j/K<u≤(j+1)/K` and `1/K≤δ` give `|u-j/K|≤δ` (via `abs_le`, using the
algebraic identity `(j+1)/K = j/K + 1/K`, `add_div`, and `0<1/K`), then apply
the modulus hypothesis directly. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 3f5c7af8-f568-44f3-bd7c-f72779b94f13,
  problem_version_id de46c8a7-d7c5-4043-9270-9b45e38716bd.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c1686399b3239894091e36f9d02b4d7ed10684862bd0cd794cfbcb694247bc67.

**Lean lesson**: `linarith` treats division expressions like `j/K` and
`(j+1)/K` as OPAQUE atoms unless an explicit equation relates them — it cannot
infer `(a+b)/c = a/c + b/c` on its own (a field fact, not linear arithmetic).
When a goal mixes several distinct-looking division terms that are secretly
related, supply the connecting identity as a `have` first (`add_div (a b c:ℝ)
: (a+b)/c = a/c + b/c` confirmed available in this pin).
-/
import Mathlib

namespace Erdos858

/-- Concrete assembly atom 4 (block oscillation bound from modulus of
continuity): given a δ-ε modulus of continuity for `f` at scale `δ≥1/K`, the
exact block-membership bound `j/K<u≤(j+1)/K` (from #104) yields `|f u -
f(j/K)|≤ε`. Feeds directly into #105's per-element hypothesis. Proof: `abs_le`
+ `add_div` + the modulus hypothesis. -/
theorem erdos858_block_oscillation_bound :
    ∀ (f : ℝ → ℝ) (K j : ℕ) (δ ε : ℝ), 0 < K → (1:ℝ) / (K:ℝ) ≤ δ →
      (∀ x y : ℝ, |x - y| ≤ δ → |f x - f y| ≤ ε) →
      ∀ u : ℝ, (j:ℝ) / (K:ℝ) < u → u ≤ ((j:ℝ) + 1) / (K:ℝ) →
      |f u - f ((j:ℝ) / (K:ℝ))| ≤ ε := by
  intro f K j δ ε hK hKd hmod u hu1 hu2
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hinvpos : (0:ℝ) < 1 / (K:ℝ) := by positivity
  have hsplit : ((j:ℝ) + 1) / (K:ℝ) = (j:ℝ) / (K:ℝ) + 1 / (K:ℝ) := add_div (j:ℝ) 1 (K:ℝ)
  have hbound : |u - (j:ℝ) / (K:ℝ)| ≤ δ := by rw [abs_le]; refine ⟨by linarith, by linarith⟩
  exact hmod u ((j:ℝ) / (K:ℝ)) hbound

end Erdos858
