/-
Erdős Problem #858 — §5.4 log-harmonic transfer, concrete assembly atom 3/3 (Chojecki 2026).

`weighted pointwise-to-sum error bound` (generic): for a finite set `s` of
naturals, functions `g,h : ℕ → ℝ` with `h ≥ 0` on `s`, a constant `c`, and
`ε ≥ 0`, if `g` is pointwise within `ε` of `c` on `s`, then the `h`-weighted sum
of `g` is within `ε·Σh` of `c·Σh`:
  `|Σ_{a∈s} g(a)·h(a) − c·Σ_{a∈s} h(a)|  ≤  ε·Σ_{a∈s} h(a)`.

This is the tool that turns the block-membership oscillation bound (#104 +
uniform continuity) into the per-block sum bound `|S j − w j·m j| ≤ ε·m j`
needed by the aggregation theorem (#101): instantiate with `g a = f(u_a)`,
`h a = 1/a`, `c = f(j/K)` over `s = block j`, giving `S j = Σ g·h`, `w j·m j =
c·Σh`. Together with #103 (partition identity) and #104 (block bound), this
completes the three concrete-assembly atoms needed to build the full concrete
log-harmonic transfer on top of the abstract engine (#98–#102).

Proof: `c·Σh = Σ(c·h)` (`Finset.mul_sum`), `Σg·h − Σc·h = Σ(g·h − c·h)`
(`Finset.sum_sub_distrib`, symm), then the Finset triangle inequality
(`Finset.abs_sum_le_sum_abs`) plus the pointwise bound `|g·h − c·h| = |g−c|·h ≤
ε·h` (via `abs_mul` + `abs_of_nonneg` + `mul_le_mul_of_nonneg_right`), summed
via `Finset.sum_le_sum`, then `Σε·h = ε·Σh`. Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 94e47a9e-b985-4ef5-ade3-d4ea33179aaa,
  problem_version_id 9a92bf72-7902-4220-b1f4-c82e5e98edbe.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 09fafcb67867358619e6cb70fa0f6309498243d4ebeaa21a5f5090e5ea6abf0c.

**Lean lesson (refines the #104 lesson, campaign-wide)**: `have X := by tacSeq`
swallows the ENTIRE subsequent single-line semicolon-chain into X's own tactic
block — flattening a nested `have` to a single line is necessary but NOT
sufficient if that `have` is itself embedded inside a LARGER semicolon chain
meant to continue past it (submission 1 here hit exactly this: `have heq := by
ring; rw [...]; exact ...` had `ring` close `heq` and then `rw`/`exact` tried
to run with "No goals to be solved", since everything after `by` was consumed
into `heq`'s own block). Robust fix for a small algebraic side-fact needed
mid-chain: use an inline `show T from by tac` TERM (not a `have`) as a direct
argument to `rw`/`exact`/etc — a complete term has no dangling tactic-block
boundary, so it cannot swallow subsequent tokens.
-/
import Mathlib

namespace Erdos858

/-- Concrete assembly atom 3/3 (weighted pointwise-to-sum error bound,
generic): if `g` is pointwise within `ε` of `c` on `s` and `h ≥ 0` on `s`, the
`h`-weighted sum of `g` is within `ε·Σh` of `c·Σh`. Instantiated with `g=f∘u`,
`h=1/a`, `c=f(j/K)`, this gives the per-block sum bound feeding the aggregation
theorem (#101). Proof: `mul_sum` + `sum_sub_distrib` + Finset triangle +
pointwise bound. -/
theorem erdos858_weighted_pointwise_sum_bound :
    ∀ (s : Finset ℕ) (g h : ℕ → ℝ) (c ε : ℝ),
      (∀ a ∈ s, |g a - c| ≤ ε) → (∀ a ∈ s, 0 ≤ h a) →
      |(∑ a ∈ s, g a * h a) - c * (∑ a ∈ s, h a)| ≤ ε * (∑ a ∈ s, h a) := by
  intro s g h c ε hg hh
  have h1 : c * (∑ a ∈ s, h a) = ∑ a ∈ s, c * h a := by rw [Finset.mul_sum]
  have h2 : (∑ a ∈ s, g a * h a) - ∑ a ∈ s, c * h a = ∑ a ∈ s, (g a * h a - c * h a) := (Finset.sum_sub_distrib (fun a => g a * h a) (fun a => c * h a)).symm
  have h4 : ∑ a ∈ s, |g a * h a - c * h a| ≤ ∑ a ∈ s, ε * h a := Finset.sum_le_sum (fun a ha => by rw [show g a * h a - c * h a = (g a - c) * h a from by ring, abs_mul, abs_of_nonneg (hh a ha)]; exact mul_le_mul_of_nonneg_right (hg a ha) (hh a ha))
  have h5 : |∑ a ∈ s, (g a * h a - c * h a)| ≤ ∑ a ∈ s, |g a * h a - c * h a| := Finset.abs_sum_le_sum_abs _ _
  have h6 : (∑ a ∈ s, ε * h a) = ε * ∑ a ∈ s, h a := by rw [Finset.mul_sum]
  rw [h1, h2]
  calc |∑ a ∈ s, (g a * h a - c * h a)| ≤ ∑ a ∈ s, |g a * h a - c * h a| := h5
    _ ≤ ∑ a ∈ s, ε * h a := h4
    _ = ε * ∑ a ∈ s, h a := h6

end Erdos858
