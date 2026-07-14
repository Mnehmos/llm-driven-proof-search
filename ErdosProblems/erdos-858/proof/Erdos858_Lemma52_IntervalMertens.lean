/-
Erdős Problem #858 — §5, toward the sharp asymptotic constant c₂: Lemma 5.2
(Mertens on intervals), in its reachable CONDITIONAL O(1) form.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 exact-constant development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP pipeline.
  problem_version_id  aba11349-6fff-4506-bb16-93f2cf6e68d5
  episode_id          97fa17c4-2dc0-4a16-a749-9a6a1e5fc3ad
  root_statement_hash 08617ee8ac9dbba77d365f65d5a07789005d459577707359da7bdbe747c95b76
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
  mathlib             360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

────────────────────────────────────────────────────────────────────────────────
CONTENT.  Write M(z) := Σ_{p≤z} 1/p for the Mertens prime-reciprocal sum, and
loglog z := log(log z).  The paper's Lemma 5.2 upgrades the endpoint Mertens'
second theorem (M(z) = loglog z + o(1)) to an INTERVAL estimate: for 2 ≤ x ≤ y,

    Σ_{x < p ≤ y} 1/p = M(y) − M(x) = loglog y − loglog x + o(1).

This snapshot records the reachable QUALITATIVE version with an explicit O(1)
constant.  Given the endpoint bounds at the two interval ends,
    |M(x) − loglog x| ≤ C   and   |M(y) − loglog y| ≤ C,
the interval sum M(y) − M(x) satisfies

    |(M(y) − M(x)) − (loglog y − loglog x)| ≤ 2·C.

Abstracted over the two Mertens values Mx, My (standing for M(x), M(y)) and the
reals loglog x, loglog y written as `Real.log (Real.log x)`,
`Real.log (Real.log y)`, the statement is a purely conditional real inequality.

────────────────────────────────────────────────────────────────────────────────
TECHNIQUE.  Pure triangle inequality.  The interval error splits as

    (My − Mx) − (Ly − Lx) = (My − Ly) − (Mx − Lx),

each parenthesized term bounded in absolute value by C, so the difference is
bounded by 2C.  `rw [abs_le]` turns each `|·| ≤ C` hypothesis and the goal into
the paired two-sided bounds `−C ≤ · ≤ C`; `constructor` splits the goal's two
sides and each is discharged by `linarith` from the four endpoint inequalities.
No `Real.log` lemma is needed — the loglog terms stay opaque reals.

Role in the constant program: Lemma 5.2 is the §5 device that carries the
endpoint Mertens-2 estimate (the campaign's verified atoms
`erdos858_mertens2_main_integral` / `_error_integral` / `_abel_split` chain,
which give M(z) = loglog z + O(1)) into sums over dyadic-type intervals used to
localize the constant c₂ = 1/2 + ∫_{α₂}^{1/2}(1 − Φ).  This atom is the clean
conditional stitching step; instantiating C from the endpoint bound turns the
two pointwise Mertens estimates into the interval bound §5 consumes.

Lean notes (this pin): `abs_add` is NOT in this pin — the triangle bound is
obtained via `abs_le` + `linarith` rather than an additive absolute-value lemma.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Lemma 5.2 (Mertens on intervals) — conditional O(1) form.
For reals `Mx`, `My` standing for the Mertens sums `M(x)`, `M(y)` and `C`, if the
endpoint Mertens' second estimate holds at both ends,
`|Mx − loglog x| ≤ C` and `|My − loglog y| ≤ C`, then the interval sum
`My − Mx` approximates `loglog y − loglog x` to within `2·C`:
`|(My − Mx) − (loglog y − loglog x)| ≤ 2·C`, with `loglog z = Real.log (Real.log z)`. -/
theorem erdos858_lemma52_interval_mertens :
    ∀ (C x y Mx My : ℝ), |Mx - Real.log (Real.log x)| ≤ C →
      |My - Real.log (Real.log y)| ≤ C →
      |(My - Mx) - (Real.log (Real.log y) - Real.log (Real.log x))| ≤ 2 * C := by
  intro C x y Mx My hx hy
  rw [abs_le] at hx hy ⊢
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

end Erdos858
