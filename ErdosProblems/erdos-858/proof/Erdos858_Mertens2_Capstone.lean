/-
Erdős Problem #858 — §5, the CAPSTONE assembly: the qualitative Mertens' second
theorem Σ_{p≤x} 1/p = loglog x + O(1), stitched together from the campaign's four
kernel-verified §5 analytic atoms.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 exact-constant development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP pipeline.
  problem_version_id  b10ae9b8-b0f3-42ee-9437-00a328e6a11d
  episode_id          d039c543-ca4c-4974-8021-1a403e7c3082
  root_statement_hash e32f500b8b0391b326fbedeb8d8f507ee5a448da7336b462ebe7b807bdb179ec
  outcome             kernel_verified (root_proved)
  toolchain           leanprover/lean4:v4.32.0-rc1
  mathlib             360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

────────────────────────────────────────────────────────────────────────────────
CONTENT.  Mertens' second theorem for the prime-reciprocal sum,
    S(x) := Σ_{p≤x} 1/p = loglog x + O(1),   loglog x := log(log x),
governs the sharp asymptotic constant c₂ of Erdős #858.  This capstone assembles
the QUALITATIVE (explicit-O(1)) form directly at the point x, tying the abstract
Abel-summation bookkeeping to the concrete `L = log x` and to the concrete error
bound `(log 2)⁻¹` from the campaign's error-integral atom (#57).

The classical Abel/partial-summation derivation, with A(x) := Σ_{p≤x} (log p)/p:
    Σ_{p≤x} 1/p = A(x)/log x + ∫₂ˣ A(t)/(t log²t) dt
                = A(x)/log x + (loglog x − loglog 2) + K,     |K| = O(1),
and Mertens' first theorem A(x) = log x + O(1) gives
    A(x)/log x = 1 + (A(x) − log x)/log x.

The four kernel-verified §5 atoms enter as hypotheses (problem_versions cannot
cross-reference other verified atoms), specialized to L = log x with A applied as
`A x` and loglog written explicitly as `Real.log (Real.log ·)`:
  • Abel split #65:            S = A x / log x + (J + K);
  • main integral #56:        J = loglog x − loglog 2
                                = Real.log (Real.log x) − Real.log (Real.log 2);
  • error integral #57 bound: |K| ≤ (log 2)⁻¹;
  • Mertens-1:                |A x − log x| ≤ CA   (A(x) = log x + O(1)).
Given `log 2 ≤ log x` (i.e. x ≥ 2), the conclusion is the explicit two-sided
qualitative Mertens-2 bound
    |S − loglog x| ≤ |1 − loglog 2| + CA/log 2 + (log 2)⁻¹,
i.e. Σ_{p≤x} 1/p = loglog x + O(1) with an explicit O(1) constant.

This complements — and is the point-specialized companion of — the campaign's
abstract Abel-reduction atom `erdos858_mertens2_abel_reduction`, and the interval
version `erdos858_lemma52_interval_mertens`.

────────────────────────────────────────────────────────────────────────────────
TECHNIQUE.  Write L = log x (> 0 since log 2 ≤ L and log 2 > 0).
  • A x / L = 1 + (A x − L)/L                          (`sub_div`, `div_self`).
  • The normalized Mertens-1 error is bounded:
        |(A x − L)/L| ≤ CA/log 2
    proved by `abs_div` + `abs_of_pos` then the cross-multiplication
    `div_le_div_iff₀ (0<L) (0<log 2)` reducing to
    `|A x − L| · log 2 ≤ CA · L`, closed by `nlinarith` from `|A x − L| ≤ CA`,
    `log 2 ≤ L`, `0 < log 2`, `0 ≤ CA`, `0 ≤ |A x − L|`.
  • Rearranged identity:
        S − loglog x = (1 − loglog 2) + (A x − L)/L + K     (`rw` + `ring`).
  • Triangle bound: `abs_add` is NOT in this pin — instead `rw [abs_le]` on the
    two hypothesis bounds and on the goal, then `le_abs_self` / `neg_abs_le`
    supply the two directions for the `(1 − loglog 2)` term and `linarith`
    discharges each side of the `constructor`.

BLOCKER for the UNCONDITIONAL sharp result (leading constant exactly 1 / the
Meissel–Mertens constant M).  The pin has no `PrimeNumberTheorem` module, no
θ(x) = x + o(x), no Chebyshev lower bound, and no Mertens first/second theorem.
The two analytic inputs `A(x) = log x + O(1)` and `|K| ≤ (log 2)⁻¹` therefore
cannot be discharged unconditionally in-pin and are taken as hypotheses here;
this theorem proves exactly the bookkeeping that, given them, yields
Σ 1/p = loglog x + O(1).  (Divergence Σ 1/p → +∞ is separately reachable
unconditionally in `erdos858_prime_reciprocal_diverges`.)

Lean notes (this pin): `abs_add` is not an identifier — triangle inequality via
`abs_le` + `le_abs_self`/`neg_abs_le` + `linarith`. The cross-multiplication
lemma is `div_le_div_iff₀` (a/b ≤ c/d ↔ a·b' ...), not `div_le_div_iff`.
`positivity` proves `0 < Real.log 2` (numeric-literal extension), but a `gcongr`
on `CA/L ≤ CA/log 2` emits an undischargeable `0 ≤ CA` side goal for the free
variable CA, so cross-multiply + `nlinarith` is the robust route.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, Mertens' second theorem (qualitative capstone) — conditional
assembly at the point x.  With `S := Σ_{p≤x} 1/p`, `A x := Σ_{p≤x} (log p)/p`,
`loglog z := Real.log (Real.log z)`, and `log 2 ≤ log x` (i.e. x ≥ 2): given the
Abel split `S = A x / log x + (J + K)`, the evaluated main integral
`J = loglog x − loglog 2`, the error-integral bound `|K| ≤ (log 2)⁻¹`, and
Mertens' first theorem `|A x − log x| ≤ CA`, the prime-reciprocal sum satisfies
the explicit two-sided bound
`|S − loglog x| ≤ |1 − loglog 2| + CA / log 2 + (log 2)⁻¹`,
i.e. `Σ_{p≤x} 1/p = loglog x + O(1)`. -/
theorem erdos858_mertens2_capstone :
    ∀ (x : ℝ) (A : ℝ → ℝ) (S J K CA : ℝ),
      (2:ℝ) ≤ x →
      Real.log 2 ≤ Real.log x →
      S = A x / Real.log x + (J + K) →
      J = Real.log (Real.log x) - Real.log (Real.log 2) →
      |K| ≤ (Real.log 2)⁻¹ →
      |A x - Real.log x| ≤ CA →
      |S - Real.log (Real.log x)| ≤
        |1 - Real.log (Real.log 2)| + CA / Real.log 2 + (Real.log 2)⁻¹ := by
  intro x A S J K CA hx hlogx hS hJ hK hCA
  have hlog2_pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_pos : (0:ℝ) < Real.log x := lt_of_lt_of_le hlog2_pos hlogx
  have hlogx_ne : Real.log x ≠ 0 := ne_of_gt hlogx_pos
  have hCA_nonneg : (0:ℝ) ≤ CA := le_trans (abs_nonneg _) hCA
  have h1 : |(A x - Real.log x) / Real.log x| ≤ CA / Real.log 2 := by
    rw [abs_div, abs_of_pos hlogx_pos, div_le_div_iff₀ hlogx_pos hlog2_pos]
    nlinarith [hCA, hlogx, hlog2_pos, hCA_nonneg, abs_nonneg (A x - Real.log x)]
  have hAL : A x / Real.log x = 1 + (A x - Real.log x) / Real.log x := by
    rw [sub_div, div_self hlogx_ne]; ring
  have hexpr : S - Real.log (Real.log x)
      = (1 - Real.log (Real.log 2)) + (A x - Real.log x) / Real.log x + K := by
    rw [hS, hAL, hJ]; ring
  rw [abs_le] at h1 hK
  have hb1 := le_abs_self (1 - Real.log (Real.log 2))
  have hb2 := neg_abs_le (1 - Real.log (Real.log 2))
  rw [hexpr, abs_le]
  constructor
  · linarith [h1.1, h1.2, hK.1, hK.2, hb1, hb2]
  · linarith [h1.1, h1.2, hK.1, hK.2, hb1, hb2]

end Erdos858
