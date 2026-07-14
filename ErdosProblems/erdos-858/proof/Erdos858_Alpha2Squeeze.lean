/-
Erdős Problem #858 — Proposition 5.6 corollary (Chojecki 2026, "An exact frontier
theorem and the asymptotic constant for Erdős problem #858").

α₂ localization SQUEEZE — a reusable order-theoretic tool for tightening the
critical exponent α₂ (and hence the constant c₂) from Φ-value brackets.

Φ is the limiting prime+semiprime density, strictly decreasing on [1/4, 1/3]
(kernel-verified monotonicity capstone, this campaign), and α₂ ∈ (1/4, 1/3) is its
unique root Φ(α₂) = 1 (kernel-verified existence/uniqueness). This atom packages
the immediate consequence: for ANY two points `lo, hi ∈ [1/4, 1/3]` whose Φ-values
bracket 1 (`Φ(lo) > 1 > Φ(hi)`), strict antitonicity forces `lo < α₂ < hi`.

Consequently every explicit numeric bound on Φ at a rational — obtainable from the
semiprime-integral bounds (`erdos858_I_upper_bound` and `..._semiprime_integral_nonneg`)
and the prime term (`erdos858_phi_prime_nonneg`) — instantly tightens the
localization of `α₂ = 0.28043830…`, and thereby of `c₂ = 1/2 + ∫_{α₂}^{1/2}(1−Φ)`.
Pure order theory on a strictly antitone function; no PNT.

Proof: each conjunct by contradiction. For `lo < α₂`, assume `α₂ ≤ lo`; if `α₂ = lo`
then `Φ(α₂) = 1` contradicts `Φ(lo) > 1`; if `α₂ < lo` then `StrictAntiOn` gives
`Φ(lo) < Φ(α₂) = 1`, again contradicting `Φ(lo) > 1`. Symmetric for `α₂ < hi`.

Kernel-verified via the proofsearch MCP:
  episode d568db48-96f4-4519-b93d-54783d9b271f,
  problem_version_id 1ec83066-8e8b-49c3-8741-9774fc2bb6c9.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash cffad010ce9fbfedffe863f01853a5acd5242708a70cdfd9d4be2240f45fd75d.
-/
import Mathlib

namespace Erdos858

/-- α₂ localization squeeze: if `Φ` is strictly antitone on `[1/4,1/3]` with unique
root `α₂` (`Φ α₂ = 1`), then any bracket `Φ lo > 1 > Φ hi` at points `lo, hi` in the
interval squeezes `lo < α₂ < hi`. The reusable tool turning numeric Φ-bounds into
tighter localizations of `α₂` (and hence `c₂`). -/
theorem erdos858_alpha2_squeeze :
    ∀ (Φ : ℝ → ℝ) (α₂ lo hi : ℝ),
      StrictAntiOn Φ (Set.Icc (1/4 : ℝ) (1/3)) →
      α₂ ∈ Set.Icc (1/4 : ℝ) (1/3) → Φ α₂ = 1 →
      lo ∈ Set.Icc (1/4 : ℝ) (1/3) → hi ∈ Set.Icc (1/4 : ℝ) (1/3) →
      1 < Φ lo → Φ hi < 1 →
      lo < α₂ ∧ α₂ < hi := by
  intro Φ α₂ lo hi hΦ hα₂mem hα₂eq hlomem himem hlo hhi
  constructor
  · by_contra h
    push_neg at h
    rcases eq_or_lt_of_le h with heq | hlt
    · subst heq; linarith
    · have hc := hΦ hα₂mem hlomem hlt
      rw [hα₂eq] at hc; linarith
  · by_contra h
    push_neg at h
    rcases eq_or_lt_of_le h with heq | hlt
    · subst heq; linarith
    · have hc := hΦ himem hα₂mem hlt
      rw [hα₂eq] at hc; linarith

end Erdos858
