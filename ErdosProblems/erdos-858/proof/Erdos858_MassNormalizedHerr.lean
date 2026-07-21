/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 10 (Chojecki 2026).

`mass-normalized diagonal error → herr` (generic): given a total-mass sequence
`mass N → L ≥ 0` and a fine-scale aggregation bound (for every oscillation
`η > 0`, eventually in `K` the block-error `|A N − W K N| ≤ η·mass N` for all
`N`), conclude the `herr` hypothesis of the diagonal squeeze: for every `ε > 0`,
eventually in `K`, eventually in `N`, `|A N − W K N| ≤ ε`.

Proof: set `M = L + 1 > 0`, choose `η = ε/M`, get eventually-`K` fineness from
the aggregation, and `mass N ≤ M` eventually (from `mass → L < M`); then
`|A N − W K N| ≤ (ε/M)·mass N ≤ (ε/M)·M = ε` (`div_mul_cancel₀`).

This is the `herr` input for the §5.3 prime-harmonic transfer's #102 capstone —
the abstract packaging of the aggregation (#136), the mesh limit (#134/#135),
and the total-mass bound (#129) into #102's exact `herr` shape.

Kernel-verified via the proofsearch MCP:
  episode 83570b0d-3d27-4def-87b5-1bdad5d00770,
  problem_version_id 823c14ac-6c66-48c7-b1e6-b36415cb0967.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash b9391a8d8fb17f2a7a3aa38055e5be2d1bb60e4f64b4629cc3dfff6b55245e75.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 10 (mass-normalized diagonal error → herr, generic in
`A,W,mass,L`): `mass → L ≥ 0` and the fine-scale aggregation bound
(`∀ η>0, ∀ᶠ K, ∀ N, |A N − W K N| ≤ η·mass N`) give the `herr` shape
`∀ ε>0, ∀ᶠ K, ∀ᶠ N, |A N − W K N| ≤ ε`. The `ε/M` diagonal argument. -/
theorem erdos858_mass_normalized_herr :
    ∀ (A : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (mass : ℕ → ℝ) (L : ℝ),
      0 ≤ L →
      Filter.Tendsto mass Filter.atTop (nhds L) →
      (∀ η : ℝ, 0 < η → ∀ᶠ K in Filter.atTop, ∀ N : ℕ, |A N - W K N| ≤ η * mass N) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ K in Filter.atTop, ∀ᶠ N in Filter.atTop, |A N - W K N| ≤ ε := by
  intro A W mass L hL0 hmass hAgg ε hε
  have hMpos : (0:ℝ) < L + 1 := by linarith
  have hηpos : (0:ℝ) < ε / (L + 1) := div_pos hε hMpos
  have hKfine := hAgg (ε / (L + 1)) hηpos
  have hmassle : ∀ᶠ N in Filter.atTop, mass N ≤ L + 1 := hmass.eventually_le_const (by linarith : L < L + 1)
  filter_upwards [hKfine] with K hK
  filter_upwards [hmassle] with N hNmass
  calc |A N - W K N| ≤ (ε / (L + 1)) * mass N := hK N
    _ ≤ (ε / (L + 1)) * (L + 1) := mul_le_mul_of_nonneg_left hNmass hηpos.le
    _ = ε := div_mul_cancel₀ ε hMpos.ne'

end Erdos858
