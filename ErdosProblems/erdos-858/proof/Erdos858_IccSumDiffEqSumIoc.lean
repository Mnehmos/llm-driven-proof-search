/-
Erdős Problem #858 — Theorem 1.2 assembly, raw Icc-sum telescoping bridge (Chojecki 2026).

Discovered while scoping the final A2 assembly: atom A2's `hSK` hypothesis
(`erdos858_hSK_general_cast_R`, `Erdos858_HSKGeneralCastR.lean`) uses the
RAW Icc-sum form `H(k):=Σ_{n∈Icc 1 k}1/n` for its "H" function — NOT
Mathlib's `harmonic`. So the pre-existing `erdos858_harmonic_diff_eq_sum_Ioc`
(`Erdos858_HarmonicDiffEqSumIoc.lean`, stated for `harmonic`) does not
directly match `hHdiff`'s needed shape. This atom proves the SAME content
in the Icc-sum representation instead:

  `H(n) - H(m) = Σ_{a∈Ioc m n} 1/a`, i.e. `Σ_{Icc1n}1/k - Σ_{Icc1m}1/k = Σ_{Ioc m n}1/a`.

Proof: convert `Icc 1 k = Ioc 0 k` via the standard bridge
(`ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega`, reused
throughout this campaign), then induct ENTIRELY in `Ioc 0 ·` form using
`Finset.sum_Ioc_succ_top` twice per step — mirroring
`erdos858_harmonic_diff_eq_sum_Ioc`'s successor step exactly, minus the
`harmonic`-cast complexity that atom needed.

Kernel-verified via the proofsearch MCP:
  episode 2206945c-fca0-4ca0-90a5-3207b5c58ddd,
  problem_version_id c0a71990-85fc-423b-96c5-4addd1bc865f.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 0a8445cb190d71f28755c5600ceb5d62ac55e13dc748292bc635006dd4031a75.
-/
import Mathlib

namespace Erdos858

/-- Raw Icc-sum telescoping bridge: `Σ_{Icc1n}1/k − Σ_{Icc1m}1/k = Σ_{Ioc m n}1/a`
for `m≤n`. The Icc-sum analogue of `erdos858_harmonic_diff_eq_sum_Ioc`,
matching the exact "H" form `erdos858_hSK_general_cast_R` uses — discharges
A2's `hHdiff` hypothesis directly (no `harmonic`-bridging needed). -/
theorem erdos858_icc_sum_diff_eq_sum_Ioc :
    ∀ m n : ℕ, m ≤ n → (∑ k ∈ Finset.Icc 1 n, (1:ℝ)/(k:ℝ)) - (∑ k ∈ Finset.Icc 1 m, (1:ℝ)/(k:ℝ)) = ∑ a ∈ Finset.Ioc m n, (1:ℝ)/(a:ℝ) := by
  intro m n hmn
  have key : ∀ m n : ℕ, m ≤ n → (∑ k ∈ Finset.Ioc 0 n, (1:ℝ)/(k:ℝ)) - (∑ k ∈ Finset.Ioc 0 m, (1:ℝ)/(k:ℝ)) = ∑ a ∈ Finset.Ioc m n, (1:ℝ)/(a:ℝ) := (by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have hsum1 := Finset.sum_Ioc_succ_top (Nat.zero_le n) (fun a => (1:ℝ)/(a:ℝ))
      have hsum2 := Finset.sum_Ioc_succ_top hmn (fun a => (1:ℝ)/(a:ℝ))
      rw [hsum1, hsum2]
      linarith [ih])
  have e1 : Finset.Icc 1 n = Finset.Ioc 0 n := (by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega)
  have e2 : Finset.Icc 1 m = Finset.Ioc 0 m := (by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega)
  rw [e1, e2]
  exact key m n hmn

end Erdos858
