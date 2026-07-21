/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 14 / discharge (Chojecki 2026).

`floor remainder pointwise bound`: if `|A(k) − log k| ≤ C` for all naturals
`k ≥ 2`, then for every real `u ≥ 2`,

  `|A(⌊u⌋) − log u|  ≤  C + log 2`.

Proof: split `A(⌊u⌋) − log u = (A(⌊u⌋) − log⌊u⌋) − (log u − log⌊u⌋)`; the
first term is bounded by `C`, and the second lies in `[0, log 2]` since
`⌊u⌋ ≤ u < ⌊u⌋ + 1 ≤ 2⌊u⌋` (using `⌊u⌋ ≥ 2`) with `log` monotone and
`log(2⌊u⌋) = log 2 + log⌊u⌋`.

This is the last discharge link of the §5.3 prime-mass stack: it converts the
Mertens-1 integer-argument bound into the pointwise hypothesis of the
dominated tail bound (#123) at the Abel remainder integrand, producing #129's
`hE` with `D = C + log 2`. With it, every hypothesis of the §5.3 capstone
(#129) is dischargeable end-to-end from kernel-verified atoms.

Kernel-verified via the proofsearch MCP:
  episode e8b9bd84-a384-42d6-a8f6-8f4bacb8c832,
  problem_version_id b8ad9433-b24f-4372-94d2-013c19b5fba1.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7a6baa38a663ebf3708849ac22d50a4983446fd5b367e743d4215efe23a81b6b.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens discharge (floor remainder bound): `|A(k) − log k| ≤ C` on
naturals `k ≥ 2` implies `|A(⌊u⌋) − log u| ≤ C + log 2` for reals `u ≥ 2` —
the floor sandwich `⌊u⌋ ≤ u < ⌊u⌋+1 ≤ 2⌊u⌋` costs exactly one `log 2`. -/
theorem erdos858_floor_remainder_bound :
    ∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
      (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
      |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2 := by
  intro A C u hu hA
  have hupos : (0:ℝ) < u := by linarith
  have hfloor2 : 2 ≤ ⌊u⌋₊ := Nat.le_floor (by exact_mod_cast hu)
  have hfr : (2:ℝ) ≤ ((⌊u⌋₊ : ℕ) : ℝ) := by exact_mod_cast hfloor2
  have hfle : ((⌊u⌋₊ : ℕ) : ℝ) ≤ u := Nat.floor_le (le_of_lt hupos)
  have hult : u < ((⌊u⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one u
  have h2f : u ≤ 2 * ((⌊u⌋₊ : ℕ) : ℝ) := by linarith
  have hlog2f := Real.log_le_log hupos h2f
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity : ((⌊u⌋₊ : ℕ) : ℝ) ≠ 0)] at hlog2f
  have hlogl : Real.log ((⌊u⌋₊ : ℕ) : ℝ) ≤ Real.log u := Real.log_le_log (by linarith) hfle
  have hA' := hA ⌊u⌋₊ hfloor2
  rw [abs_le] at hA'
  rw [abs_le]
  exact ⟨by linarith [hA'.1, hA'.2], by linarith [hA'.1, hA'.2]⟩

end Erdos858
