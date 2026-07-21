/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 7 (Chojecki 2026).

`geometric grid properties bundle`: the geometric grid `v_j = s·(t/s)^{j/K}`
satisfies all the structural properties needed by the §5.3 aggregation (#136):
for `0 < s ≤ t`, `1 < N`, `K > 0`,

  (a) `v` monotone: `v j ≤ v (j+1)`;
  (b) `v 0 = s`;
  (c) `v K = t`;
  (d) the floor endpoint sequence `e_j = ⌊N^{v j}⌋` is monotone.

Proofs: (a)/(d) `Real.rpow_le_rpow_of_exponent_le` (base `≥ 1`, monotone
exponent) + `Nat.floor_mono`; (b) `rpow_zero` + `mul_one`; (c) `K/K = 1`,
`rpow_one`, `s·(t/s) = t`. Discharges the grid hypotheses of #136 at the
geometric instantiation, connecting the aggregation's symbolic endpoints to the
concrete `⌊N^s⌋`, `⌊N^t⌋`.

Kernel-verified via the proofsearch MCP:
  episode 06233ef3-7f56-4b74-848e-c11345a22e30,
  problem_version_id a6864070-34a7-444d-95ee-4475db94e6ad.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 1e5075622909d6abfc1b1d9beec41150b7e9a7d29b7caeb54643e61fefd82f86.

**Lean lesson**: `gcongr` on `↑a/↑c ≤ ↑b/↑c` (Nat casts, `c > 0`, `a ≤ b` in
context) CLOSES COMPLETELY — its discharger is cast-aware and finds the Nat
hypothesis; do NOT append `exact_mod_cast` (it hits "No goals").
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 7 (geometric grid bundle): the geometric grid
`v_j = s·(t/s)^{j/K}` is monotone with `v 0 = s`, `v K = t`, and floor-endpoint
monotone — the structural hypotheses of #136 at the geometric instantiation. -/
theorem erdos858_geometric_grid_properties :
    ∀ (s t : ℝ) (N K : ℕ), 0 < s → s ≤ t → 1 < (N:ℝ) → 0 < K →
      (∀ j : ℕ, s * (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)))
      ∧ s * (t/s) ^ (((0:ℕ):ℝ)/(K:ℝ)) = s
      ∧ s * (t/s) ^ (((K:ℕ):ℝ)/(K:ℝ)) = t
      ∧ Monotone (fun j : ℕ => ⌊(N:ℝ) ^ (s * (t/s) ^ ((j:ℝ)/(K:ℝ)))⌋₊) := by
  intro s t N K hs hst hN hK
  have hbase : (0:ℝ) < t/s := div_pos (by linarith) hs
  have hts : (1:ℝ) ≤ t/s := (one_le_div hs).mpr hst
  have hKr : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hinv : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun j => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hts (by rw [add_div]; linarith)) hs.le
  · simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
  · rw [div_self (ne_of_gt hKr), Real.rpow_one]; field_simp
  · exact fun a b hab => Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN) (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hts (by gcongr)) hs.le))

end Erdos858
