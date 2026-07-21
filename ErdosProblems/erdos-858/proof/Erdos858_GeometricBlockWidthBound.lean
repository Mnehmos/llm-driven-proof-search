/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 5 (Chojecki 2026).

`geometric block width bound`: for `0 < s ≤ t`, `K > 0`, and `j < K`, the width
of the `j`-th geometric block is bounded by the mesh factor:

  `s·(t/s)^((j+1)/K) − s·(t/s)^(j/K)  ≤  t·((t/s)^(1/K) − 1)`.

Proof: `Real.rpow_add` splits `(t/s)^((j+1)/K) = (t/s)^(j/K)·(t/s)^(1/K)`,
factoring the width as `(s·(t/s)^(j/K))·((t/s)^(1/K) − 1)`; the left factor
`s·(t/s)^(j/K) ≤ t` (since `(t/s)^(j/K) ≤ (t/s)^1` with base `≥ 1` and exponent
`≤ 1`, then `s·(t/s) = t`), and the right factor `≥ 0` (base `≥ 1`, exponent
`≥ 0`). Combined with the mesh limit (#134), eventually in `K` every block width
is `≤ δ` — the refinement condition (`herr`) of the §5.3 prime-harmonic transfer.

Kernel-verified via the proofsearch MCP:
  episode bae83197-5d10-4b41-8fe8-accccbbc26d3,
  problem_version_id 7c1728a3-181d-4a4a-a19b-28ce746df2ef.
Outcome: kernel_verified / root_kernel_verified (3rd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 955508d2b8524fe87036bac6cf8945c5d3092a627636fbf3b55164177e074bff.

**Lean lessons**: (1) `positivity` cannot derive `0 < t/s` from `0 < s`, `s ≤ t`
alone — use `div_pos (by linarith) hs`. (2) `sub_nonneg.mpr (h : b ≤ a) : 0 ≤
a − b` — prefer this DIRECT term over `linarith` when the nonneg subterm's atom
was just introduced by a preceding `rw` (linarith's atom canonicalization can
miss the freshly-rewritten form).
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 5 (geometric block width bound): for `0 < s ≤ t`, `K > 0`,
`j < K`, `s·(t/s)^((j+1)/K) − s·(t/s)^(j/K) ≤ t·((t/s)^(1/K) − 1)`. With the mesh
limit (#134), eventually every block width is `≤ δ`. -/
theorem erdos858_geometric_block_width_bound :
    ∀ (s t : ℝ), 0 < s → s ≤ t → ∀ (K : ℕ), 0 < K → ∀ (j : ℕ), j < K →
      s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)) - s * (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ t * ((t/s) ^ ((1:ℝ)/(K:ℝ)) - 1) := by
  intro s t hs hst K hK j hjK
  have hbase : (0:ℝ) < t/s := div_pos (by linarith) hs
  have hts : (1:ℝ) ≤ t/s := (one_le_div hs).mpr hst
  have hKr : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hjle : (j:ℝ)/(K:ℝ) ≤ 1 := by rw [div_le_one hKr]; exact_mod_cast le_of_lt hjK
  have hexp : ((j:ℝ)+1)/(K:ℝ) = (j:ℝ)/(K:ℝ) + (1:ℝ)/(K:ℝ) := add_div _ _ _
  have hsplit : (t/s) ^ (((j:ℝ)+1)/(K:ℝ)) = (t/s) ^ ((j:ℝ)/(K:ℝ)) * (t/s) ^ ((1:ℝ)/(K:ℝ)) := by rw [hexp, Real.rpow_add hbase]
  have hfac0 : (t/s) ^ (0:ℝ) ≤ (t/s) ^ ((1:ℝ)/(K:ℝ)) := Real.rpow_le_rpow_of_exponent_le hts (by positivity)
  have hfac : (1:ℝ) ≤ (t/s) ^ ((1:ℝ)/(K:ℝ)) := by rwa [Real.rpow_zero] at hfac0
  have hvj0 : (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ (t/s) ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hts hjle
  have hvj : (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ t/s := by rwa [Real.rpow_one] at hvj0
  have h2 : s * (t / s) = t := by field_simp
  have h1 : s * (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ s * (t/s) := mul_le_mul_of_nonneg_left hvj hs.le
  have hvj' : s * (t/s) ^ ((j:ℝ)/(K:ℝ)) ≤ t := by linarith [h1, h2]
  have hkey : s * (t/s) ^ (((j:ℝ)+1)/(K:ℝ)) - s * (t/s) ^ ((j:ℝ)/(K:ℝ)) = (s * (t/s) ^ ((j:ℝ)/(K:ℝ))) * ((t/s) ^ ((1:ℝ)/(K:ℝ)) - 1) := by rw [hsplit]; ring
  rw [hkey]
  exact mul_le_mul_of_nonneg_right hvj' (sub_nonneg.mpr hfac)

end Erdos858
