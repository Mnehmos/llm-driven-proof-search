/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, atom 1 (Chojecki 2026).

`general-exponent block-membership bound` (#104 generalized): for `N` with
`1 < N` and ANY reals `v, w`, membership `a ∈ (⌊N^v⌋, ⌊N^w⌋]` forces

  `v < log a / log N ≤ w`

exactly, for every `N` — no asymptotics. The `j/K`-grid structure of #104 was
never load-bearing; the same floor sandwich (`Nat.lt_floor_add_one` /
`Nat.floor_le`) + log monotonicity + `log_rpow` argument works verbatim.

This serves the §5.3 prime-harmonic transfer's GEOMETRIC blocks
`v_j = s·(t/s)^{j/K}` (equispaced in `log v`, so each block's prime mass is the
constant `log(t/s)/K` by #129): membership in a block pins the prime's
log-coordinate `u_p = log p / log N` to `(v_j, v_{j+1}]`, which is what the
per-block oscillation control needs.

Kernel-verified via the proofsearch MCP:
  episode 395263b1-79e9-41b9-87d5-d6cab1677f29,
  problem_version_id 0f4a7fe1-2f86-49c4-b880-38ad3abe8b4c.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 446d31a3e26eac709a4c5ca918fa1ee2572dc1c722f8ff872027bf29d382cdbc.
-/
import Mathlib

namespace Erdos858

/-- §5.3 transfer atom 1 (general-exponent block membership): for `1 < N` and
any reals `v, w`, `a ∈ (⌊N^v⌋, ⌊N^w⌋]` forces `v < log a/log N ≤ w` exactly.
Subsumes #104; serves the geometric prime blocks of Lemma 5.3. -/
theorem erdos858_general_block_membership_bound :
    ∀ (N : ℕ) (v w : ℝ), 1 < (N:ℝ) → ∀ a : ℕ,
      a ∈ Finset.Ioc ⌊(N:ℝ)^v⌋₊ ⌊(N:ℝ)^w⌋₊ →
      v < Real.log (a:ℝ) / Real.log (N:ℝ) ∧ Real.log (a:ℝ) / Real.log (N:ℝ) ≤ w := by
  intro N v w hN a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Ioc.mp ha
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos hN
  have hNv_pos : (0:ℝ) < (N:ℝ) ^ v := Real.rpow_pos_of_pos hNpos _
  have hNw_pos : (0:ℝ) < (N:ℝ) ^ w := Real.rpow_pos_of_pos hNpos _
  have ha_pos : (0:ℕ) < a := by omega
  have ha_pos' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha_pos
  have h1nat : (⌊(N:ℝ) ^ v⌋₊ : ℕ) + 1 ≤ a := by omega
  have h1 : ((⌊(N:ℝ) ^ v⌋₊ : ℕ) : ℝ) + 1 ≤ (a:ℝ) := by exact_mod_cast h1nat
  have h2 : (N:ℝ) ^ v < ((⌊(N:ℝ) ^ v⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : (N:ℝ) ^ v < (a:ℝ) := by linarith
  have h3 : (a:ℝ) ≤ ((⌊(N:ℝ) ^ w⌋₊ : ℕ) : ℝ) := by exact_mod_cast ha2
  have h4 : ((⌊(N:ℝ) ^ w⌋₊ : ℕ) : ℝ) ≤ (N:ℝ) ^ w := Nat.floor_le (le_of_lt hNw_pos)
  have hle : (a:ℝ) ≤ (N:ℝ) ^ w := by linarith
  have hlog1 : v * Real.log (N:ℝ) < Real.log (a:ℝ) := by have hh := Real.log_lt_log hNv_pos hlt; rwa [Real.log_rpow hNpos] at hh
  have hlog2 : Real.log (a:ℝ) ≤ w * Real.log (N:ℝ) := by have hh := Real.log_le_log ha_pos' hle; rwa [Real.log_rpow hNpos] at hh
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hlogN]; linarith
  · rw [div_le_iff₀ hlogN]; linarith

end Erdos858
