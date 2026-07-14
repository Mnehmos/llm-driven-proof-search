/-
Erdős Problem #858 — §5.4 foundation (Chojecki 2026, "An exact frontier theorem
and the asymptotic constant for Erdős problem #858").

Floor block-endpoint limit `log⌊N^x⌋/log N → x` — the exact right endpoint of the
log-scale block up to `N^x`, for the §5.4 harmonic Riemann sum (toward Theorem 1.2).

Conditional on the rpow block-endpoint limit `log(N^x − 1)/log N → x`
(`erdos858_rpow_block_limit`, #89, taken as hypothesis since problem_versions
cannot cross-reference). The floor value satisfies `N^x − 1 < ⌊N^x⌋ ≤ N^x`, so
`log⌊N^x⌋/log N` is squeezed between `log(N^x − 1)/log N` (→ x by hypothesis) and
`log(N^x)/log N = x`; by the squeeze theorem the floor version → x. This gives the
exact integer block endpoints the §5.4 Riemann sum runs over. Elementary, no PNT.

Proof: `tendsto_of_tendsto_of_tendsto_of_le_of_le'` with the hypothesis (lower) and
`tendsto_const_nhds` (upper `x`); lower bound via `Nat.lt_floor_add_one` +
`Real.log_le_log` + `div_le_div_iff_of_pos_right`; upper via `Nat.floor_le` +
`div_le_iff₀` + `Real.log_le_log` + `Real.log_rpow`.

Kernel-verified via the proofsearch MCP:
  episode 655f04a1-933d-45a8-9c36-d7f0dacd2977,
  problem_version_id 1c285c29-283f-435e-8085-385573b2cb90.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash f47f308253fc71932b13d045c6d05ea72e5b06c2de7224fa1e616556b0086b6d.
-/
import Mathlib

namespace Erdos858

/-- Floor block-endpoint limit: for `x > 0`, given the rpow limit
`log(N^x − 1)/log N → x` (#89), the floor version `log⌊N^x⌋/log N → x` (squeeze,
since `N^x − 1 < ⌊N^x⌋ ≤ N^x`). The exact integer block endpoint for the §5.4
harmonic Riemann sum. Toward Theorem 1.2. -/
theorem erdos858_floor_block_limit :
    ∀ x : ℝ, 0 < x →
      Filter.Tendsto (fun N : ℕ => Real.log ((N:ℝ)^x - 1) / Real.log (N:ℝ)) Filter.atTop (nhds x) →
      Filter.Tendsto (fun N : ℕ => Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ)) Filter.atTop (nhds x) := by
  intro x hx hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    have hNxpos : (0:ℝ) < (N:ℝ)^x := Real.rpow_pos_of_pos hNpos x
    have hNxgt1 : (1:ℝ) < (N:ℝ)^x := (Real.one_lt_rpow_iff_of_pos hNpos).mpr (Or.inl ⟨hN1, hx⟩)
    have hlogpos : (0:ℝ) < Real.log (N:ℝ) := Real.log_pos hN1
    have hfloor_gt : (N:ℝ)^x - 1 < (⌊(N:ℝ)^x⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one ((N:ℝ)^x)
      linarith
    have hsub_pos : (0:ℝ) < (N:ℝ)^x - 1 := by linarith
    have hlog_le : Real.log ((N:ℝ)^x - 1) ≤ Real.log (⌊(N:ℝ)^x⌋₊ : ℝ) := Real.log_le_log hsub_pos hfloor_gt.le
    exact (div_le_div_iff_of_pos_right hlogpos).mpr hlog_le
  · filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    have hN1 : (1:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    have hNxpos : (0:ℝ) < (N:ℝ)^x := Real.rpow_pos_of_pos hNpos x
    have hNxge1 : (1:ℝ) ≤ (N:ℝ)^x := by
      have := (Real.one_lt_rpow_iff_of_pos hNpos).mpr (Or.inl ⟨hN1, hx⟩); linarith
    have hlogpos : (0:ℝ) < Real.log (N:ℝ) := Real.log_pos hN1
    have hfloor_le : (⌊(N:ℝ)^x⌋₊ : ℝ) ≤ (N:ℝ)^x := Nat.floor_le hNxpos.le
    have h1 : (1:ℕ) ≤ ⌊(N:ℝ)^x⌋₊ := Nat.le_floor (by exact_mod_cast hNxge1)
    have h0 : 0 < ⌊(N:ℝ)^x⌋₊ := by omega
    have hfloor_pos : (0:ℝ) < (⌊(N:ℝ)^x⌋₊ : ℝ) := by exact_mod_cast h0
    rw [div_le_iff₀ hlogpos]
    calc Real.log (⌊(N:ℝ)^x⌋₊ : ℝ) ≤ Real.log ((N:ℝ)^x) := Real.log_le_log hfloor_pos hfloor_le
      _ = x * Real.log (N:ℝ) := Real.log_rpow hNpos x

end Erdos858
