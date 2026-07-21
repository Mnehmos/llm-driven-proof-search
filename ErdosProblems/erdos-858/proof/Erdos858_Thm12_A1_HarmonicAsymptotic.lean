/-
Erdős Problem #858 — Theorem 1.2 assembly, atom A1 (Chojecki 2026).

`harmonic main term`: the harmonic-number difference `H_N − H_{⌊√N⌋}` is
asymptotically `(1/2)·log N`:

  `(H_N − H_{Nat.sqrt N}) / log N  →  1/2`.

This is the leading term of the maximum `M(N)` in the exact frontier identity
(Prop 5.1): `M(N) = H_N − H_{⌊√N⌋} + Σ_{K*<a≤√N} (1 − P_N(a) − Q_N(a))/a`, whose
first summand contributes `(1/2) log N` and whose sum contributes
`(∫_{α₂}^{1/2}(1−Φ)) log N`, giving `M(N) = (c₂+o(1)) log N` with
`c₂ = 1/2 + ∫_{α₂}^{1/2}(1−Φ)`.

Conditional on (all standard / discharged elsewhere):
  h1 : `H_N − log N → γ`  (Euler–Mascheroni, Mathlib `tendsto_harmonic_sub_log`);
  h2 : `H_{⌊√N⌋} − log⌊√N⌋ → γ`  (h1 ∘ `Nat.sqrt`);
  h3 : `log⌊√N⌋ / log N → 1/2`  (= #91 at `x = 1/2`, since `Nat.sqrt N = ⌊N^{1/2}⌋`);
  hlog : `log N → ∞`.

Proof: split
  `(H_N − H_√N)/log N = (H_N − log N)/log N − (H_√N − log√N)/log N + (1 − log√N/log N)`.
The first two terms → 0 (`Tendsto.div_atTop`: bounded γ-limit over `log N → ∞`);
the third → `1 − 1/2 = 1/2` (h3). The pointwise identity holds for `log N ≠ 0`
(`N ≥ 2`, `field_simp` + `ring`), transported by `Tendsto.congr'`.

Kernel-verified via the proofsearch MCP:
  episode 9b5aee6e-b05c-4a3d-9f7e-3e5469a64e28,
  problem_version_id d093fc19-b495-4448-aebb-ff3c6abcf4cf.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 32d333f53fa830ac5654461f3958a66e4da931242f1b5d53dfdb5fc050451348.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 atom A1 (harmonic main term): `(H_N − H_{⌊√N⌋})/log N → 1/2` — the
leading term of `M(N) = S_N(K*)` in the Prop 5.1 frontier identity. Conditional on
the Euler–Mascheroni limits (`H_m − log m → γ`), `log√N/log N → 1/2`, `log N → ∞`.
Split into three terms + `Tendsto.div_atTop` + `congr'`. -/
theorem erdos858_thm12_harmonic_asymptotic :
    ∀ (γ : ℝ),
      Filter.Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log N) Filter.atTop (nhds γ) →
      Filter.Tendsto (fun N : ℕ => (harmonic (Nat.sqrt N) : ℝ) - Real.log (Nat.sqrt N)) Filter.atTop (nhds γ) →
      Filter.Tendsto (fun N : ℕ => Real.log (Nat.sqrt N) / Real.log N) Filter.atTop (nhds (1/2)) →
      Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop →
      Filter.Tendsto (fun N : ℕ => ((harmonic N : ℝ) - harmonic (Nat.sqrt N)) / Real.log N) Filter.atTop (nhds (1/2)) := by
  intro γ h1 h2 h3 hlog
  have hA : Filter.Tendsto (fun N : ℕ => ((harmonic N : ℝ) - Real.log N)/Real.log N) Filter.atTop (nhds 0) := h1.div_atTop hlog
  have hB : Filter.Tendsto (fun N : ℕ => ((harmonic (Nat.sqrt N) : ℝ) - Real.log (Nat.sqrt N))/Real.log N) Filter.atTop (nhds 0) := h2.div_atTop hlog
  have hC : Filter.Tendsto (fun N : ℕ => (1:ℝ) - Real.log (Nat.sqrt N)/Real.log N) Filter.atTop (nhds (1 - 1/2)) := tendsto_const_nhds.sub h3
  have hsum := (hA.sub hB).add hC
  have hval : (0 : ℝ) - 0 + (1 - 1/2) = 1/2 := by norm_num
  rw [hval] at hsum
  have heq : (fun N : ℕ => ((harmonic N : ℝ) - Real.log N)/Real.log N - ((harmonic (Nat.sqrt N) : ℝ) - Real.log (Nat.sqrt N))/Real.log N + ((1:ℝ) - Real.log (Nat.sqrt N)/Real.log N)) =ᶠ[Filter.atTop] (fun N : ℕ => ((harmonic N : ℝ) - harmonic (Nat.sqrt N))/Real.log N) := by filter_upwards [Filter.eventually_gt_atTop 1] with N hN; have hlogN : Real.log (N:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hN)); field_simp; ring
  exact hsum.congr' heq

end Erdos858
