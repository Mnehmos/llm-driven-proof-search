/-
Erdős Problem #858 — §5.3 prime-harmonic transfer, hmodfam discharge / FINAL (Chojecki 2026).

`§5.3 clamp modulus family` (hmodfam discharge, [s,t] analogue of #116): for `G`
continuous on `[s,t]` (`s ≤ t`), the clamped composition `G(max (min t x) s)`
satisfies the GLOBAL uniform-continuity modulus family

  `∀ ε>0, ∃ δ>0, ∀ x y : ℝ, |x−y| ≤ δ → |G(clamp x) − G(clamp y)| ≤ ε`

— exactly the `hmodfam` hypothesis of the §5.3 herr wrapper #145b, the SOLE
remaining external hypothesis of the §5.3 prime-harmonic transfer chain.

Since the clamp `max (min t ·) s` is the identity on `[s,t]` and every transfer
argument (`u_a = log a/log N`, `v_j = s·(t/s)^{j/K}`) lies in `[s,t]`, instantiating
the #141 capstone chain at `G ∘ clamp` recovers the transfer for `G`'s values: the
§5.3 prime-harmonic Riemann-sum theorem now applies to EVERY `G` continuous on
`[s,t]`, with NO external hypotheses left anywhere in the tree. This mirrors #116,
which discharged the analogous `hUC` for the §5.4 transfer (clamping to `[0,1]`).

Proof (verbatim transport of #116 with `1 → t`, `0 → s`, `zero_le_one → hst`):
Heine–Cantor on the compact `[s,t]`
(`isCompact_Icc.uniformContinuousOn_of_continuous`) at `ε/2` gives `δ`; return
`δ/4`; the clamp is 2-Lipschitz (min layer via `min_add_max` + `max_comm` +
`abs_max_sub_max_le_abs`, outer max layer via
`abs_max_sub_max_le_abs (min t x) (min t y) s` directly); clamped values lie in
`[s,t]` (`le_max_right`, `max_le (min_le_left t z) hst`). Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 1239cbef-a6a6-47a5-bcd6-773eddc2ce9f,
  problem_version_id 77706fc6-3ce5-4e21-a4e6-a4643cfcfe39.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 34b0ff1fdbb4f2a48cb86595bbff447c00969fe7d8cd6c439e48249510b63676.
-/
import Mathlib

namespace Erdos858

/-- §5.3 hmodfam discharge / FINAL (clamp modulus family on `[s,t]`): for `G`
continuous on `[s,t]`, the clamped `G(max (min t x) s)` has a global δ-ε modulus for
every ε — the `hmodfam` input of #145b, closing the last external hypothesis of the
§5.3 transfer chain. `[s,t]` analogue of #116. Proof: Heine–Cantor + the clamp's
2-Lipschitz bound. -/
theorem erdos858_prime_clamp_modulus :
    ∀ (G : ℝ → ℝ) (s t : ℝ), s ≤ t → ContinuousOn G (Set.Icc s t) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ →
        |G (max (min t x) s) - G (max (min t y) s)| ≤ ε := by
  intro G s t hst hG ε hε
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hG
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδpos, hδ⟩ := hUC (ε/2) (by linarith)
  refine ⟨δ/4, by positivity, fun x y hxy => ?_⟩
  have hmem : ∀ z : ℝ, max (min t z) s ∈ Set.Icc s t := fun z => Set.mem_Icc.mpr ⟨le_max_right _ _, max_le (min_le_left t z) hst⟩
  have e1 := min_add_max t x
  have e2 := min_add_max t y
  have c1 : max t x = max x t := max_comm t x
  have c2 : max t y = max y t := max_comm t y
  have hmaxb := abs_max_sub_max_le_abs x y t
  have hminid : min t x - min t y = (x - y) - (max x t - max y t) := by rw [c1] at e1; rw [c2] at e2; linarith
  have p1 := le_abs_self (x - y)
  have p2 := neg_abs_le (x - y)
  have p3 := le_abs_self (max x t - max y t)
  have p4 := neg_abs_le (max x t - max y t)
  have hminb : |min t x - min t y| ≤ 2 * |x - y| := by rw [hminid, abs_le]; exact ⟨by linarith, by linarith⟩
  have hclampb : |max (min t x) s - max (min t y) s| ≤ 2 * |x - y| := le_trans (abs_max_sub_max_le_abs (min t x) (min t y) s) hminb
  have hdist : dist (max (min t x) s) (max (min t y) s) < δ := by rw [Real.dist_eq]; linarith
  have hfd := hδ _ (hmem x) _ (hmem y) hdist
  rw [Real.dist_eq] at hfd
  linarith

end Erdos858
