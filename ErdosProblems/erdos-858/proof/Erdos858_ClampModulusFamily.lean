/-
Erdős Problem #858 — §5.4 log-harmonic transfer, discharge atom 5 / FINAL (Chojecki 2026).

`clamp modulus family` (hUC discharge): for `f` continuous on `[0,1]`, the
clamped composition `g(x) = f (max (min 1 x) 0)` satisfies the GLOBAL
uniform-continuity modulus family

  `∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ, |x−y| ≤ δ → |g x − g y| ≤ ε`

— exactly the `hUC` shape needed by the eventual transfer error (#110), which
was the SOLE remaining external hypothesis of the §5.4 transfer chain. Since
the clamp is the identity on `[0,1]` and every transfer argument (`u_a`, `j/K`)
lies in `[0,1]`, instantiating the #111 chain at `g` recovers the transfer for
`f`'s values: the concrete log-harmonic Riemann theorem now applies to EVERY
`f ∈ C[0,1]`, with no external hypotheses left anywhere in the tree.

Proof: Heine–Cantor on the compact `[0,1]`
(`isCompact_Icc.uniformContinuousOn_of_continuous`, as in the durable #97) at
`ε/2` gives `δ`; return `δ/4` globally. The clamp is 2-Lipschitz: the min layer
via the identity `min 1 x − min 1 y = (x−y) − (max x 1 − max y 1)`
(`min_add_max` + `max_comm` + `linarith`) combined with
`abs_max_sub_max_le_abs`, and the outer max layer via
`abs_max_sub_max_le_abs (min 1 x) (min 1 y) 0` directly (writing the clamp as
`max (min 1 x) 0` matches the lemma's shared-second-argument shape with no
commutation). Clamped values lie in `[0,1]` (`le_max_right`, `max_le`,
`min_le_left`, `zero_le_one`). Elementary, no PNT.

Kernel-verified via the proofsearch MCP:
  episode 5ba2df9c-192d-41f7-adf2-67e467e913a2,
  problem_version_id 5dbc51cc-ea15-40bd-897c-92c292ee5225.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 40947ecbbd72303c809125c4a359d1ea637c9f42fdebc32469f0264ae58533ea.
-/
import Mathlib

namespace Erdos858

/-- Discharge atom 5 / FINAL (clamp modulus family, hUC): for `f` continuous on
`[0,1]`, the clamped `g x = f (max (min 1 x) 0)` has a global δ-ε modulus for
every ε — the `hUC` input of #110, closing the last external hypothesis of the
§5.4 transfer chain. Proof: Heine–Cantor + the clamp's 2-Lipschitz bound. -/
theorem erdos858_clamp_modulus_family :
    ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, |x - y| ≤ δ →
        |f (max (min 1 x) 0) - f (max (min 1 y) 0)| ≤ ε := by
  intro f hf ε hε
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδpos, hδ⟩ := hUC (ε/2) (by linarith)
  refine ⟨δ/4, by positivity, fun x y hxy => ?_⟩
  have hmem : ∀ z : ℝ, max (min 1 z) 0 ∈ Set.Icc (0:ℝ) 1 := fun z => Set.mem_Icc.mpr ⟨le_max_right _ _, max_le (min_le_left 1 z) zero_le_one⟩
  have e1 := min_add_max (1:ℝ) x
  have e2 := min_add_max (1:ℝ) y
  have c1 : max (1:ℝ) x = max x 1 := max_comm 1 x
  have c2 : max (1:ℝ) y = max y 1 := max_comm 1 y
  have hmaxb := abs_max_sub_max_le_abs x y (1:ℝ)
  have hminid : min (1:ℝ) x - min 1 y = (x - y) - (max x 1 - max y 1) := by rw [c1] at e1; rw [c2] at e2; linarith
  have p1 := le_abs_self (x - y)
  have p2 := neg_abs_le (x - y)
  have p3 := le_abs_self (max x 1 - max y 1)
  have p4 := neg_abs_le (max x 1 - max y 1)
  have hminb : |min (1:ℝ) x - min 1 y| ≤ 2 * |x - y| := by rw [hminid, abs_le]; exact ⟨by linarith, by linarith⟩
  have hclampb : |max (min 1 x) 0 - max (min 1 y) 0| ≤ 2 * |x - y| := le_trans (abs_max_sub_max_le_abs (min 1 x) (min 1 y) 0) hminb
  have hdist : dist (max (min 1 x) 0) (max (min 1 y) 0) < δ := by rw [Real.dist_eq]; linarith
  have hfd := hδ _ (hmem x) _ (hmem y) hdist
  rw [Real.dist_eq] at hfd
  linarith

end Erdos858
