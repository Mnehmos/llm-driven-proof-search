/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 7 (Chojecki 2026).

`dominated tail bound`: given the tail FTC (#119, hypothesis), for any `g`
integrable on `(a,b]` with `|g(t)| ≤ C·t⁻¹/log²t` pointwise (`C ≥ 0`,
`2 ≤ a ≤ b`),

  `|∫_{(a,b]} g|  ≤  C·(1/log a − 1/log b)`.

Instantiated at `g(t) = R(t)/(t·log²t)` with `R = A − log` bounded by the
Mertens-1 stack (#47/#48), this is the ENTIRE o(1) of Mertens' second theorem:
the remainder contribution over `(N^s, N^t]` is `≤ C/(s·log N) → 0`.

Proof: `|∫ g| ≤ ∫ |g|` (`abs_integral_le_integral_abs`), set-integral
monotonicity against the dominating bound (`setIntegral_mono_on`, with the
bound's integrability from #119's continuity chain + `integrableOn_Icc` +
`mono_set` + `const_mul`), then the exact evaluation via
`integral_const_mul` + `intervalIntegral.integral_of_le` + #119.

Kernel-verified via the proofsearch MCP:
  episode 7d647fdf-e095-4598-bf7c-c8c6c24d1f48,
  problem_version_id e78c91da-6a79-4a3f-8891-28dd379671c0.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 96cbd6f711244856bf59380291403f73f9bdac5fce404b81d61c5a650feb4f8e.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 7 (dominated tail bound): `|g| ≤ C·t⁻¹/log²t` on
`(a,b]` (integrable `g`, `C ≥ 0`, `2 ≤ a ≤ b`) implies
`|∫_{(a,b]} g| ≤ C·(1/log a − 1/log b)`, via #119 (hypothesis). -/
theorem erdos858_dominated_tail_bound :
    (∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, t⁻¹ / Real.log t ^ 2 = (Real.log a)⁻¹ - (Real.log b)⁻¹) →
      ∀ (g : ℝ → ℝ) (C a b : ℝ), 0 ≤ C → 2 ≤ a → a ≤ b →
        MeasureTheory.IntegrableOn g (Set.Ioc a b) MeasureTheory.volume →
        (∀ t ∈ Set.Ioc a b, |g t| ≤ C * (t⁻¹ / Real.log t ^ 2)) →
        |∫ t in Set.Ioc a b, g t| ≤ C * ((Real.log a)⁻¹ - (Real.log b)⁻¹) := by
  intro h119 g C a b hC ha hab hgint hbound
  have hmem : ∀ t ∈ Set.Icc a b, 2 ≤ t := fun t ht => le_trans ha ht.1
  have hsubne : ∀ t ∈ Set.Icc a b, t ∈ ({0}ᶜ : Set ℝ) := fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (by linarith [hmem t ht])
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.Icc a b) := ContinuousOn.div (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (by linarith [hmem t ht] : (0:ℝ) < t))) (ContinuousOn.pow (Real.continuousOn_log.mono hsubne) 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [hmem t ht] : (1:ℝ) < t))))
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t⁻¹ / Real.log t ^ 2) (Set.Ioc a b) MeasureTheory.volume := hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hbint : MeasureTheory.IntegrableOn (fun t : ℝ => C * (t⁻¹ / Real.log t ^ 2)) (Set.Ioc a b) MeasureTheory.volume := hbase.const_mul C
  have habs : |∫ t in Set.Ioc a b, g t| ≤ ∫ t in Set.Ioc a b, |g t| := MeasureTheory.abs_integral_le_integral_abs
  have hmono : (∫ t in Set.Ioc a b, |g t|) ≤ ∫ t in Set.Ioc a b, C * (t⁻¹ / Real.log t ^ 2) := MeasureTheory.setIntegral_mono_on hgint.abs hbint measurableSet_Ioc hbound
  have heval : (∫ t in Set.Ioc a b, C * (t⁻¹ / Real.log t ^ 2)) = C * ((Real.log a)⁻¹ - (Real.log b)⁻¹) := by rw [MeasureTheory.integral_const_mul, ← intervalIntegral.integral_of_le hab, h119 a b ha hab]
  exact le_trans habs (le_trans hmono (le_of_eq heval))

end Erdos858
