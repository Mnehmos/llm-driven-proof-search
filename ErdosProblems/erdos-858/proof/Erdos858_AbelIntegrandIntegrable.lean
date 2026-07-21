/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 8 (Chojecki 2026).

`integrability of the cumulative-weight Abel integrand` (generic): for a
NONNEGATIVE arithmetic weight `c : ℕ → ℝ` and `2 ≤ a ≤ b`, the Abel integrand

  `t ↦ C(t)/(t·log²t)`,   `C(t) = Σ_{k≤⌊t⌋} c(k)`,

is integrable on `(a,b]`. Route (`Integrable.mono'`): the step function
`C ∘ ⌊·⌋` is measurable (`measurable_from_top` composed with
`Nat.measurable_floor` — with EXPLICIT `(g :=)(f :=)` named arguments, since
higher-order unification otherwise decomposes the `Finset.sum` incorrectly);
the denominator is measurable (`measurable_id.mul (Real.measurable_log.pow_const 2)`);
and the integrand is dominated by `C(b)·(t·log²t)⁻¹` (cumulative-sum
monotonicity via `Finset.sum_le_sum_of_subset_of_nonneg` + `Nat.floor_le_floor`,
and `a/b = a·b⁻¹` definitionally closes the shape), which is integrable by
continuity. Supplies the integrability hypotheses of the Ioc additivity (#122)
and the dominated tail bound (#123) at the Mertens weight `c = [prime]·log k/k`.

Kernel-verified via the proofsearch MCP:
  episode d54c5874-3eaf-4251-862b-bf6d09fad7ac,
  problem_version_id 97b368d7-4768-4020-8d57-45b2edd24dfd.
Outcome: kernel_verified / root_kernel_verified (3rd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7f6f322b93568ac3fb92946fe5f757f36ba0ddf350f4b97ef7651fc4cd6e7799.

**Lean lessons**: (1) `Measurable.comp` with a `Finset.sum` outer function
needs explicit `(g :=)(f :=)` named arguments — HO-unification otherwise picks
a `Multiset.map` decomposition; (2) mid-chain inline tactic proofs must be
PARENTHESIZED `(by tac)` — a bare `:= by tac;` swallows the rest of the
semicolon chain even when `tac` is a single tactic.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 8 (Abel-integrand integrability, generic `c ≥ 0`):
`C(t)/(t·log²t)` with `C(t) = Σ_{k≤⌊t⌋} c(k)` is integrable on `(a,b]` for
`2 ≤ a ≤ b`. Dominated by `C(b)·(t·log²t)⁻¹` via `Integrable.mono'`. -/
theorem erdos858_abel_integrand_integrable :
    ∀ (c : ℕ → ℝ) (a b : ℝ), 2 ≤ a → a ≤ b → (∀ k : ℕ, 0 ≤ c k) →
      MeasureTheory.IntegrableOn (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / (t * Real.log t ^ 2)) (Set.Ioc a b) MeasureTheory.volume := by
  intro c a b ha hab hc
  have hmemIcc : ∀ t ∈ Set.Icc a b, 2 ≤ t := fun t ht => le_trans ha ht.1
  have hsubne : ∀ t ∈ Set.Icc a b, t ∈ ({0}ᶜ : Set ℝ) := fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (by linarith [hmemIcc t ht])
  have hcontD : ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Icc a b) := ContinuousOn.inv₀ (ContinuousOn.mul continuousOn_id (ContinuousOn.pow (Real.continuousOn_log.mono hsubne) 2)) (fun t ht => ne_of_gt (mul_pos (by linarith [hmemIcc t ht] : (0:ℝ) < t) (pow_pos (Real.log_pos (by linarith [hmemIcc t ht] : (1:ℝ) < t)) 2)))
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.Ioc a b) MeasureTheory.volume := hcontD.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hbint : MeasureTheory.IntegrableOn (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k) * (t * Real.log t ^ 2)⁻¹) (Set.Ioc a b) MeasureTheory.volume := hbase.const_mul _
  have hmeasA : Measurable (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)) := Measurable.comp (g := fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, c k) (f := fun t : ℝ => ⌊t⌋₊) measurable_from_top Nat.measurable_floor
  have hmeasD : Measurable (fun t : ℝ => t * Real.log t ^ 2) := measurable_id.mul (Real.measurable_log.pow_const 2)
  have hmeas : Measurable (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / (t * Real.log t ^ 2)) := hmeasA.div hmeasD
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc a b)), ‖(∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / (t * Real.log t ^ 2)‖ ≤ (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k) * (t * Real.log t ^ 2)⁻¹ := (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun t ht => by have h2t : (2:ℝ) ≤ t := le_trans ha (le_of_lt ht.1); have htpos : (0:ℝ) < t := (by linarith); have hDpos : (0:ℝ) < t * Real.log t ^ 2 := mul_pos htpos (pow_pos (Real.log_pos (by linarith)) 2); have hA0 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := Finset.sum_nonneg (fun k _ => hc k); have hAle : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) ≤ ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.floor_le_floor ht.2)) (fun k _ _ => hc k); rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hA0 (le_of_lt hDpos))]; exact mul_le_mul_of_nonneg_right hAle (inv_nonneg.mpr (le_of_lt hDpos))))
  exact MeasureTheory.Integrable.mono' hbint hmeas.aestronglyMeasurable hae

end Erdos858
