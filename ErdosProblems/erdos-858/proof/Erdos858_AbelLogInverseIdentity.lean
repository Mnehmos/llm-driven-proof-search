/-
Erdős Problem #858 — §5.2/§5.3 o(1)-Mertens arc, atom 1 (Chojecki 2026).

`Abel identity for log-inverse weights` (GENERIC): for any arithmetic weight
`c : ℕ → ℝ` and `x ≥ 2`, with `f(t) = 1/log t`:

  `Σ_{2<k≤⌊x⌋} c(k)/log k
     = C(x)/log x − C(2)/log 2 − ∫_{(2,x]} (−t⁻¹/log²t)·C(t) dt`,

where `C(y) = Σ_{k≤⌊y⌋} c(k)`. Specialized at `c(k) = [k prime]·log k/k`
(so `C = A`, the Mertens-first-theorem partial sum `Σ_{p≤y} log p/p`, and each
summand becomes `1/k`), this is the split identity

  `Σ_{2<p≤x} 1/p = A(x)/log x − A(2)/log 2 + ∫_{(2,x]} A(t)/(t log²t) dt`

driving the o(1)-form of Mertens' second theorem (`Σ_{p≤x} 1/p = loglog x + M
+ o(1)`) — whose INTERVAL form (the constant `M` cancels, the same trick as
#78) yields the prime block masses `Σ_{N^s<p≤N^t} 1/p → log(t/s)` of the §5.3
prime-harmonic transfer.

Built directly on Mathlib's Abel summation `sum_mul_eq_sub_sub_integral_mul`
(availability in this pin confirmed 2026-07-16), with the derivative
`(1/log t)' = −t⁻¹/log²t` via `HasDerivAt.inv` on `Real.hasDerivAt_log`, and
integrability of the derivative from continuity (`ContinuousOn.div` chain +
`IntegrableOn.congr_fun`). Adapted from the kernel-verified erdos-647 template
`Erdos647_PrimeLogDivIdentity.lean` (read-only reference), restructured to the
single-line pipeline discipline.

Kernel-verified via the proofsearch MCP:
  episode f31ed437-964c-4689-81e5-d99d8135b206,
  problem_version_id 3374318c-aedc-4ae0-b1ac-88f57982a006.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 0408de12bfd240a778b2619b0f45c9ca21ce9a6c05ba7d686af8796fc14df3bc.

**Lean note**: stating BOTH the `EqOn` form (for `IntegrableOn.congr_fun`) and
a plain-∀ pointwise equation `hde` (for the per-point integrand `rw` inside
`setIntegral_congr_fun`) avoids the EqOn-application-redex `rw` failure mode.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 1 (generic Abel identity, `f = (log ·)⁻¹`): for any
weight `c` and `x ≥ 2`, `Σ_{2<k≤⌊x⌋} c(k)/log k = C(x)/log x − C(2)/log 2 −
∫ (−t⁻¹/log²t)·C(t)`. Specialize `c := [prime]·log k/k` for the Mertens-2
split identity. Via `sum_mul_eq_sub_sub_integral_mul` + `HasDerivAt.inv`. -/
theorem erdos858_abel_log_inverse_identity :
    ∀ (c : ℕ → ℝ) (x : ℝ), 2 ≤ x →
      ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (Real.log (k:ℝ))⁻¹ * c k
        = (Real.log x)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k)
          - (Real.log 2)⁻¹ * (∑ k ∈ Finset.Icc 0 2, c k)
          - ∫ t in Set.Ioc (2:ℝ) x, -(t:ℝ)⁻¹ / Real.log t ^ 2 * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) := by
  intro c x hx
  have hderiv : ∀ t ∈ Set.Icc (2:ℝ) x, HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-(t:ℝ)⁻¹ / Real.log t ^ 2) t := fun t ht => (Real.hasDerivAt_log (ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1] : (0:ℝ) < t))).inv (ne_of_gt (Real.log_pos (by linarith [(Set.mem_Icc.mp ht).1] : (1:ℝ) < t)))
  have hf_diff : ∀ t ∈ Set.Icc (2:ℝ) x, DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) t := fun t ht => (hderiv t ht).differentiableAt
  have hderiv_eq : Set.EqOn (fun t : ℝ => -(t:ℝ)⁻¹ / Real.log t ^ 2) (deriv (fun u : ℝ => (Real.log u)⁻¹)) (Set.Icc (2:ℝ) x) := fun t ht => ((hderiv t ht).deriv).symm
  have hde : ∀ t ∈ Set.Icc (2:ℝ) x, deriv (fun u : ℝ => (Real.log u)⁻¹) t = -(t:ℝ)⁻¹ / Real.log t ^ 2 := fun t ht => (hderiv t ht).deriv
  have hsubne : ∀ t ∈ Set.Icc (2:ℝ) x, t ∈ ({0}ᶜ : Set ℝ) := fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1])
  have hgcont : ContinuousOn (fun t : ℝ => -(t:ℝ)⁻¹ / Real.log t ^ 2) (Set.Icc (2:ℝ) x) := ContinuousOn.div (ContinuousOn.neg (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (by linarith [(Set.mem_Icc.mp ht).1] : (0:ℝ) < t)))) (ContinuousOn.pow (Real.continuousOn_log.mono hsubne) 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [(Set.mem_Icc.mp ht).1] : (1:ℝ) < t))))
  have hf_int : MeasureTheory.IntegrableOn (deriv (fun u : ℝ => (Real.log u)⁻¹)) (Set.Icc (2:ℝ) x) MeasureTheory.volume := MeasureTheory.IntegrableOn.congr_fun hgcont.integrableOn_Icc hderiv_eq measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c (by norm_num : (0:ℝ) ≤ 2) hx hf_diff hf_int
  have hfloor2 : ⌊(2:ℝ)⌋₊ = 2 := by norm_num
  rw [hfloor2] at habel
  have hint : (∫ t in Set.Ioc (2:ℝ) x, deriv (fun u : ℝ => (Real.log u)⁻¹) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = ∫ t in Set.Ioc (2:ℝ) x, -(t:ℝ)⁻¹ / Real.log t ^ 2 * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) := MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [hde t (Set.mem_Icc.mpr ⟨le_of_lt ht.1, ht.2⟩)])
  rw [hint] at habel
  exact habel

end Erdos858
