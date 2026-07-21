/-
Erdős Problem #858 — §5.2 o(1)-Mertens arc, atom 2 (Chojecki 2026).

`Mertens-2 split identity` (prime specialization of the Abel identity): for
`x ≥ 2`, taking the generic Abel identity (#117) at the weight
`c(k) = [k prime]·log k/k`:

  `Σ_{p≤x} 1/p  =  A(x)/log x  +  ∫_{(2,x]} A(t)/(t·log²t) dt`,

where `A(y) = Σ_{p≤y} log p/p` is the Mertens-first-theorem partial sum. The
`p = 2` boundary terms cancel exactly (`(log 2)⁻¹·(log 2/2) = 1/2` on the right
against the `p = 2` term `1/2` of the left-hand sum).

This is the classical partial-summation form of Mertens' second theorem. With
`A(t) = log t + O(1)` (the verified Mertens-1 stack #47/#48) and the verified
integrals `∫ 1/(t log t) = loglog x − loglog 2` (#56) and `∫ 1/(t log²t) ≤
1/log 2` (#57), the o(1)-form `Σ_{p≤x} 1/p = loglog x + M + o(1)` follows —
whose INTERVAL form (the constant `M` cancels, the same trick as #78) yields
the prime block masses `Σ_{N^s<p≤N^t} 1/p → log(t/s)` of the §5.3
prime-harmonic transfer.

Bookkeeping: filter-set conversions (`Finset.sum_filter` + a `Icc 0 ↔ Icc 1`
filter identity from `Nat.Prime.one_lt`), literal-finset evaluations
(`Finset.Icc (0:ℕ) 2 = {0,1,2}` / `Finset.Ioc (0:ℕ) 2 = {1,2}` by `decide` +
`simp` with `Nat.prime_two`/`not_prime_zero`/`not_prime_one`), the head-split
via #103's own `Finset.sum_Ioc_consecutive`, the per-k field identity
`(log k)⁻¹·(log k/k) = 1/k` (`by_cases <;> simp <;> field_simp`), and the
integrand conversion via `setIntegral_congr_fun` + `ring` +
`MeasureTheory.integral_neg`.

Kernel-verified via the proofsearch MCP:
  episode 6def15d2-59fd-4c18-b14b-cb64cbfa9b19,
  problem_version_id c655b1bd-5041-4370-933e-35f500b9a00f.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash ff208875cbd2ef97037f2af51c9d19844b17c374b77ee6d3d8635687b47004c7.

**Lean lesson (4th distinct pipeline pitfall)**: bare-literal Finset intervals
(`Finset.Icc 0 2`, `Finset.Ioc 0 2`) in a `have`-type whose summands only
carry cast-ascriptions elaborate the index type as ℝ (`LocallyFiniteOrder ℝ` /
`Real.Prime` failures) — always pin `(0:ℕ)` on interval endpoints when no
`⌊·⌋₊` anchors the domain.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 2 (Mertens-2 split identity): specializing the
generic Abel identity (#117, hypothesis) at `c = [prime]·log k/k`,
`Σ_{p≤x} 1/p = A(x)/log x + ∫_{(2,x]} A(t)/(t log²t) dt` for `x ≥ 2` — the
partial-summation form of Mertens' second theorem. The 1/2-boundary terms
cancel exactly. -/
theorem erdos858_mertens2_split_identity :
    (∀ (c : ℕ → ℝ) (x : ℝ), 2 ≤ x →
        ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (Real.log (k:ℝ))⁻¹ * c k
          = (Real.log x)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k)
            - (Real.log 2)⁻¹ * (∑ k ∈ Finset.Icc 0 2, c k)
            - ∫ t in Set.Ioc (2:ℝ) x, -(t:ℝ)⁻¹ / Real.log t ^ 2 * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k)) →
      ∀ x : ℝ, 2 ≤ x →
        ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1:ℝ) / (p:ℝ)
          = (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / Real.log x
            + ∫ t in Set.Ioc (2:ℝ) x, (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2) := by
  intro h117 x hx
  have habel := h117 (fun k => if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) x hx
  have h2floor : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfil : ∀ n : ℕ, (Finset.Icc 0 n).filter Nat.Prime = (Finset.Icc 1 n).filter Nat.Prime := fun n => by ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨hp.one_lt.le, hb⟩, hp⟩, fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨Nat.zero_le _, hb⟩, hp⟩⟩
  have hCA : ∀ n : ℕ, (∑ k ∈ Finset.Icc 0 n, (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0)) = ∑ p ∈ Finset.Icc 1 n with p.Prime, Real.log (p:ℝ) / (p:ℝ) := fun n => by rw [← Finset.sum_filter, hfil n, Finset.sum_filter]
  have hicc02 : Finset.Icc (0:ℕ) 2 = {0, 1, 2} := by decide
  have hC2 : (∑ k ∈ Finset.Icc (0:ℕ) 2, (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0)) = Real.log 2 / 2 := by rw [hicc02]; simp [Nat.not_prime_zero, Nat.not_prime_one, Nat.prime_two]
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hhalf : (Real.log 2)⁻¹ * (Real.log 2 / 2) = 1/2 := by field_simp
  have hsetIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hsplit : (∑ k ∈ Finset.Ioc (0:ℕ) 2, (if k.Prime then (1:ℝ)/(k:ℝ) else 0)) + (∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (if k.Prime then (1:ℝ)/(k:ℝ) else 0)) = ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, (if k.Prime then (1:ℝ)/(k:ℝ) else 0) := Finset.sum_Ioc_consecutive _ (by omega) h2floor
  have hioc02 : Finset.Ioc (0:ℕ) 2 = {1, 2} := by decide
  have hhead : (∑ k ∈ Finset.Ioc (0:ℕ) 2, (if k.Prime then (1:ℝ)/(k:ℝ) else 0)) = 1/2 := by rw [hioc02]; simp [Nat.not_prime_one, Nat.prime_two]
  have hLHS : (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1:ℝ)/(p:ℝ)) = 1/2 + ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (if k.Prime then (1:ℝ)/(k:ℝ) else 0) := by rw [Finset.sum_filter, hsetIcc, ← hsplit, hhead]
  have hterm : ∀ k ∈ Finset.Ioc 2 ⌊x⌋₊, (Real.log (k:ℝ))⁻¹ * (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) = (if k.Prime then (1:ℝ)/(k:ℝ) else 0) := fun k hk => by have hlogne : Real.log (k:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast lt_trans one_lt_two (Finset.mem_Ioc.mp hk).1)); by_cases hp : k.Prime <;> simp [hp] <;> field_simp
  have htermsum : (∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (Real.log (k:ℝ))⁻¹ * (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0)) = ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (if k.Prime then (1:ℝ)/(k:ℝ) else 0) := Finset.sum_congr rfl hterm
  have hint : (∫ t in Set.Ioc (2:ℝ) x, -(t:ℝ)⁻¹ / Real.log t ^ 2 * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0))) = ∫ t in Set.Ioc (2:ℝ) x, -((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) := MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [hCA ⌊t⌋₊]; ring)
  rw [htermsum, hC2, hhalf, hCA ⌊x⌋₊, hint, MeasureTheory.integral_neg, inv_mul_eq_div] at habel
  linarith [habel, hLHS]

end Erdos858
