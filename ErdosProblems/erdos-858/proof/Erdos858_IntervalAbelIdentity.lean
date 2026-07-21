/-
Erdős Problem #858 — §5.2/§5.3 o(1)-Mertens arc, atom 9 (Chojecki 2026).

`interval Abel identity for prime reciprocals` (conditional assembly of the
verified toolkit): for naturals `2 ≤ m ≤ n`,

  `Σ_{m<p≤n} 1/p
     = [A(n)/log n − A(m)/log m]  +  ∫_{(m,n]} A(t)/(t·log²t) dt`,

`A(k) = Σ_{p≤k} log p/p`. Assembled from (all hypotheses, each kernel-verified):
#118's split identity at both endpoints (`⌊(n:ℝ)⌋₊ = n` via `Nat.floor_natCast`),
#121's Finset interval split, #122's Ioc additivity — applied at the filtered
Abel integrand, whose integrability comes from #124 at the prime weight,
transferred along the `Icc 0`-if ↔ filtered-sum equality (`IntegrableOn.congr_fun`).
Final assembly is a 4-fact `linarith`.

This is the exact fixed-endpoint identity whose `N → ∞` limit (at `m=⌊N^s⌋`,
`n=⌊N^t⌋`, with `A = log + O(1)` from the Mertens-1 stack and the FTCs
#119/#120) gives the §5.3 prime block masses `Σ_{N^s<p≤N^t} 1/p → log(t/s)`.

Kernel-verified via the proofsearch MCP:
  episode 2fe5b33e-fa3e-4bdd-934e-9ab0a099c7b3,
  problem_version_id 2557cc1c-15bf-4ab5-9622-496100d0a50a.
Outcome: kernel_verified / root_kernel_verified (2nd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 44c6274452db92af16842b91aa5bf8730b6e412286adb763403e119e4dc8d269.

**Lean lesson**: `Set.EqOn` per-point goals present UN-beta-reduced
(`(fun t => ..) t = (fun t => ..) t`) — `rw` cannot see into the redex; use
`simp only [eq-lemma]` (beta-normalizes first) inside EqOn lambdas.
-/
import Mathlib

namespace Erdos858

/-- o(1)-Mertens arc, atom 9 (interval Abel identity): for `2 ≤ m ≤ n`,
`Σ_{m<p≤n} 1/p = [A(n)/log n − A(m)/log m] + ∫_{(m,n]} A(t)/(t·log²t)`,
from #118 (both endpoints) + #121 + #122 + #124 (hypotheses). -/
theorem erdos858_interval_abel_identity :
    (∀ x : ℝ, 2 ≤ x →
        ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1:ℝ) / (p:ℝ)
          = (∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / Real.log x
            + ∫ t in Set.Ioc (2:ℝ) x, (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) →
      (∀ m n : ℕ, m ≤ n →
        (∑ p ∈ Finset.Icc 1 n with p.Prime, (1:ℝ) / (p:ℝ)) - (∑ p ∈ Finset.Icc 1 m with p.Prime, (1:ℝ) / (p:ℝ))
          = ∑ p ∈ Finset.Ioc m n with p.Prime, (1:ℝ) / (p:ℝ)) →
      (∀ (f : ℝ → ℝ) (a b : ℝ), 2 ≤ a → a ≤ b →
        MeasureTheory.IntegrableOn f (Set.Ioc 2 b) MeasureTheory.volume →
        ∫ t in Set.Ioc (2:ℝ) b, f t = (∫ t in Set.Ioc (2:ℝ) a, f t) + ∫ t in Set.Ioc a b, f t) →
      (∀ (c : ℕ → ℝ) (a b : ℝ), 2 ≤ a → a ≤ b → (∀ k : ℕ, 0 ≤ c k) →
        MeasureTheory.IntegrableOn (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / (t * Real.log t ^ 2)) (Set.Ioc a b) MeasureTheory.volume) →
      ∀ m n : ℕ, 2 ≤ m → m ≤ n →
        ∑ p ∈ Finset.Ioc m n with p.Prime, (1:ℝ) / (p:ℝ)
          = ((∑ p ∈ Finset.Icc 1 n with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / Real.log (n:ℝ)
              - (∑ p ∈ Finset.Icc 1 m with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / Real.log (m:ℝ))
            + ∫ t in Set.Ioc (m:ℝ) (n:ℝ), (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2) := by
  intro h118c h121 h122 h124 m n hm hmn
  have hmr : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmnr : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have hnr : (2:ℝ) ≤ (n:ℝ) := le_trans hmr hmnr
  have hfm := h118c (m:ℝ) hmr
  have hfn := h118c (n:ℝ) hnr
  rw [Nat.floor_natCast] at hfm hfn
  have hfil : ∀ k : ℕ, (Finset.Icc 0 k).filter Nat.Prime = (Finset.Icc 1 k).filter Nat.Prime := fun k => by ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨hp.one_lt.le, hb⟩, hp⟩, fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨Nat.zero_le _, hb⟩, hp⟩⟩
  have hCA : ∀ k : ℕ, (∑ j ∈ Finset.Icc 0 k, (if j.Prime then Real.log (j:ℝ) / (j:ℝ) else 0)) = ∑ p ∈ Finset.Icc 1 k with p.Prime, Real.log (p:ℝ) / (p:ℝ) := fun k => by rw [← Finset.sum_filter, hfil k, Finset.sum_filter]
  have hc0 : ∀ k : ℕ, (0:ℝ) ≤ (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) := fun k => by by_cases hp : k.Prime <;> simp only [hp, if_true, if_false] <;> first | exact le_refl 0 | exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) (Nat.cast_nonneg k)
  have hint0 := h124 (fun k => if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) 2 (n:ℝ) le_rfl hnr hc0
  have hinteq : Set.EqOn (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0)) / (t * Real.log t ^ 2)) (fun t : ℝ => (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) (Set.Ioc 2 (n:ℝ)) := fun t _ => by simp only [hCA]
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) (Set.Ioc 2 (n:ℝ)) MeasureTheory.volume := MeasureTheory.IntegrableOn.congr_fun hint0 hinteq measurableSet_Ioc
  have hadd := h122 (fun t : ℝ => (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) (m:ℝ) (n:ℝ) hmr hmnr hint
  have hsum := h121 m n hmn
  linarith [hfm, hfn, hadd, hsum]

end Erdos858
