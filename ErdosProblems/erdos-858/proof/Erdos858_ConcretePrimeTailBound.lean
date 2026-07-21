/-
Erdős Problem #858 — Mertens-1 Abel-split chain, ATOM 2 of the row 5.7/Lemma
5.5 literal-completion assembly (Chojecki 2026).

**Bounds atom 1's remainder integral** `∫(A−logt)/(t·log²t)` by `(Cm+log2)/logm`
— matching `erdos858_prime_block_mass_limit`'s (#129) `hE` hypothesis shape at
the concrete prime setting. Combines `erdos858_dominated_tail_bound` (generic
pointwise-domination integral bound) with `erdos858_floor_remainder_bound`
(converts the given Mertens-1 bound `|A(k)−logk|≤Cm` for naturals `k` into the
real-`t` pointwise bound `|A(⌊t⌋)−logt|≤Cm+log2` needed as the dominating
function). The integrability certificate the tail bound needs is re-derived
via TWO pieces: the same `h124`-based technique from atom 1 (integrability of
`A/(t·log²t)`), plus a fresh `ContinuousOn`-based derivation for
`(logt)⁻¹·t⁻¹` mirroring `erdos858_main_term_extraction`'s own internal
proof — subtracted via `IntegrableOn.sub` and transported along the pointwise
identity `(A−logt)/(t·log²t) = A/(t·log²t) − (logt)⁻¹t⁻¹` (`field_simp`).

Kernel-verified via the proofsearch MCP:
  episode ec73caa8-e70c-4832-bee4-d0a45e1bdb53,
  problem_version_id 942d0efe-31ad-40e4-8179-15110d3c0d21.
Outcome: kernel_verified / root_proved (2nd submission — 1st hit two issues:
(a) a trailing `ring` after `field_simp` on an already-closed goal, "no goals
to be solved" — `field_simp` alone closes that class of goal, matching the
already-banked lesson; (b) a genuine logic gap — `erdos858_dominated_tail_bound`
concludes `C*((1/loga)−(1/logb))`, NOT `C/loga` as this atom's target states —
fixed by adding a final step showing `(1/logm−1/logn)≤1/logm` (since
`1/logn≥0` for `n>1`) hence `C*(...)≤C/logm` via `mul_le_mul_of_nonneg_left`,
chained onto the raw tail-bound result via `le_trans`).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c628f9ea47ef776810c3a6feabd56599c6d868635b42c56a0312f875fd73bf67.
-/
import Mathlib

namespace Erdos858

/-- Mertens-1 chain atom 2: `|∫(A−logt)/(t·log²t)| ≤ (Cm+log2)/logm` for the
CONCRETE prime log-weight `A`, chaining `dominated_tail_bound` +
`floor_remainder_bound` + a fresh integrability derivation, then tightening
`C*(1/logm−1/logn)` down to `C/logm`. -/
theorem erdos858_concrete_prime_tail_bound :
    (∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, t⁻¹ / Real.log t ^ 2 = (Real.log a)⁻¹ - (Real.log b)⁻¹) →
    ((∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, t⁻¹ / Real.log t ^ 2 = (Real.log a)⁻¹ - (Real.log b)⁻¹) →
      ∀ (g : ℝ → ℝ) (C a b : ℝ), 0 ≤ C → 2 ≤ a → a ≤ b →
        MeasureTheory.IntegrableOn g (Set.Ioc a b) MeasureTheory.volume →
        (∀ t ∈ Set.Ioc a b, |g t| ≤ C * (t⁻¹ / Real.log t ^ 2)) →
        |∫ t in Set.Ioc a b, g t| ≤ C * ((Real.log a)⁻¹ - (Real.log b)⁻¹)) →
    (∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
        (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
        |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2) →
    (∀ (c : ℕ → ℝ) (a b : ℝ), 2 ≤ a → a ≤ b → (∀ k : ℕ, 0 ≤ c k) →
        MeasureTheory.IntegrableOn (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) / (t * Real.log t ^ 2)) (Set.Ioc a b) MeasureTheory.volume) →
    ∀ (Cm : ℝ), (∀ k:ℕ, 2≤k → |(∑ p ∈ Finset.Icc 1 k with p.Prime, Real.log (p:ℝ)/(p:ℝ)) - Real.log (k:ℝ)| ≤ Cm) →
    ∀ m n : ℕ, 2 ≤ m → m ≤ n →
      |∫ t in Set.Ioc (m:ℝ) (n:ℝ), ((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) - Real.log t) / (t * Real.log t ^ 2)|
        ≤ (Cm + Real.log 2) / Real.log (m:ℝ) := by
  intro h119 hTailBound_thm hfloorrem h124 Cm hCm m n hm hmn
  have hmr : (2:ℝ) ≤ (m:ℝ) := (by exact_mod_cast hm)
  have hmnr : (m:ℝ) ≤ (n:ℝ) := (by exact_mod_cast hmn)
  have hfil : ∀ k : ℕ, (Finset.Icc 0 k).filter Nat.Prime = (Finset.Icc 1 k).filter Nat.Prime := fun k => by ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨hp.one_lt.le, hb⟩, hp⟩, fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨Nat.zero_le _, hb⟩, hp⟩⟩
  have hCA : ∀ k : ℕ, (∑ j ∈ Finset.Icc 0 k, (if j.Prime then Real.log (j:ℝ) / (j:ℝ) else 0)) = ∑ p ∈ Finset.Icc 1 k with p.Prime, Real.log (p:ℝ) / (p:ℝ) := fun k => by rw [← Finset.sum_filter, hfil k, Finset.sum_filter]
  have hc0 : ∀ k : ℕ, (0:ℝ) ≤ (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) := fun k => by by_cases hp : k.Prime <;> simp only [hp, if_true, if_false] <;> first | exact le_refl 0 | exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) (Nat.cast_nonneg k)
  have hint0 := h124 (fun k => if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) (m:ℝ) (n:ℝ) hmr hmnr hc0
  have hinteq : Set.EqOn (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0)) / (t * Real.log t ^ 2)) (fun t : ℝ => (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) (Set.Ioc (m:ℝ) (n:ℝ)) := fun t _ => by simp only [hCA]
  have hAint : MeasureTheory.IntegrableOn (fun t : ℝ => (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) (Set.Ioc (m:ℝ) (n:ℝ)) MeasureTheory.volume := MeasureTheory.IntegrableOn.congr_fun hint0 hinteq measurableSet_Ioc
  have hmem : ∀ t ∈ Set.Icc (m:ℝ) (n:ℝ), 2 ≤ t := fun t ht => le_trans hmr ht.1
  have hsubne : ∀ t ∈ Set.Icc (m:ℝ) (n:ℝ), t ∈ ({0}ᶜ : Set ℝ) := fun t ht => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt (by linarith [hmem t ht])
  have hcontM : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹ * t⁻¹) (Set.Icc (m:ℝ) (n:ℝ)) := ContinuousOn.mul (ContinuousOn.inv₀ (Real.continuousOn_log.mono hsubne) (fun t ht => ne_of_gt (Real.log_pos (by linarith [hmem t ht] : (1:ℝ) < t)))) (ContinuousOn.inv₀ continuousOn_id (fun t ht => ne_of_gt (by linarith [hmem t ht] : (0:ℝ) < t)))
  have hMint : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.log t)⁻¹ * t⁻¹) (Set.Ioc (m:ℝ) (n:ℝ)) MeasureTheory.volume := hcontM.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have heqfun : ∀ t ∈ Set.Ioc (m:ℝ) (n:ℝ), ((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) - Real.log t) / (t * Real.log t ^ 2) = (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2) - (Real.log t)⁻¹ * t⁻¹ := fun t ht => by have h2t : (2:ℝ) ≤ t := le_trans hmr (le_of_lt ht.1); have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith)); have htne : t ≠ 0 := ne_of_gt (by linarith); field_simp
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ => ((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) - Real.log t) / (t * Real.log t ^ 2)) (Set.Ioc (m:ℝ) (n:ℝ)) MeasureTheory.volume := (hAint.sub hMint).congr_fun (fun t ht => (heqfun t ht).symm) measurableSet_Ioc
  have hbound : ∀ t ∈ Set.Ioc (m:ℝ) (n:ℝ), |((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) - Real.log t) / (t * Real.log t ^ 2)| ≤ (Cm + Real.log 2) * (t⁻¹ / Real.log t ^ 2) := (by
    intro t ht
    have h2t : (2:ℝ) ≤ t := le_trans hmr (le_of_lt ht.1)
    have hfr := hfloorrem (fun k => ∑ p ∈ Finset.Icc 1 k with p.Prime, Real.log (p:ℝ) / (p:ℝ)) Cm t h2t hCm
    have htpos : (0:ℝ) < t := (by linarith)
    have hlogtpos : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
    have heq : (Cm + Real.log 2) * (t⁻¹ / Real.log t ^ 2) = (Cm + Real.log 2) / (t * Real.log t ^ 2) := (by field_simp)
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t * Real.log t ^ 2), heq]
    gcongr)
  have hCmnn : 0 ≤ Cm + Real.log 2 := (by
    have h1 : 0 ≤ Cm := le_trans (abs_nonneg _) (hCm 2 le_rfl)
    have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith)
  have hraw := hTailBound_thm h119 _ (Cm + Real.log 2) (m:ℝ) (n:ℝ) hCmnn hmr hmnr hgint hbound
  have hn2 : 2 ≤ n := le_trans hm hmn
  have hlogn_pos : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hstep : (Cm + Real.log 2) * ((Real.log (m:ℝ))⁻¹ - (Real.log (n:ℝ))⁻¹) ≤ (Cm + Real.log 2) / Real.log (m:ℝ) := (by
    have h1 : (Real.log (m:ℝ))⁻¹ - (Real.log (n:ℝ))⁻¹ ≤ (Real.log (m:ℝ))⁻¹ := (by nlinarith [inv_nonneg.mpr hlogn_pos.le])
    have h2 : (Cm + Real.log 2) * ((Real.log (m:ℝ))⁻¹) = (Cm + Real.log 2) / Real.log (m:ℝ) := (by rw [div_eq_mul_inv])
    calc (Cm + Real.log 2) * ((Real.log (m:ℝ))⁻¹ - (Real.log (n:ℝ))⁻¹) ≤ (Cm + Real.log 2) * (Real.log (m:ℝ))⁻¹ := (mul_le_mul_of_nonneg_left h1 hCmnn)
      _ = (Cm + Real.log 2) / Real.log (m:ℝ) := h2)
  exact le_trans hraw hstep

end Erdos858
