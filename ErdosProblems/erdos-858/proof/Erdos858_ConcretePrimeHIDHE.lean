/-
Erdős Problem #858 — Mertens-1 Abel-split chain, ATOM 3 (final combination) of
the row 5.7/Lemma 5.5 literal-completion assembly (Chojecki 2026).

**THE CAPSTONE of the three-atom Mertens-1 chain**: combines atoms 1 and 2's
proof bodies (spliced verbatim, since `problem_version`s cannot
cross-reference each other) into a single CONJUNCTION giving BOTH the
deterministic identity (`hID`) and the tail bound (`hE`) at the CONCRETE prime
setting — in EXACTLY the shape `erdos858_prime_block_mass_limit` (#129) and
`erdos858_uniform_prime_block_mass_bound` (this session's uniform capstone)
need as their own `hID`/`hE` hypotheses. This is a directly-pluggable
`hID ∧ hE` pair for the real prime-reciprocal sum, closing the technical gap
identified when the row 5.7 literal completion was first scoped.

Both halves of the conjunction are byte-identical copies of atoms 1
(`Erdos858_ConcretePrimeIntervalIdentity.lean`) and 2
(`Erdos858_ConcretePrimeTailBound.lean`)'s own proof bodies — verified on the
FIRST submission as expected, since neither half contains any new reasoning
beyond what was already independently kernel-verified.

Kernel-verified via the proofsearch MCP:
  episode b7dd80fa-d30f-4789-88f6-59d44fdc8e1f,
  problem_version_id 2918f9e9-c643-425f-94b7-067f7f3983c1.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7fad8f796ece38a31a2d1cb4074aa4b4d82c5b8852accee9af50aa84345239bd.
-/
import Mathlib

namespace Erdos858

/-- Mertens-1 chain CAPSTONE: `hID ∧ hE` at the concrete prime log-weight sum,
combining atoms 1+2 (spliced) into the exact shape `erdos858_prime_block_mass_limit`
/ `erdos858_uniform_prime_block_mass_bound` need — the literal Mertens-1
instantiation the row 5.7/Lemma 5.5 assembly was blocked on. -/
theorem erdos858_concrete_prime_hID_hE :
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
    (∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, (Real.log t)⁻¹ * t⁻¹ = Real.log (Real.log b) - Real.log (Real.log a)) →
    (∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, t⁻¹ / Real.log t ^ 2 = (Real.log a)⁻¹ - (Real.log b)⁻¹) →
    ((∀ x : ℝ, 2 ≤ x →
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
            + ∫ t in Set.Ioc (m:ℝ) (n:ℝ), (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) →
    ((∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, (Real.log t)⁻¹ * t⁻¹ = Real.log (Real.log b) - Real.log (Real.log a)) →
      ∀ (A : ℝ → ℝ) (a b : ℝ), 2 ≤ a → a ≤ b →
        MeasureTheory.IntegrableOn (fun t : ℝ => A t / (t * Real.log t ^ 2)) (Set.Ioc a b) MeasureTheory.volume →
        ∫ t in Set.Ioc a b, A t / (t * Real.log t ^ 2)
          = (Real.log (Real.log b) - Real.log (Real.log a)) + ∫ t in Set.Ioc a b, (A t - Real.log t) / (t * Real.log t ^ 2)) →
    ((∀ a b : ℝ, 2 ≤ a → a ≤ b →
        ∫ t in a..b, t⁻¹ / Real.log t ^ 2 = (Real.log a)⁻¹ - (Real.log b)⁻¹) →
      ∀ (g : ℝ → ℝ) (C a b : ℝ), 0 ≤ C → 2 ≤ a → a ≤ b →
        MeasureTheory.IntegrableOn g (Set.Ioc a b) MeasureTheory.volume →
        (∀ t ∈ Set.Ioc a b, |g t| ≤ C * (t⁻¹ / Real.log t ^ 2)) →
        |∫ t in Set.Ioc a b, g t| ≤ C * ((Real.log a)⁻¹ - (Real.log b)⁻¹)) →
    (∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
        (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
        |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2) →
    ∀ (Cm : ℝ), (∀ k:ℕ, 2≤k → |(∑ p ∈ Finset.Icc 1 k with p.Prime, Real.log (p:ℝ)/(p:ℝ)) - Real.log (k:ℝ)| ≤ Cm) →
    (∀ m n : ℕ, 2 ≤ m → m ≤ n →
       (∑ p ∈ Finset.Ioc m n with p.Prime, (1:ℝ)/(p:ℝ))
         = ((∑ p ∈ Finset.Icc 1 n with p.Prime, Real.log (p:ℝ)/(p:ℝ))/Real.log (n:ℝ) - (∑ p ∈ Finset.Icc 1 m with p.Prime, Real.log (p:ℝ)/(p:ℝ))/Real.log (m:ℝ))
           + (Real.log (Real.log (n:ℝ)) - Real.log (Real.log (m:ℝ)))
           + (∫ t in Set.Ioc (m:ℝ) (n:ℝ), ((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ)/(p:ℝ)) - Real.log t)/(t*Real.log t^2)))
    ∧
    (∀ m n : ℕ, 2 ≤ m → m ≤ n →
       |∫ t in Set.Ioc (m:ℝ) (n:ℝ), ((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ)/(p:ℝ)) - Real.log t)/(t*Real.log t^2)|
         ≤ (Cm+Real.log 2)/Real.log (m:ℝ)) := by
  intro h118c h121 h122 h124 h120 h119 hAbelId_thm hMainTerm_thm hTailBound_thm hfloorrem Cm hCm
  refine ⟨fun m n hm hmn => ?_, fun m n hm hmn => ?_⟩
  · have hAbelId := hAbelId_thm h118c h121 h122 h124 m n hm hmn
    have hfil : ∀ k : ℕ, (Finset.Icc 0 k).filter Nat.Prime = (Finset.Icc 1 k).filter Nat.Prime := fun k => by ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨hp.one_lt.le, hb⟩, hp⟩, fun ⟨⟨_, hb⟩, hp⟩ => ⟨⟨Nat.zero_le _, hb⟩, hp⟩⟩
    have hCA : ∀ k : ℕ, (∑ j ∈ Finset.Icc 0 k, (if j.Prime then Real.log (j:ℝ) / (j:ℝ) else 0)) = ∑ p ∈ Finset.Icc 1 k with p.Prime, Real.log (p:ℝ) / (p:ℝ) := fun k => by rw [← Finset.sum_filter, hfil k, Finset.sum_filter]
    have hc0 : ∀ k : ℕ, (0:ℝ) ≤ (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) := fun k => by by_cases hp : k.Prime <;> simp only [hp, if_true, if_false] <;> first | exact le_refl 0 | exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) (Nat.cast_nonneg k)
    have hmr : (2:ℝ) ≤ (m:ℝ) := (by exact_mod_cast hm)
    have hmnr : (m:ℝ) ≤ (n:ℝ) := (by exact_mod_cast hmn)
    have hint0 := h124 (fun k => if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0) (m:ℝ) (n:ℝ) hmr hmnr hc0
    have hinteq : Set.EqOn (fun t : ℝ => (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log (k:ℝ) / (k:ℝ) else 0)) / (t * Real.log t ^ 2)) (fun t : ℝ => (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) (Set.Ioc (m:ℝ) (n:ℝ)) := fun t _ => by simp only [hCA]
    have hint : MeasureTheory.IntegrableOn (fun t : ℝ => (∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / (t * Real.log t ^ 2)) (Set.Ioc (m:ℝ) (n:ℝ)) MeasureTheory.volume := MeasureTheory.IntegrableOn.congr_fun hint0 hinteq measurableSet_Ioc
    have hMainTerm := hMainTerm_thm h120 (fun t => ∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) (m:ℝ) (n:ℝ) hmr hmnr hint
    rw [hAbelId, hMainTerm]
    ring
  · have hmr : (2:ℝ) ≤ (m:ℝ) := (by exact_mod_cast hm)
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
