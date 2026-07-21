/-
Erdős Problem #858 — Mertens-1 Abel-split chain, ATOM 1 of the row 5.7/Lemma
5.5 literal-completion assembly (Chojecki 2026).

**First of three atoms turning #129's abstract `hID`/`hE` shape into the
concrete prime-sum form**, per the plan scoped in the `erdos-858-thm12-assembly`
memory dossier. Combines `erdos858_interval_abel_identity` (gives the
Abel-split identity in INTEGRAL form: `Σ_{m<p≤n}1/p = Aratio + ∫A/(t·log²t)`)
with `erdos858_main_term_extraction` (splits that integral into
`(loglogn−loglogm) + ∫(A−logt)/(t·log²t)`) to produce the full THREE-TERM
identity matching the shape `erdos858_prime_block_mass_limit`'s (#129) `hID`
hypothesis needs — still with the remainder as an UNBOUNDED integral (bounding
it is atom 2's job, `erdos858_dominated_tail_bound`).

The integrability certificate `erdos858_main_term_extraction` needs (for the
concrete prime log-weight function over `(m,n]`) is NOT inherited from
`interval_abel_identity` automatically — it's re-derived INLINE via the exact
same `h124`-based `Set.EqOn` congr argument that theorem's own internal proof
uses (splicing that proof fragment verbatim, the same "opaque theorem
splicing" technique used throughout this session), since I need it supplied
EXPLICITLY at the `(m,n]` range for the `main_term_extraction` call.

Kernel-verified via the proofsearch MCP:
  episode 312d3477-4e8a-48b9-95b5-05f50bccced7,
  problem_version_id b7058978-c293-45f8-b0cc-cd24736e074e.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 2a2aa20e0911e6774cce383a172857a22c16a457df550cf4ec8e2e2473160356.
-/
import Mathlib

namespace Erdos858

/-- Mertens-1 chain atom 1: `Σ_{m<p≤n}1/p = [Aratio] + [loglog] + ∫(A−logt)/(t·log²t)`
for the CONCRETE prime log-weight `A`, chaining `interval_abel_identity` +
`main_term_extraction` (with the integrability certificate re-derived inline). -/
theorem erdos858_concrete_prime_interval_identity :
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
    ∀ m n : ℕ, 2 ≤ m → m ≤ n →
      ∑ p ∈ Finset.Ioc m n with p.Prime, (1:ℝ) / (p:ℝ)
        = ((∑ p ∈ Finset.Icc 1 n with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / Real.log (n:ℝ)
            - (∑ p ∈ Finset.Icc 1 m with p.Prime, Real.log (p:ℝ) / (p:ℝ)) / Real.log (m:ℝ))
          + (Real.log (Real.log (n:ℝ)) - Real.log (Real.log (m:ℝ)))
          + ∫ t in Set.Ioc (m:ℝ) (n:ℝ), ((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ) / (p:ℝ)) - Real.log t) / (t * Real.log t ^ 2) := by
  intro h118c h121 h122 h124 h120 hAbelId_thm hMainTerm_thm m n hm hmn
  have hAbelId := hAbelId_thm h118c h121 h122 h124 m n hm hmn
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

end Erdos858
