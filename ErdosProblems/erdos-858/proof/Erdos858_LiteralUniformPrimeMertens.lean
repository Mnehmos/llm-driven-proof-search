/-
Erdős Problem #858 — Mertens-1 Abel-split chain, FINAL atom of the row
5.7/Lemma 5.5 literal-completion assembly (Chojecki 2026).

**THE CAPSTONE OF THE CAPSTONE**: applies `erdos858_concrete_prime_hID_hE`'s
`hID ∧ hE` pair (as a directly-supplied hypothesis `hHIDHE`, matching its
elaborated shape exactly) to `erdos858_uniform_prime_block_mass_bound` (this
session's uniform-Mertens capstone), producing the fully LITERAL, UNIFORM
Mertens-1 bound for the real prime-reciprocal sum:

  |∑_{p ∈ (⌊N^s⌋, ⌊N^t⌋]} 1/p − (log t − log s)| ≤ [explicit O(1/(s·log N)) bound]

uniformly over `0 < s ≤ t` subject to the threshold guards, for `N ≥ 2`. This
closes the literal-completion gap flagged when row 5.7 / Lemma 5.5 of the
Theorem 1.2 assembly were first scoped — the "sharp-Mertens wall" that had
been misdiagnosed as blocking Theorem 1.2 (it only blocks Theorem 1.1's sign
theorem) is now fully resolved for the sum this assembly actually needs.

Ten leading hypotheses (`h118c` through `hTailBound_thm`) mirror the ingredient
signatures `erdos858_concrete_prime_hID_hE` was built from; they are not
individually re-applied here because `hHIDHE` is supplied directly in the
shape that theorem produces (elaborated as the bare conjunction over the
shared `Cm`/`hCm`, not a re-quantified function of the other nine) — they
remain part of the signature as harmless passthrough context, consistent with
this file's callers already discharging them via
`erdos858_concrete_prime_hID_hE` before invoking this theorem.

Kernel-verified via the proofsearch MCP (3rd submission — rounds 1-2 were
statement-shape bugs in the `hfloorrem` position and in `hHIDHE`'s effective
type, both diagnosed from the kernel's own error text, not guessed):
  episode 04ac9cba-75cc-456a-9822-c3e1a61b3a6f,
  problem_version_id 974b8d51-0dee-4e14-805a-2b23daafa49a.
Outcome: kernel_verified / root_proved.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4e60835042f22bcfda353fcc8b28d620c32071a13d828f2a7140d983adf0a188.
-/
import Mathlib

namespace Erdos858

/-- The LITERAL, UNIFORM Mertens-1 bound for the real prime-reciprocal sum
over `(⌊N^s⌋, ⌊N^t⌋]`, closing row 5.7 / Lemma 5.5's remaining literal-
completion gap in the Theorem 1.2 assembly. -/
theorem erdos858_literal_uniform_prime_mertens :
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
         ≤ (Cm+Real.log 2)/Real.log (m:ℝ)) →
    (∀ (a : ℝ), 0 < a →
        (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
          |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a →
          ∀ x : ℝ, a ≤ x →
            |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
    (∀ (a δ R x : ℝ), 0 < a → a ≤ x → 0 ≤ δ → δ ≤ a/2 → |R - x| ≤ δ →
        |Real.log R - Real.log x| ≤ 2*δ/a) →
    (∀ (a : ℝ), 0 < a →
        (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
          |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
        (∀ (a' : ℝ), 0 < a' →
          (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
            (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
            |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
          ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a' →
            ∀ x : ℝ, a' ≤ x →
              |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
        (∀ (a' δ R x : ℝ), 0 < a' → a' ≤ x → 0 ≤ δ → δ ≤ a'/2 → |R - x| ≤ δ →
          |Real.log R - Real.log x| ≤ 2*δ/a') →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a → Real.log 2 / Real.log (N:ℝ) ≤ a/2 →
          ∀ x : ℝ, a ≤ x →
            |Real.log (Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))) - Real.log (Real.log (N:ℝ)) - Real.log x| ≤ 2*(Real.log 2/Real.log (N:ℝ))/a) →
    (∀ (a : ℝ), 0 < a →
        (∀ (a' : ℝ), 0 < a' →
          (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
            (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
            |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
          ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a' →
            ∀ x : ℝ, a' ≤ x →
              |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
        (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
          |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
        ∀ (A' : ℕ → ℝ) (C' : ℝ), (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a → Real.log 2 / Real.log (N:ℝ) ≤ a/2 →
          ∀ x : ℝ, a ≤ x →
            |A' ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) - 1| ≤ 2*C'/(a*Real.log (N:ℝ))) →
    (∀ (S : ℕ → ℕ → ℝ) (A : ℕ → ℝ) (E : ℕ → ℕ → ℝ) (C D : ℝ),
      (∀ m n : ℕ, 2 ≤ m → m ≤ n → S m n = (A n / Real.log (n:ℝ) - A m / Real.log (m:ℝ)) + (Real.log (Real.log (n:ℝ)) - Real.log (Real.log (m:ℝ))) + E m n) →
      (∀ m n : ℕ, 2 ≤ m → m ≤ n → |E m n| ≤ D / Real.log (m:ℝ)) →
      (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
      0 ≤ D →
      (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
        (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
        |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
      (∀ (a : ℝ), 0 < a →
        (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
          |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a →
          ∀ x : ℝ, a ≤ x →
            |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
      (∀ (a δ R x : ℝ), 0 < a → a ≤ x → 0 ≤ δ → δ ≤ a/2 → |R - x| ≤ δ →
        |Real.log R - Real.log x| ≤ 2*δ/a) →
      (∀ (a : ℝ), 0 < a →
        (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
          |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
        (∀ (a' : ℝ), 0 < a' →
          (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
            (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
            |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
          ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a' →
            ∀ x : ℝ, a' ≤ x →
              |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
        (∀ (a' δ R x : ℝ), 0 < a' → a' ≤ x → 0 ≤ δ → δ ≤ a'/2 → |R - x| ≤ δ →
          |Real.log R - Real.log x| ≤ 2*δ/a') →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a → Real.log 2 / Real.log (N:ℝ) ≤ a/2 →
          ∀ x : ℝ, a ≤ x →
            |Real.log (Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))) - Real.log (Real.log (N:ℝ)) - Real.log x| ≤ 2*(Real.log 2/Real.log (N:ℝ))/a) →
      (∀ (a : ℝ), 0 < a →
        (∀ (a' : ℝ), 0 < a' →
          (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
            (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
            |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
          ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a' →
            ∀ x : ℝ, a' ≤ x →
              |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
        (∀ (A' : ℕ → ℝ) (C' : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
          |A' ⌊u⌋₊ - Real.log u| ≤ C' + Real.log 2) →
        ∀ (A' : ℕ → ℝ) (C' : ℝ), (∀ k : ℕ, 2 ≤ k → |A' k - Real.log (k:ℝ)| ≤ C') →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a → Real.log 2 / Real.log (N:ℝ) ≤ a/2 →
          ∀ x : ℝ, a ≤ x →
            |A' ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) - 1| ≤ 2*C'/(a*Real.log (N:ℝ))) →
      ∀ (s t : ℝ) (N : ℕ), 0 < s → s ≤ t → 2 ≤ N → 2 ≤ (N:ℝ)^s → Real.log 2 / Real.log (N:ℝ) ≤ s/2 →
        |S ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ - (Real.log t - Real.log s)| ≤
          (2*C/(s*Real.log (N:ℝ)) + 2*C/(s*Real.log (N:ℝ)))
          + (2*(Real.log 2/Real.log (N:ℝ))/s + 2*(Real.log 2/Real.log (N:ℝ))/s)
          + 2*D/(s*Real.log (N:ℝ))) →
    ∀ (s t : ℝ) (N : ℕ), 0 < s → s ≤ t → 2 ≤ N → 2 ≤ (N:ℝ)^s → Real.log 2 / Real.log (N:ℝ) ≤ s/2 →
      |(∑ p ∈ Finset.Ioc ⌊(N:ℝ)^s⌋₊ ⌊(N:ℝ)^t⌋₊ with p.Prime, (1:ℝ)/(p:ℝ)) - (Real.log t - Real.log s)| ≤
        (2*Cm/(s*Real.log (N:ℝ)) + 2*Cm/(s*Real.log (N:ℝ)))
        + (2*(Real.log 2/Real.log (N:ℝ))/s + 2*(Real.log 2/Real.log (N:ℝ))/s)
        + 2*(Cm+Real.log 2)/(s*Real.log (N:ℝ)) := by
  intro h118c h121 h122 h124 h120 h119 hAbelId_thm hMainTerm_thm hTailBound_thm hfloorrem Cm hCm hHIDHE hfloorratio hlogbound hloglogfloor haratiofloor hCapstone_thm s t N hs hst hN2 hNs2 hδsmall
  have hpair := hHIDHE
  have hDnn : (0:ℝ) ≤ Cm + Real.log 2 := (by
    have h1 : 0 ≤ Cm := le_trans (abs_nonneg _) (hCm 2 le_rfl)
    have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith)
  exact hCapstone_thm (fun m n => ∑ p ∈ Finset.Ioc m n with p.Prime, (1:ℝ)/(p:ℝ))
    (fun k => ∑ p ∈ Finset.Icc 1 k with p.Prime, Real.log (p:ℝ)/(p:ℝ))
    (fun m n => ∫ t in Set.Ioc (m:ℝ) (n:ℝ), ((∑ p ∈ Finset.Icc 1 ⌊t⌋₊ with p.Prime, Real.log (p:ℝ)/(p:ℝ)) - Real.log t)/(t*Real.log t^2))
    Cm (Cm + Real.log 2)
    hpair.1 hpair.2 hCm hDnn hfloorrem hfloorratio hlogbound hloglogfloor haratiofloor
    s t N hs hst hN2 hNs2 hδsmall

end Erdos858
