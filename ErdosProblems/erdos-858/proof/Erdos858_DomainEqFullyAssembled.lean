/-
Erdős Problem #858 — Theorem 1.2 assembly, FULLY-ASSEMBLED domain equality (Chojecki 2026).

Glues `lemma45_CN_domain_subset_fully_assembled`
(`Erdos858_DomainSubsetFullyAssembled.lean`) and
`lemma45_CN_domain_supset_fully_assembled`
(`Erdos858_DomainSupsetFullyAssembled.lean`) — both taken as opaque
re-quantified hypotheses (problem_versions cannot cross-reference) — via
`Finset.Subset.antisymm`, instantiated at the shared leaf-level π-axioms.
Pure bookkeeping glue; the union of both source theorems' hypothesis lists
(15 total: the 13 leaf π-axioms/standalone-theorems plus the two big
theorem-hypotheses themselves).

Kernel-verified via the proofsearch MCP:
  episode c0f8f091-ec60-41d7-89d2-137075dba0da,
  problem_version_id 64e7121b-59ea-41a5-96d4-d6b8a09aa552.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 168028c536221ef7eb0f6c1417b6b6ab3ce0a9966db34fc89ad9cc91873597be.
-/
import Mathlib

namespace Erdos858

/-- Fully-assembled domain equality: `{n:π n=a} = P_N(a)-image ∪ Q_N(a)-image`,
gluing the fully-assembled subset/supset directions via `Finset.Subset.antisymm`. -/
theorem lemma45_CN_domain_eq_fully_assembled :
    ∀ (π : ℕ → ℕ) (N a : ℕ), N < a^4 → 1 ≤ a → π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π n < r) →
      (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π m) →
      (∀ a' b' n' : ℕ, a' < b' → b' < n' →
        (∃ u : ℕ, n' = a' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a' < r) →
        (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
        ∃ t : ℕ, b' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) →
      (∀ a' p' : ℕ, 1 ≤ a' → Nat.Prime p' → a' < p' →
        (∃ t : ℕ, a' * p' = a' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a' < r) ∧
          (∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
            (∃ w : ℕ, a' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a' ∨ b = a' * p')) →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → a' * p' * q' ≤ N' → N' < a' ^ 4 → q' < a' * p') →
      (∀ a' p' q' N' : ℕ, 1 ≤ a' → a' < p' → p' ≤ q' → a' * p' * q' ≤ N' → N' < a' ^ 4 → p' < a' * q') →
      (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
      (∀ a' p' q' : ℕ, 1 ≤ a' → Nat.Prime p' → Nat.Prime q' → a' < p' → p' ≤ q' →
        q' < a' * p' → p' < a' * q' →
        (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        ∀ b : ℕ, (∃ s : ℕ, b = a' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a' < r) →
          (∃ w : ℕ, a' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
          b = a' ∨ b = a' * p' * q') →
      (∀ a' t' : ℕ, 1 ≤ a' → 0 < t' → t' < a'^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a' < p) →
        t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ), N' < a'^4 → 1 ≤ a' → π' 1 = 0 →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π' n < r) →
        (∀ a'' t' : ℕ, 1 ≤ a'' → 0 < t' → t' < a''^3 → (∀ p : ℕ, Nat.Prime p → p ∣ t' → a'' < p) →
          t' = 1 ∨ Nat.Prime t' ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t' = p * q) →
        (Finset.Icc 1 N').filter (fun n => π' n = a') ⊆
          ((Finset.Icc (a'+1) N').filter (fun p => Nat.Prime p ∧ a' * p ≤ N')).image (fun p => a' * p)
          ∪ (((Finset.Icc (a'+1) N') ×ˢ (Finset.Icc (a'+1) N')).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a' * (pq.1 * pq.2) ≤ N')).image
              (fun pq => a' * pq.1 * pq.2)) →
      (∀ (π' : ℕ → ℕ) (N' a' : ℕ), N' < a'^4 → 1 ≤ a' →
        (∀ n : ℕ, 2 ≤ n → n ≤ N' → 1 ≤ π' n ∧ π' n < n) →
        (∀ z m : ℕ, z < m → (∃ t : ℕ, m = z * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → z < r) → z ≤ π' m) →
        (∀ n : ℕ, 2 ≤ n → ∃ t : ℕ, n = π' n * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → π' n < r) →
        (∀ a'' b' n' : ℕ, a'' < b' → b' < n' →
          (∃ u : ℕ, n' = a'' * u ∧ ∀ r : ℕ, Nat.Prime r → r ∣ u → a'' < r) →
          (∃ v : ℕ, n' = b' * v ∧ ∀ r : ℕ, Nat.Prime r → r ∣ v → b' < r) →
          ∃ t : ℕ, b' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) →
        (∀ a'' p' : ℕ, 1 ≤ a'' → Nat.Prime p' → a'' < p' →
          (∃ t : ℕ, a'' * p' = a'' * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → a'' < r) ∧
            (∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
              (∃ w : ℕ, a'' * p' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) → b = a'' ∨ b = a'' * p')) →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → q' < a'' * p') →
        (∀ a'' p' q' N'' : ℕ, 1 ≤ a'' → a'' < p' → p' ≤ q' → a'' * p' * q' ≤ N'' → N'' < a'' ^ 4 → p' < a'' * q') →
        (∀ b q' : ℕ, 0 < b → Nat.Prime q' → q' < b → ¬ (∃ t : ℕ, b * q' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
        (∀ a'' p' q' : ℕ, 1 ≤ a'' → Nat.Prime p' → Nat.Prime q' → a'' < p' → p' ≤ q' →
          q' < a'' * p' → p' < a'' * q' →
          (∀ b q'' : ℕ, 0 < b → Nat.Prime q'' → q'' < b → ¬ (∃ t : ℕ, b * q'' = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r)) →
          ∀ b : ℕ, (∃ s : ℕ, b = a'' * s ∧ ∀ r : ℕ, Nat.Prime r → r ∣ s → a'' < r) →
            (∃ w : ℕ, a'' * p' * q' = b * w ∧ ∀ r : ℕ, Nat.Prime r → r ∣ w → b < r) →
            b = a'' ∨ b = a'' * p' * q') →
        (((Finset.Icc (a'+1) N').filter (fun p => Nat.Prime p ∧ a' * p ≤ N')).image (fun p => a' * p)
          ∪ (((Finset.Icc (a'+1) N') ×ˢ (Finset.Icc (a'+1) N')).filter
              (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a' * (pq.1 * pq.2) ≤ N')).image
              (fun pq => a' * pq.1 * pq.2))
          ⊆ (Finset.Icc 1 N').filter (fun n => π' n = a')) →
      (Finset.Icc 1 N).filter (fun n => π n = a) =
        ((Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N)).image (fun p => a * p)
        ∪ (((Finset.Icc (a+1) N) ×ˢ (Finset.Icc (a+1) N)).filter
            (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 ≤ pq.2 ∧ a * (pq.1 * pq.2) ≤ N)).image
            (fun pq => a * pq.1 * pq.2) := by
  intro π N a hN4 ha hπ1 hax hsound hmax hsandwich hlemma27 hB1 hB2 hsubfact huniqapq hdichotomy hsub_thm hsup_thm
  have hsub := hsub_thm π N a hN4 ha hπ1 hax hsound hdichotomy
  have hsup := hsup_thm π N a hN4 ha hax hmax hsound hsandwich hlemma27 hB1 hB2 hsubfact huniqapq
  exact Finset.Subset.antisymm hsub hsup

end Erdos858
