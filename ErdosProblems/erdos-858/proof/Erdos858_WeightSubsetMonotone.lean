/-
  Erdős problem #858 — weight subset-monotonicity glue lemma
  Paper ref: Chojecki 2026, "weight subset monotonicity glue"

  The reciprocal weight w(B) = Σ_{n∈B} 1/n is monotone under Finset inclusion:
  since every term 1/n ≥ 0, dropping to a subset can only decrease the sum.
  Used in the ≤ direction of the max-closure duality (an antichain B ⊆ ∂D
  gives w(B) ≤ w(∂D)) toward Corollary 3.5.

  problem_version_id : 2572333e-ae93-4385-91a5-414c070018da
  episode_id         : 937e3f78-221b-465f-bc27-5fc64781bc9b
  outcome            : kernel_verified (root_proved)
  toolchain          : leanprover/lean4:v4.32.0-rc1,
                       mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  root_statement_hash: 4f73b9c6893e633f31fc7f871507532d11afe7f9d97a12af894ed3b0bd765c6d
-/
import Mathlib

namespace Erdos858

theorem weight_subset_monotone :
    ∀ (B C : Finset ℕ), B ⊆ C → (∑ n ∈ B, (1:ℚ)/(n:ℚ)) ≤ ∑ n ∈ C, (1:ℚ)/(n:ℚ) := by
  intro B C hsub
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)

end Erdos858
