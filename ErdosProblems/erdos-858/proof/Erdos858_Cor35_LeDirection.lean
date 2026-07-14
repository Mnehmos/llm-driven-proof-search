/-
Erdős Problem #858 — Corollary 3.5, the ≤ direction of the max-closure duality.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Corollary 3.5 / Proposition 3.4 consequence.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode c78c33ce-ac2c-43d5-b77c-cd776246affc,
problem_version_id 779b78c0-578e-4d37-983d-6477737dbfda.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash dd521e98…

This ASSEMBLES the separately-verified §3 max-closure components (each a
kernel-verified lemma of this campaign, taken here as hypotheses) into the hard
direction of the reduction: every admissible ⪯-antichain B ⊆ [1,N] has weight
Σ_{n∈B} 1/n ≤ S_N(K). Since M(N) is the maximum of that weight over admissible
antichains, this is exactly M(N) ≤ S_N(K).

The four hypotheses are the verified components:
  • hstop  — the exchange-free stopping-set construction (Erdos858_StoppingSetConstruction):
             every ⪯-antichain B (1∉B) has a continuation set D with B ⊆ ∂D.
  • h34    — Proposition 3.4 (Erdos858_Prop34_MaxClosureIdentity):
             Σ_{n∈∂D} 1/n = 1 + Σ_{a∈D} q_N(a).
  • hopt   — the Corollary 3.5 optimization inequality (Erdos858_Cor35_OptimizationInequality):
             Σ_{a∈D} q_N ≤ Σ_{a∈[1,K]} q_N.
  • hS     — the frontier value S = 1 + Σ_{a∈[1,K]} q_N (Erdos858_FrontierSweep*, Prop 3.2).

Proof: if 1 ∈ B then B = {1} (since 1 ⪯ everything and B is an antichain), so
w(B) = 1 ≤ S; otherwise the stopping-set gives D with B ⊆ ∂D, whence
w(B) ≤ w(∂D) [subset, weights ≥ 0] = 1 + Σ_D q_N [h34] ≤ 1 + Σ_{[1,K]} q_N [hopt]
= S [hS]. Together with the ≥ direction (A_N(K) = ∂[1,K] achieves S_N(K)) this is
Corollary 3.5, M(N) = S_N(K), modulo packaging M(N) as a `Finset.max'` over the
admissible antichains and discharging these hypotheses with the verified lemmas.
-/
import Mathlib

namespace Erdos858

/-- Corollary 3.5, ≤ direction: assembling the verified max-closure components,
every admissible `⪯`-antichain `B ⊆ [1,N]` has `Σ_{n∈B} 1/n ≤ S` (`= S_N(K)`),
i.e. `M(N) ≤ S_N(K)`. -/
theorem cor35_le_direction :
    ∀ (π : ℕ → ℕ) (q : ℕ → ℚ) (N K : ℕ) (S : ℚ),
      (∀ B : Finset ℕ, (∀ x y : ℕ, x ∈ B → y ∈ B → (∃ t : ℕ, y = x * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → x < p) → x = y) →
        B ⊆ Finset.Icc 1 N → 1 ∉ B →
        ∃ D : Finset ℕ, 1 ∈ D ∧ (∀ a ∈ D, 2 ≤ a → π a ∈ D) ∧ D ⊆ Finset.Icc 1 N ∧
          B ⊆ (Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D)) →
      (∀ D : Finset ℕ, (∀ a ∈ D, 2 ≤ a → π a ∈ D) → D ⊆ Finset.Icc 1 N → 1 ∈ D →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D), (1:ℚ)/(n:ℚ)) = 1 + ∑ a ∈ D, q a) →
      (∀ D : Finset ℕ, D ⊆ Finset.Icc 1 N → (∑ a ∈ D, q a) ≤ ∑ a ∈ Finset.Icc 1 K, q a) →
      (1 + ∑ a ∈ Finset.Icc 1 K, q a = S) → 1 ≤ S →
      ∀ B : Finset ℕ, (∀ x y : ℕ, x ∈ B → y ∈ B → (∃ t : ℕ, y = x * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → x < p) → x = y) →
        B ⊆ Finset.Icc 1 N → (∑ n ∈ B, (1:ℚ)/(n:ℚ)) ≤ S := by
  intro π q N K S hstop h34 hopt hS hSge1 B hAnti hBsub
  by_cases h1 : 1 ∈ B
  · have hBsingle : B ⊆ ({1} : Finset ℕ) := by
      intro b hb
      have hb1 : (1:ℕ) = b := hAnti 1 b h1 hb ⟨b, (one_mul b).symm, fun p hp _ => hp.one_lt⟩
      simp only [Finset.mem_singleton]; omega
    have hle : (∑ n ∈ B, (1:ℚ)/(n:ℚ)) ≤ ∑ n ∈ ({1}:Finset ℕ), (1:ℚ)/(n:ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBsingle (fun n _ _ => by positivity)
    have h1eq : (∑ n ∈ ({1}:Finset ℕ), (1:ℚ)/(n:ℚ)) = 1 := by simp
    rw [h1eq] at hle
    linarith
  · obtain ⟨D, hD1, hDclosed, hDsub, hBsubD⟩ := hstop B hAnti hBsub h1
    have hle1 : (∑ n ∈ B, (1:ℚ)/(n:ℚ)) ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ∉ D ∧ π n ∈ D), (1:ℚ)/(n:ℚ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBsubD (fun n _ _ => by positivity)
    rw [h34 D hDclosed hDsub hD1] at hle1
    have hoptD := hopt D hDsub
    linarith

end Erdos858
