/-
Erdős problem #858 — Chojecki 2026, Remark 2.5 (Bellman form of the subtree recursion).

The subtree optimum F_N(a) = max(1/a, Σ_{b∈ch(a)} F_N(b)) rescales, via
V_N(a) := a · F_N(a), to the Bellman form V_N(a) = max(1, Σ_{b∈ch(a)} (a/b) · V_N(b)).
This file formalizes exactly that algebraic rescaling: given
F a = max(1/a, Σ_{b∈ch} F b) with a > 0 and every child b > 0, multiplying through by a
yields a · F a = max(1, Σ_{b∈ch} (a/b) · (b · F b)), where b · F b = V_N(b).

Math sketch:
  a · max(1/a, Σ) = max(a·(1/a), a·Σ) = max(1, a·Σ)  (since a > 0), and
  Σ_b (a/b)·(b·F b) = Σ_b a·F b = a·Σ_b F b            (since each b > 0),
exhibiting the optimal-stopping / Bellman structure of the tree optimization.

Provenance (verifier-backed, proofsearch MCP):
  problem_version_id : 1c5f2019-6e63-42fb-89b6-a53f8816618d
  episode_id         : 6c59fc46-acdf-49e4-bab5-31326433b14f
  root_statement_hash: 632e263bb39da200f6adfd59a5914cbdd3bce4c3e740e0c8911aa8fc0c576e9a
  outcome            : kernel_verified (root_proved)
  atom               : remark25_bellman_form
  toolchain          : leanprover/lean4:v4.32.0-rc1,
                       mathlib @ 360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
-/
import Mathlib

namespace Erdos858

theorem remark25_bellman_form :
    ∀ (F : ℕ → ℚ) (a : ℕ) (ch : Finset ℕ), 0 < a → (∀ b ∈ ch, 0 < b) →
      F a = max ((1:ℚ)/(a:ℚ)) (∑ b ∈ ch, F b) →
      (a:ℚ) * F a = max 1 (∑ b ∈ ch, (a:ℚ)/(b:ℚ) * ((b:ℚ) * F b)) := by
  intro F a ch ha hch hrec
  have ha0 : (0:ℚ) < (a:ℚ) := by exact_mod_cast ha
  rw [hrec, mul_max_of_nonneg _ _ (le_of_lt ha0)]
  congr 1
  · field_simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hb0 : (0:ℚ) < (b:ℚ) := by exact_mod_cast hch b hb
    field_simp

end Erdos858
