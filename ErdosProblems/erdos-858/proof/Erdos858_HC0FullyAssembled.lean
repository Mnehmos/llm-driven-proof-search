/-
Erdős Problem #858 — Theorem 1.2 assembly, FULLY-ASSEMBLED hC0 (Chojecki 2026).

Reduces A2's `hC0` hypothesis to genuinely primitive π-structure axioms:
`π 1=0`, the range axiom, π-soundness (`π w⪯w`), and `top_block_antichain`
(`Erdos858_TopBlockAntichain.lean` — a SELF-CONTAINED, hypothesis-free
number-theory fact about `⪯`, taken as an opaque hypothesis representing
its full theorem). Directly in ℝ — **no cast needed**, since the original
proof (`erdos858_frontier_CN_zero_above_sqrt`, #177,
`Erdos858_FrontierFact_CN0AboveSqrt.lean`) is pure Finset combinatorics
(showing the filter set is `∅`) with zero ring-specific arithmetic; it
works verbatim for any `AddCommMonoid` codomain, including `ℝ` directly.

Proof: verbatim `#177` proof body (renamed `hn1'` to `hn1prime` to avoid
prime-tick naming friction), stated directly with `(1:ℝ)/(n:ℝ)` summands.

Kernel-verified via the proofsearch MCP:
  episode 241d616b-983c-4e33-8bb8-5d94c1e36246,
  problem_version_id a32ba4ef-de5d-41eb-9808-2b616092901f.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 28ef87fa124f50fba00e741c39c73ae7c1c0cb7044c6f0b6152eee25a922292f.
-/
import Mathlib

namespace Erdos858

/-- Fully-assembled hC0: `C_N(a)=0` for `N<a·a`, directly in ℝ, needing only
`π 1=0` + range axiom + π-soundness + `top_block_antichain` (opaque, already
self-contained). -/
theorem erdos858_hC0_fully_assembled :
    ∀ (π : ℕ → ℕ) (N a : ℕ),
      π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ w : ℕ, 2 ≤ w → ∃ t : ℕ, w = π w * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → π w < p) →
      (∀ N' a' b' : ℕ, N' < a' * a' → a' < b' → b' ≤ N' →
        ¬ (∃ t : ℕ, b' = a' * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a' < p)) →
      N < a * a →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℝ)/(n:ℝ)) = 0 := by
  intro π N a hπ1 hax hpi_anc htop hNa
  have hempty : (Finset.Icc 1 N).filter (fun n => π n = a) = ∅ := by ext n; exact ⟨(fun hn => by rw [Finset.mem_filter, Finset.mem_Icc] at hn; obtain ⟨⟨hn1, hnN⟩, hπna⟩ := hn; have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => by rw [h] at hNa; simp at hNa); have hn2 : 2 ≤ n := (by by_contra hlt; push_neg at hlt; have hn1prime : n = 1 := (by omega); rw [hn1prime, hπ1] at hπna; omega); have han : a < n := (by rw [← hπna]; exact (hax n hn2 hnN).2); obtain ⟨t, hnt, hpt⟩ := hpi_anc n hn2; rw [hπna] at hnt hpt; exact ((htop N a n hNa han hnN) ⟨t, hnt, hpt⟩).elim), (fun hn => absurd hn (by simp))⟩
  simp only [hempty, Finset.sum_empty]

end Erdos858
