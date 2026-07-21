/-
Erdős Problem #858 — frontier fact hC0: C_N(a)=0 above √N (Chojecki 2026).

`C_N(a) = 0` for `a` with `N < a·a` (i.e. `a` above `√N`). Discharges the `hC0`
hypothesis of the Prop 5.1 identity (Theorem 1.2 assembly, atom A2,
`Erdos858_Thm12_A2_Prop51Identity.lean`).

Uses the already-verified `top_block_antichain` (`N<a·a, a<b, b≤N ⟹ ¬(a⪯b)`,
`Erdos858_TopBlockAntichain.lean`), taken as an explicit hypothesis since
problem_versions cannot cross-reference, combined with the standard abstract-π
axioms (`π 1=0`, `1≤π n<n` for `2≤n≤N`) and π-soundness (`π w ⪯ w` for `2≤w`, the
`hpi_anc`-style hypothesis already precedented in `Erdos858_StoppingSetConstruction.lean`).

Proof: for any `n∈[1,N]` with `π n = a`: if `n=1`, `π n=0` forces `a=0`,
contradicting `N<a·a` (which forces `a>0` — `N<0·0=0` is impossible for `ℕ`); if
`n≥2`, π-soundness gives `a⪯n` (via `π n=a`), and `a<n≤N` with `N<a·a` directly
contradicts `top_block_antichain`. So the filter set defining `C_N(a)` is empty.

Kernel-verified via the proofsearch MCP:
  episode 3ee8863c-a8e1-4e6f-ba0b-500905f3ea5b,
  problem_version_id 7bc2dd8a-65d3-4f7f-b561-fd95e76603f0.
Outcome: kernel_verified / root_kernel_verified (10th submission — see Lean
lessons below; the underlying mathematical content was correct from the first
attempt, all subsequent rounds fixed pure Lean-mechanics issues).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash e2c29049bc81345a766ae1715fd38a813da028ec957f3bee2b0eb156274cc5f7.

**Lean lessons (significant, banked for reuse)**:
(1) Neither `Finset.eq_empty_of_forall_not_mem` nor `Finset.eq_empty_iff_forall_not_mem`
    exist in this pin — for Finset-emptiness proofs, prefer `ext n; exact ⟨mp, mpr⟩`
    (term-mode Iff) over guessing a named characterization lemma.
(2) **Multiple bullets chained via `;` on ONE flattened line do NOT reliably
    transition between goals** — after `constructor` (or similar 2-goal-producing
    tactics), only the FIRST bullet's content executes correctly; the SECOND
    bullet sees a stale/wrong goal state ("No goals to be solved" or the second
    case left entirely unsolved). Bullets fundamentally rely on indentation-based
    boundaries that a flat `;`-chain can't express. **Fix: for a 2-way split
    (Iff, Or.elim, etc.) on a flattened line, use term-mode anonymous-constructor
    syntax (`⟨proof1, proof2⟩`) instead of tactic-mode `constructor`+bullets.**
(3) The "bare `:= by tac; swallows the chain" pitfall recurs at ANY nesting depth,
    not just the top level — a bare `have hn1' : n=1 := by omega` nested three
    `have`s deep, followed by more `;`-chain, swallows that chain exactly like a
    top-level one would. Parenthesize every `by`-block with more chain following,
    regardless of nesting depth.
(4) A misleading unrelated-looking error ("No applicable extensionality theorem
    for ℚ" on an `ext n` that should target a `Finset ℕ` goal) can be the SYMPTOM
    of a scope leak from unflattened newlines elsewhere in the same `have`-body,
    not a real lemma-applicability issue — don't over-trust the FIRST diagnostic
    entry's apparent target; it can be a generic "here's what didn't get proved"
    placeholder identical across differently-broken attempts.
(5) `Finset.not_mem_empty` is not the name in this pin — `(by simp)` closes
    `n ∉ (∅:Finset α)` without needing the exact lemma name.
-/
import Mathlib

namespace Erdos858

/-- Frontier fact hC0: `C_N(a) = 0` for `N < a·a` (`a` above `√N`). Via
`top_block_antichain` + the π-soundness/standard-axiom hypotheses: any
`n` with `π n = a` in range would force `a ⪯ n`, contradicting the antichain
fact once `a` exceeds `√N`. Discharges A2's hC0. -/
theorem erdos858_frontier_CN_zero_above_sqrt :
    ∀ (π : ℕ → ℕ) (N a : ℕ),
      π 1 = 0 →
      (∀ n : ℕ, 2 ≤ n → n ≤ N → 1 ≤ π n ∧ π n < n) →
      (∀ w : ℕ, 2 ≤ w → ∃ t : ℕ, w = π w * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → π w < p) →
      (∀ N' a' b' : ℕ, N' < a' * a' → a' < b' → b' ≤ N' →
        ¬ (∃ t : ℕ, b' = a' * t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → a' < p)) →
      N < a * a →
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => π n = a), (1:ℚ)/(n:ℚ)) = 0 := by
  intro π N a hπ1 hax hpi_anc htop hNa
  have hempty : (Finset.Icc 1 N).filter (fun n => π n = a) = ∅ := by ext n; exact ⟨(fun hn => by rw [Finset.mem_filter, Finset.mem_Icc] at hn; obtain ⟨⟨hn1, hnN⟩, hπna⟩ := hn; have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => by rw [h] at hNa; simp at hNa); have hn2 : 2 ≤ n := (by by_contra hlt; push_neg at hlt; have hn1' : n = 1 := (by omega); rw [hn1', hπ1] at hπna; omega); have han : a < n := (by rw [← hπna]; exact (hax n hn2 hnN).2); obtain ⟨t, hnt, hpt⟩ := hpi_anc n hn2; rw [hπna] at hnt hpt; exact ((htop N a n hNa han hnN) ⟨t, hnt, hpt⟩).elim), (fun hn => absurd hn (by simp))⟩
  simp only [hempty, Finset.sum_empty]

end Erdos858
