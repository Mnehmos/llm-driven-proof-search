/-
Erdős Problem #858 — frontier fact: S_N(N)=0, the top cutoff is empty (Chojecki 2026).

The frontier at cutoff `K=N` is empty: `A_N(N) = {n∈[1,N] : π n≤N ∧ N<n} = ∅`.
Immediate from the range restriction (`n≤N` contradicts `N<n`), independent of
any π-axioms. The mirror image of the already-verified `frontier_base_zero`
(`S_N(0)=1`, `Erdos858_FrontierBaseZero.lean`) — the blocking lemma for both
routes to the parent-counting identity `Σ_a C_N(a) = H_N−1` feeding the Prop 5.1
identity (Theorem 1.2 assembly, atom A2): via `frontier_sweep_telescope`/
`erdos858_thm12_telescoping` (`S_N(N)−S_N(0) = Σ increments`) or via
`prop34_max_closure_identity` at `D=Icc 1 N` (downward-closure via
`cor35_initial_segment_closed`).

Kernel-verified via the proofsearch MCP:
  episode 36b02834-bbb7-4651-9423-7a1c047f72e3,
  problem_version_id 4902a2f8-23af-4804-81a9-c61facb46684.
Outcome: kernel_verified / root_kernel_verified (4th submission — see the
`Erdos858_FrontierFact_CN0AboveSqrt.lean` header for the general lessons banked
this round; this specific proof's earlier rounds hit `rintro`'s auto-flattening
binding names unpredictably against a `(A∧B)∧(C∧D)`-shaped hypothesis, and
`omega` failing to close a non-arithmetic goal (`n∈∅`) directly even from a
contradictory context — the eventual FIX abandoned `ext`/`constructor`/`rintro`
entirely in favor of the much shorter `rw [Finset.filter_eq_empty_iff]; intro n
hn; rw [Finset.mem_Icc] at hn; omega`, which incidentally CONFIRMS
`Finset.filter_eq_empty_iff` genuinely exists in this pin — the earlier
`Erdos858_FrontierFact_CN0AboveSqrt.lean` struggles with it were structural
(scope leaks), not a missing-lemma issue).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 4287c14c9b7de458cc20329a319f26cdb0d59025b5398d50b632c2d7452004e1.

**Lean lesson**: `omega` does NOT auto-close non-arithmetic goals (like Finset
membership) from contradictory arithmetic hypotheses — it only proves goals that
are themselves arithmetic. When the target after unfolding IS purely arithmetic
(e.g. via `Finset.filter_eq_empty_iff` turning the goal into `∀x∈s,¬P x` with `P`
arithmetic), a single `omega` closes it directly — prefer reshaping the goal to
be arithmetic-shaped over bridging a non-arithmetic goal with `absurd`/`.elim`.
-/
import Mathlib

namespace Erdos858

/-- Frontier fact: the top-cutoff frontier `A_N(N)` is empty — immediate from
the range restriction `n≤N` vs `N<n`. The mirror of `frontier_base_zero`,
blocking lemma for the parent-counting identity feeding A2. -/
theorem erdos858_frontier_top_zero :
    ∀ (π : ℕ → ℕ) (N : ℕ),
      (Finset.Icc 1 N).filter (fun n => π n ≤ N ∧ N < n) = ∅ := by
  intro π N
  rw [Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_Icc] at hn
  omega

end Erdos858
