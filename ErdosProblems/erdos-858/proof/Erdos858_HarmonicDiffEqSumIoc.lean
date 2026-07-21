/-
Erdős Problem #858 — §5.4 log-harmonic transfer, connector lemma (Chojecki 2026).

`harmonic difference equals Ioc sum`: for `m ≤ n`, `harmonic n − harmonic m =
Σ_{a∈Ioc m n} 1/a` (as reals). This is the connector lemma identifying a
log-harmonic block's mass `Σ_{a∈block j} 1/a` with the harmonic difference
`harmonic(e_{j+1}) − harmonic(e_j)` used throughout the log-harmonic transfer
(#98–#106): it closes the gap between #99's `Tendsto`-form limit statement
(which only speaks about the LIMIT of `(harmonic⌊N^t⌋−harmonic⌊N^s⌋)/log N`)
and the EXACT finite sum needed by the concrete instantiation of #105's
weighted pointwise-to-sum bound.

Proof: `Nat.le_induction` on `n ≥ m`. Base case `n = m`: both sides are `0`
(`Finset.Ioc m m = ∅`), closed by `simp`. Successor case: `harmonic_succ` gives
the recursive step for `harmonic`, `Finset.sum_Ioc_succ_top` gives the matching
recursive step for the sum, and the two `+1/(n+1)` terms cancel against the
inductive hypothesis via `linarith`. Elementary, no PNT — a 2-block telescoping
special case reusing the same consecutive-interval-sum pattern as the generic
partition identity #103.

Kernel-verified via the proofsearch MCP:
  episode fb52afe8-9bdc-45f3-9bc4-bcadbc99f40e,
  problem_version_id 689aa9d6-6fd6-4cd0-bf05-aae97f189186.
Outcome: kernel_verified / root_kernel_verified (3rd submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 71637c00539c31fa2489b0cf892e1c5b261e74371ab0966a2a0fba72c7be984f.

**Lean lesson (cast pitfall, distinct from the have-block/show-from lessons)**:
`(n:ℝ)+1` (cast-then-add) and `((n+1:ℕ):ℝ)` (add-then-cast) PRINT IDENTICALLY
in diagnostics (both as `↑(n+1)`-looking output) but are NOT syntactically /
defeq-equal terms — `exact_mod_cast` can silently fail to bridge them when
nested inside `⁻¹` or other operations, and the error's "actual vs expected"
types can look deceptively identical in the rendered diagnostic. Robust
pattern for casting a `*_succ`-style recursive lemma into a larger field:
(1) state a `have` with an EXPLICIT inner type ascription matching the source
lemma's native shape exactly, so `exact_mod_cast` only wraps and never
rearranges; (2) `push_cast` to canonically normalize that `have` AND any
sibling fact (e.g. a `Finset.sum_*_succ_top` result) into the SAME distributed
form; (3) if a `⁻¹` vs `1/x` mismatch remains, `rw [← one_div]` (or `one_div`)
to force one shared representation before the final `rw`/`linarith`.
-/
import Mathlib

namespace Erdos858

/-- Log-harmonic transfer connector lemma (harmonic difference = Ioc sum): for
`m ≤ n`, `harmonic n − harmonic m = Σ_{a∈Ioc m n} 1/a`. Identifies the abstract
block mass used in #99/#101/#102 with the exact finite sum needed by the
concrete instantiation. Proof: `Nat.le_induction` + `harmonic_succ` +
`Finset.sum_Ioc_succ_top`. -/
theorem erdos858_harmonic_diff_eq_sum_Ioc :
    ∀ m n : ℕ, m ≤ n →
      (harmonic n : ℝ) - (harmonic m : ℝ) = ∑ a ∈ Finset.Ioc m n, (1:ℝ) / (a:ℝ) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hcast : ((harmonic (n+1) : ℚ) : ℝ) = ((harmonic n : ℚ) : ℝ) + (((n+1:ℕ) : ℚ) : ℝ)⁻¹ := by exact_mod_cast harmonic_succ n
    push_cast at hcast
    rw [← one_div] at hcast
    have hsum := Finset.sum_Ioc_succ_top hn (fun a => (1:ℝ) / (a:ℝ))
    push_cast at hsum
    rw [hsum, hcast]
    linarith [ih]

end Erdos858
