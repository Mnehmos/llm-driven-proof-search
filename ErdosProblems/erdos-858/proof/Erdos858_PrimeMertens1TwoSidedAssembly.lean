/-
Erdős Problem #858 — §5 analytic foundation: PRIME-SUM Mertens' first theorem,
TWO-SIDED (O(1)) assembly. Conditional assembly of the prime-sum two-sided bound
Σ_{p≤N}(log p)/p = log N + O(1) from the campaign's verified von Mangoldt log-sum
two-sided bound (#48) plus a prime-power tail bound.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5 quantitative-Mertens / exact-constant c₂ development.)

Byte-faithful snapshot of the kernel-verified root theorem from the proofsearch
MCP episode df3666f0-4e96-4811-87f8-6f1ec56b3291,
problem_version_id 3c75e0ba-e48e-4b9b-bcdc-4e72ddf03c86.
Outcome: kernel_verified / root_proved (root_kernel_verified).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash fc18505f75fe2956c5a9fb3ba64662f60a0ec72c476c52c3c27c52869349810e.

Content: with Sl := Σ_{d≤N} Λ(d)/d the von Mangoldt log-sum, Sp := Σ_{p≤N}(log p)/p
the prime sum, and T := Sl − Sp the proper-prime-power tail, this transports the
campaign-verified von Mangoldt TWO-SIDED bound (#48, Σ_{d≤N} Λ(d)/d = log N + O(1),
i.e. |Sl − log N| ≤ C) into a two-sided bound on the prime sum, TAKEN AS
HYPOTHESES:
  • decomposition:      Sl = Sp + T;
  • tail bounds:        0 ≤ T   and   T ≤ C';
  • von Mangoldt #48:   |Sl − Real.log N| ≤ C.
The assembly concludes  |Sp − Real.log N| ≤ C + C', i.e. Σ_{p≤N}(log p)/p =
log N + O(1), the PRIME-sum two-sided Mertens' first theorem.

Proof: Sp − log N = (Sl − log N) − T. The upper side is ≤ C ≤ C + C' (uses
T ≥ 0, and C' ≥ T ≥ 0 so C' ≥ 0); the lower side is ≥ −C − C' (uses
Sl − log N ≥ −C and T ≤ C'). Discharged by `abs_le` (unfolding both absolute
values into two-sided bounds) + `obtain` (splitting the rewritten conjunction so
`linarith` sees both bounds — `linarith` does not auto-split conjunctions) +
`constructor <;> linarith`, with `Real.log ↑N` an opaque atom. NOTE: `abs_add`
is not an identifier in this Mathlib pin, hence the `abs_le` + `linarith` route.
CONDITIONAL assembly over the verified von Mangoldt two-sided bound (#48) and the
prime-power tail bound.
-/
import Mathlib

namespace Erdos858

/-- Erdős #858, PRIME-SUM Mertens-1 TWO-SIDED (O(1)) assembly. Given the tail
decomposition `Sl = Sp + T`, the tail bounds `0 ≤ T`, `T ≤ C'`, and the
campaign-verified von Mangoldt two-sided bound `|Sl − log N| ≤ C` (#48), the
prime sum satisfies `|Sp − log N| ≤ C + C'`, i.e. `Σ_{p≤N}(log p)/p = log N + O(1)`. -/
theorem erdos858_prime_mertens1_twosided_assembly :
    ∀ (N : ℕ) (Sp Sl T C C' : ℝ), Sl = Sp + T → 0 ≤ T → T ≤ C' →
      |Sl - Real.log (N : ℝ)| ≤ C → |Sp - Real.log (N : ℝ)| ≤ C + C' := by
  intro N Sp Sl T C C' hSl hT0 hTC hC
  rw [abs_le] at hC ⊢
  obtain ⟨hCl, hCr⟩ := hC
  constructor <;> linarith

end Erdos858
