/-
Erdős Problem #858 — §5, toward the sharp constant c₂: two-sided Mertens' first
theorem for the von Mangoldt sum (conditional assembly).
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", §5.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 79ec2bb3-2a1b-4db6-b781-7002106071b4,
problem_version_id c97ced6c-c9f2-4925-8009-b854a11a2b07.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash b08b5716…

Write S = Σ_{d≤N} Λ(d)/d, P = Σ_{d≤N} Λ(d)⌊N/d⌋, F = log(N!). The campaign's
verified building blocks give the three hypotheses:
  • F = P            (from #41 Σ log n = Σ_d Λ(d)⌊N/d⌋ and #43 Σ log n = log N!);
  • |N·S − P| ≤ ψ    (fractional-part step: |N·Σ Λ(d)/d − Σ Λ(d)⌊N/d⌋| ≤ Σ Λ(d) = ψ(N));
  • |F − (N log N − N)| ≤ E   (Stirling, two-sided, error E = O(log N)).
This theorem concludes |N·S − (N log N − N)| ≤ ψ + E, i.e. Σ_{d≤N} Λ(d)/d =
log N + O(1) — **Mertens' first theorem for the von Mangoldt sum, both directions**.
It complements the verified one-directional lower bound
(Erdos858_Mertens1_LowerAssembly, Σ Λ(d)/d ≥ log N − 1). Dropping the prime-power
tail (Σ_{p^k, k≥2} (log p)/p^k convergent) then gives Σ_{p≤x}(log p)/p = log x +
O(1), and Abel summation the sharp Σ 1/p = loglog x + M + o(1) that fixes c₂.

Assembled conditionally (taking the verified building-block conclusions as
hypotheses — the campaign's cor35_max_eq technique, since problem_versions cannot
cross-reference lemmas). Lean note: `abs_add` is not the identifier in this pin;
the triangle inequality is done via `rw [abs_le]` componentwise + `linarith`.
-/
import Mathlib

namespace Erdos858

/-- Two-sided Mertens' first theorem for the von Mangoldt sum (conditional): from
`F = P`, `|N·S − P| ≤ ψ`, and the two-sided Stirling bound `|F − (N log N − N)| ≤ E`,
conclude `|N·S − (N log N − N)| ≤ ψ + E`, i.e. `Σ_{d≤N} Λ(d)/d = log N + O(1)`. -/
theorem erdos858_mertens1_two_sided :
    ∀ (N : ℕ) (S P F psi E : ℝ),
      0 < N →
      F = P →
      |(N : ℝ) * S - P| ≤ psi →
      |F - ((N : ℝ) * Real.log N - (N : ℝ))| ≤ E →
      |(N : ℝ) * S - ((N : ℝ) * Real.log N - (N : ℝ))| ≤ psi + E := by
  intro N S P F psi E hN hFP hfrac hstir
  rw [abs_le] at hfrac hstir ⊢
  refine ⟨?_, ?_⟩ <;> linarith [hfrac.1, hfrac.2, hstir.1, hstir.2]

end Erdos858
