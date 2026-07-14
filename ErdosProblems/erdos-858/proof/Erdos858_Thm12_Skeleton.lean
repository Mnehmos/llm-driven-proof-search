/-
Erdős Problem #858 — Theorem 1.2 assembly skeleton: the conditional composition
that turns the verified frontier reduction plus the (open) frontier asymptotic law
into the headline asymptotic constant.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for Erdős
problem #858", Theorem 1.2.)

Theorem 1.2 states
    M(N) = (c₂ + o(1)) · log N,
where c₂ = 0.6187712… is the sharp asymptotic constant. The paper's proof
assembles this from exactly two results:
  • Corollary 3.5  —  M(N) = S_N(K*(N))                (KERNEL-VERIFIED here:
        Erdos858_Cor35_MaxEq / Cor35 family — the exact frontier reduction of the
        maximization to the frontier value S_N at the optimal cutoff K*(N)).
  • Theorem 5.8    —  S_N(K*(N)) = (c₂ + o(1)) · log N (NOT formalized — this is
        the analytic wall: the c₂ asymptotic of the frontier value, resting on the
        sharp Mertens constant, Φ, and the localization c₂ = 1/2 + ∫_{α₂}^{1/2}(1−Φ)).

This snapshot is the trivial-but-faithful bookkeeping composition only. Writing
MN = M(N), SN = S_N(K*(N)), L = log N, e = o(1) (the error term), and c2 = c₂:
Corollary 3.5 supplies `MN = SN`, Theorem 5.8 supplies `SN = (c2 + e) · L`, and
transitivity of equality yields `MN = (c2 + e) · L`. That is Theorem 1.2.

HONESTY BOUNDARY. The entire mathematical substance — Theorem 5.8, the c₂
asymptotic of the frontier value — is quarantined into the hypothesis
`SN = (c2 + e) * L` and is deliberately NOT proved here. This atom is only the glue
recording that Cor 3.5 (verified) ⨾ Thm 5.8 (the §5 analytic wall) ⟹ Thm 1.2. No
Mathlib lemma beyond `Eq.trans` participates; nothing in this file can be mistaken
for a proof of the asymptotic constant. The natural-number parameter `N` is retained
to mirror the paper's indexing by N.

Kernel-verified via the proofsearch MCP:
  episode 8fc1c70b-12c5-44d0-814b-cb47af2d1678,
  problem_version_id e8f8aecb-4f4e-4715-91b1-24bb5a963054.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 39ac7284c91f57a7cb4a513830b5bd24a6864591befc2282f5931bb8ed5e4245.

Lean note: `intro` the natural-number index and the five reals plus the two
equality hypotheses `h1 : MN = SN` (Cor 3.5) and `h2 : SN = (c2 + e) * L` (Thm 5.8);
then `rw [h1, h2]` rewrites the goal `MN = (c2 + e) * L` to `(c2 + e) * L = (c2 + e) * L`,
closed by `rfl`. Equivalently `exact h1.trans h2`.
-/
import Mathlib

namespace Erdos858

/-- Theorem 1.2 assembly skeleton. For any index `N : ℕ` and reals
`MN, SN, c2, e, L`, if `MN = SN` (Corollary 3.5: `M(N) = S_N(K*(N))`, verified)
and `SN = (c2 + e) * L` (Theorem 5.8: `S_N(K*(N)) = (c₂ + o(1)) · log N`, the open
analytic frontier law), then `MN = (c2 + e) * L` (Theorem 1.2:
`M(N) = (c₂ + o(1)) · log N`). Pure transitivity of equality; the analytic content
lives entirely in the second hypothesis. -/
theorem erdos858_thm12_skeleton :
    ∀ (N : ℕ) (MN SN c2 e L : ℝ),
      MN = SN → SN = (c2 + e) * L → MN = (c2 + e) * L := by
  intro N MN SN c2 e L h1 h2
  rw [h1, h2]

end Erdos858
