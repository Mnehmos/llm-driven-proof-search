/-
Erdős problem #858 — Chojecki 2026, §4.4, Theorem 4.7 (sign of the frontier
increment) — initial-segment / downward-closed core.

Atom: sec47_sign_theorem
Campaign: erdos-858

Paper statement (Theorem 4.7): "For every N ≥ 2 there exists an integer K(N)
such that R_N(a) > 1 for 1 ≤ a ≤ K(N) and R_N(a) ≤ 1 for a > K(N)." Here
R_N(a) := a·C_N(a), C_N(a) := Σ_{π(n)=a} 1/n. Equivalently the positivity set
{a : R_N(a) > 1} is always an initial segment of {1,…,N} — the reduction on
which Theorem 1.1 (M(N) = M_fr(N)) hinges (see §3, Cor 3.5).

This atom isolates the LOGICAL CORE of Theorem 4.7 as a conditional-assembly
lemma: the downward-closure (initial-segment) property of {a : R_N a > 1},
taking as hypotheses the two ingredients the paper proves separately. With
L := ⌊N^{1/4}⌋:
  hlow  : ∀ a, 1 ≤ a → a ≤ L → 1 < RN a
          — R_N > 1 on the small+low range [1,L]; the paper's Prop 4.1
            (computer-assisted small thresholds τ(a), 1 ≤ a ≤ 19, strictly
            increasing) together with Cor 4.4 (prime-harmonic lower bound
            q_N(a) > 0 on 20 ≤ a ≤ N^{1/4}).
  hmono : ∀ a b, L ≤ a → a ≤ b → RN b ≤ RN a
          — R_N nonincreasing on the upper layer [L,∞); the paper's
            Proposition 4.6, kernel-verified in this campaign
            (prop46_PN_monotone, prop46_QN_monotone).
Conclusion: {a : RN a > 1} is downward-closed, i.e.
  ∀ a b, 1 ≤ b → b ≤ a → 1 < RN a → 1 < RN b.
A downward-closed subset of ℕ with a witness at every small value is exactly an
initial segment; this is the "initial segment" content of the sign theorem.

Proof: case split on b ≤ L. If b ≤ L, hlow gives 1 < RN b directly. Otherwise
L < b ≤ a, so hmono b a gives RN a ≤ RN b, and 1 < RN a transports down to
1 < RN b by linarith.

Provenance:
  problem_version_id  : 171fd0d2-a28f-4cd2-b417-e7c5d5fbc5ac
  root_statement_hash : 0ef090b6791c8cbfd79d3a9175c93da7790d9fd19963098fbeec4cc4c3f4742d
  episode_id          : 4c7c9209-754b-44f2-970a-6af13c55f1d6
  outcome             : kernel_verified (termination_reason = root_proved, 1 submission)
  toolchain           : leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  fidelity_status     : attested (unsafe_dev_attestation=true — not a certified review)
-/
import Mathlib

namespace Erdos858

theorem erdos858_sec47_sign_theorem :
    ∀ (RN : ℕ → ℝ) (L : ℕ),
      (∀ a : ℕ, 1 ≤ a → a ≤ L → 1 < RN a) →
      (∀ a b : ℕ, L ≤ a → a ≤ b → RN b ≤ RN a) →
      (∀ a b : ℕ, 1 ≤ b → b ≤ a → 1 < RN a → 1 < RN b) := by
  intro RN L hlow hmono a b hb1 hba hRa
  by_cases hbL : b ≤ L
  · exact hlow b hb1 hbL
  · push_neg at hbL
    have hxa := hmono b a hbL.le hba
    linarith

end Erdos858
