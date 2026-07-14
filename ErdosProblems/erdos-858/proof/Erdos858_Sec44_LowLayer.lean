/-
Erdős problem #858 — Chojecki 2026, §4.4, Corollary 4.4 (low-layer positivity),
conditional-assembly composition atom.

Atom: erdos858_sec44_low_layer
Campaign: erdos-858

Statement formalized: for real quantities `RNa`, `primeIntervalSum`,
`bigIntervalSum`,
  1 < primeIntervalSum →
  primeIntervalSum ≤ bigIntervalSum →
  bigIntervalSum ≤ RNa →
  1 < RNa.

This is the clean composition step of the paper's proof of Corollary 4.4 in the
case `a ≥ 20`. The three hypotheses are the three inputs the paper chains, with
the sums modeled as opaque reals:
  • `1 < primeIntervalSum`  is Lemma 4.3: for every integer `a ≥ 20`,
      Σ_{a<p≤a^3} 1/p > 1.
  • `primeIntervalSum ≤ bigIntervalSum` is the interval monotonicity of the
      prime-reciprocal sum: since `a ≤ N^{1/4}` gives `a^3 ≤ N/a`, the small
      range (a, a^3] is contained in the big range (a, N/a], and all summands
      1/p are nonnegative, so Σ_{a<p≤a^3} 1/p ≤ Σ_{a<p≤N/a} 1/p.
  • `bigIntervalSum ≤ RNa`  is the prime-child lower bound (Lemma 2.7 /
      prime-child lemma, π(a·p)=a): every prime p with a < p ≤ N/a contributes
      the child a·p, each adding 1/p to R_N(a), so
      R_N(a) ≥ Σ_{a<p≤N/a} 1/p.
The conclusion `1 < RNa` is R_N(a) > 1, the low-layer sign statement feeding the
§4.7 sign theorem (initial-segment positivity ⇒ Theorem 1.1 M(N)=M_fr(N)).

Conditional-assembly note: this atom takes the three analytic/combinatorial
inputs as hypotheses and proves only their composition. It is a legitimate
campaign technique (cf. cor35_max_eq, #73): the paper's remaining §4.3 (Lemma
4.3 bound), interval monotonicity, and prime-child lower bound are discharged in
their own atoms; this one certifies that once all three hold, R_N(a) > 1.

Proof idea: pure real linear-order transitivity — intro the reals and
hypotheses, then `linarith` chains 1 < primeIntervalSum ≤ bigIntervalSum ≤ RNa.

Provenance:
  problem_version_id : 4123f837-7d54-45f7-918f-3f89e36d2481
  root_statement_hash : b674b6d11db0ca1d59d2ae6c8c6dfc4f551308568e225d081da6e7184bd751d1
  episode_id          : 355795f4-f9d0-440b-be2e-f9408ccf2fd9
  outcome             : kernel_verified (termination_reason = root_proved, 1 submission)
  toolchain           : leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56
  fidelity_status     : attested (unsafe_dev_attestation=true — not a certified review)
-/
import Mathlib

namespace Erdos858

theorem erdos858_sec44_low_layer :
    ∀ RNa primeIntervalSum bigIntervalSum : ℝ,
      1 < primeIntervalSum →
      primeIntervalSum ≤ bigIntervalSum →
      bigIntervalSum ≤ RNa →
      1 < RNa := by
  intro RNa primeIntervalSum bigIntervalSum h43 hmono hchild
  linarith

end Erdos858
