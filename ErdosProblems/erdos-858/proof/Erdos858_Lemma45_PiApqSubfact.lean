/-
Erdős Problem #858 — Lemma 4.5, the π(a·p·q) = a sub-fact.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Lemma 4.5.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 55f6df39-7e11-4ad3-a33a-9e2d236c7483,
problem_version_id cbd049d5-a5d3-4a8b-873b-c673f2fdcbc0.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash c4df4340…

In Lemma 4.5 the paper shows a semiprime child a·p·q (a > N^{1/4}, a < p ≤ q
prime, apq ≤ N) has parent a, not a·p: because a·p > a² > N^{1/2} and
q ≤ N/(a·p) < N^{1/2} < a·p, one has q < a·p, and a ⪯-step from a·p must
multiply by a factor all of whose prime factors exceed a·p.

Here that impossibility is formalized in clean general form: for any base b > 0
and prime q < b, `b ⋠ b·q` — there is NO t with b·q = b·t and every prime factor
of t exceeding b. Proof: cancelling b forces t = q, and then the prime q ∣ q
would require b < q, contradicting q < b. Specialized to b = a·p this is exactly
why a·p is not a proper ancestor of a·p·q, giving π(a·p·q) = a and hence the
`R_N(a) = P_N(a) + Q_N(a)` split in the upper layer.
-/
import Mathlib

namespace Erdos858

/-- A `⪯`-step must multiply by a factor whose prime factors all exceed the
base: for `b > 0` and a prime `q < b`, there is no `t` with `b*q = b*t` and every
prime factor of `t` exceeding `b`. (I.e. `b ⋠ b*q`.) -/
theorem lemma45_pi_apq_subfact :
    ∀ b q : ℕ, 0 < b → Nat.Prime q → q < b →
      ¬ (∃ t : ℕ, b * q = b * t ∧ ∀ r : ℕ, Nat.Prime r → r ∣ t → b < r) := by
  intro b q hb hq hqb
  rintro ⟨t, heq, ht⟩
  have htq : q = t := Nat.eq_of_mul_eq_mul_left hb heq
  subst htq
  have hbq : b < q := ht q hq (dvd_refl q)
  omega

end Erdos858
