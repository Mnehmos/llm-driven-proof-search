/-
Erdős Problem #858 — Lemma 4.5 connection, disjointness (Chojecki 2026).

The single-prime-child form `a·p` and the semiprime-child form `a·p'·q'`
never coincide, for any primes `p,p',q'`. Needed for the future
`C_N(a)=R_N(a)/a` Finset-bijection (Lemma 4.5): justifies splitting
`Σ_{n:π n=a}1/n` as a DISJOINT union of the single-prime piece
(`lemma27_pi_ap_full`) and the semiprime piece (`lemma45_pi_apq_full`),
given the forward classification (`lemma45_forward_classification`,
`Erdos858_Lemma45_ForwardClassification.lean`) shows every such `n` is one
or the other.

Proof: cancel `a` from `a*p=a*p'*q'` to get `p=p'*q'`; since `p` is prime,
`p'∣p` forces `p'=1` (impossible, `p'` prime) or `p'=p`; the latter forces
(cancelling `p`) `q'=1` (impossible, `q'` prime). Term-mode `Or.elim`
avoiding bullets.

Kernel-verified via the proofsearch MCP:
  episode f94165b0-58ad-4431-972e-d0db911375cd,
  problem_version_id b78fd0ec-230f-4b77-9709-94348876aec9.
Outcome: kernel_verified / root_kernel_verified (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bc37509763106677b1443c1a93ce743e2aa32ec533687c604a3c4729867d1f89.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 disjointness: `a·p ≠ a·p'·q'` for any primes `p,p',q'`. -/
theorem lemma45_apq_disjoint_from_ap :
    ∀ a p p' q' : ℕ, 1 ≤ a → Nat.Prime p → Nat.Prime p' → Nat.Prime q' → a * p ≠ a * p' * q' := by
  intro a p p' q' ha hp hp' hq' heq
  have heq2 : a*p = a*(p'*q') := (by rw [heq]; ring)
  have hpp'q' : p = p'*q' := Nat.eq_of_mul_eq_mul_left ha heq2
  have hp'dvd : p' ∣ p := ⟨q', hpp'q'⟩
  exact (hp.eq_one_or_self_of_dvd p' hp'dvd).elim (fun h1 => absurd h1 hp'.ne_one) (fun h1 => by rw [h1] at hpp'q'; exact absurd (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hpp'q')).symm hq'.ne_one)

end Erdos858
