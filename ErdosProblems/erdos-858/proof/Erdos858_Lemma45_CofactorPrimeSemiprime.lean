/-
Erdős Problem #858 — Lemma 4.5 (prime–semiprime description), cofactor core.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Lemma 4.5.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 441292d0-af2d-496e-a74d-f5cd0a7695fd,
problem_version_id c3d8025c-c0ad-4e20-96fb-ad3acd67740b.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 7ce3fa75…

Paper statement: in the upper layer a > N^{1/4} (so N < a⁴), every child of a is
a·p or a·p·q with a < p ≤ q prime. The cofactor t = n/a satisfies t ≤ N/a < a³
and every prime factor of t exceeds a, hence t has at most two prime factors.
This is what makes R_N(a) = P_N(a) + Q_N(a) (Lemma 4.5) and drives the
upper-layer monotonicity (Prop 4.6) behind the sign theorem.

Here the arithmetic core is formalized without the tree: if `1 ≤ a`, `0 < t`,
`t < a³`, and every prime factor of `t` exceeds `a`, then
`Ω(t) = t.primeFactorsList.length ≤ 2` — i.e., for `t > 1`, `t` is prime or a
product of two primes. Proof: each prime factor is `≥ a+1`, so by
`List.pow_card_le_prod`, `(a+1)^Ω(t) ≤ ∏ primeFactorsList t = t < a³ < (a+1)³`,
forcing `Ω(t) ≤ 2`.
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5 cofactor core. A cofactor `t < a³` all of whose prime factors
exceed `a` has at most two prime factors (`Ω(t) ≤ 2`): it is `1`, a prime, or a
product of two primes. -/
theorem lemma45_cofactor_prime_semiprime :
    ∀ a t : ℕ, 1 ≤ a → 0 < t → t < a ^ 3 →
      (∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
      t.primeFactorsList.length ≤ 2 := by
  intro a t ha htpos htlt hprimes
  by_contra hlen
  push_neg at hlen
  have ht_ne : t ≠ 0 := by omega
  have hprod : t.primeFactorsList.prod = t := Nat.prod_primeFactorsList ht_ne
  have hge : ∀ x ∈ t.primeFactorsList, a + 1 ≤ x := by
    intro x hx
    have hxp : x.Prime := Nat.prime_of_mem_primeFactorsList hx
    have hxd : x ∣ t := Nat.dvd_of_mem_primeFactorsList hx
    have hax : a < x := hprimes x hxp hxd
    omega
  have hpow : (a + 1) ^ t.primeFactorsList.length ≤ t.primeFactorsList.prod :=
    List.pow_card_le_prod t.primeFactorsList (a + 1) hge
  have hmono : (a + 1) ^ 3 ≤ (a + 1) ^ t.primeFactorsList.length :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hcube : a ^ 3 < (a + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  rw [hprod] at hpow
  omega

end Erdos858
