/-
Erdős Problem #858 — Lemma 4.5 (prime–semiprime description), full dichotomy.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Lemma 4.5.)

Byte-faithful reconstruction of the kernel-verified root theorem from the
proofsearch MCP episode 1883d607-3756-41a3-a872-c41b499b524d,
problem_version_id f8035342-426e-4483-afb4-c18a37436893.
Outcome: kernel_verified / root_kernel_verified.
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash bbd9ad12…

Upgrades the verified `Ω(t) ≤ 2` core (Erdos858_Lemma45_CofactorPrimeSemiprime)
to the explicit statement of Lemma 4.5: a child's cofactor `t` in the upper
layer (`t < a³`, all prime factors `> a`) is `1`, a prime, or a product of two
primes — i.e. every child of `a` is `a`, `a·p`, or `a·p·q`. Proof: bound
`Ω(t) = t.primeFactorsList.length ≤ 2` via `List.pow_card_le_prod`, then
case-split the list of prime factors ([] ⇒ t=1, [p] ⇒ t=p prime, [p,q] ⇒ t=p·q;
length ≥ 3 contradicts the bound).
-/
import Mathlib

namespace Erdos858

/-- Lemma 4.5, full form. A cofactor `t < a³` all of whose prime factors exceed
`a` is `1`, a prime, or a product of two primes. -/
theorem lemma45_prime_semiprime_full :
    ∀ a t : ℕ, 1 ≤ a → 0 < t → t < a ^ 3 →
      (∀ p : ℕ, Nat.Prime p → p ∣ t → a < p) →
      t = 1 ∨ Nat.Prime t ∨ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ t = p * q := by
  intro a t ha htpos htlt hprimes
  have ht_ne : t ≠ 0 := by omega
  have hprod : t.primeFactorsList.prod = t := Nat.prod_primeFactorsList ht_ne
  have hge : ∀ x ∈ t.primeFactorsList, a + 1 ≤ x := by
    intro x hx
    have hxp := Nat.prime_of_mem_primeFactorsList hx
    have hxd := Nat.dvd_of_mem_primeFactorsList hx
    have hax := hprimes x hxp hxd
    omega
  have hlen : t.primeFactorsList.length ≤ 2 := by
    by_contra hlen
    push_neg at hlen
    have hpow : (a + 1) ^ t.primeFactorsList.length ≤ t.primeFactorsList.prod :=
      List.pow_card_le_prod t.primeFactorsList (a + 1) hge
    have hmono : (a + 1) ^ 3 ≤ (a + 1) ^ t.primeFactorsList.length :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hcube : a ^ 3 < (a + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    rw [hprod] at hpow
    omega
  rcases hcase : t.primeFactorsList with _ | ⟨p, l1⟩
  · left
    rw [hcase, List.prod_nil] at hprod
    omega
  · rcases l1 with _ | ⟨q, l2⟩
    · right; left
      have hp : Nat.Prime p := Nat.prime_of_mem_primeFactorsList (by rw [hcase]; simp)
      rw [hcase] at hprod
      simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
      rwa [← hprod]
    · rcases l2 with _ | ⟨r, l3⟩
      · right; right
        have hp : Nat.Prime p := Nat.prime_of_mem_primeFactorsList (by rw [hcase]; simp)
        have hq : Nat.Prime q := Nat.prime_of_mem_primeFactorsList (by rw [hcase]; simp)
        rw [hcase] at hprod
        simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
        exact ⟨p, q, hp, hq, hprod.symm⟩
      · exfalso
        rw [hcase] at hlen
        simp only [List.length_cons] at hlen
        omega

end Erdos858
