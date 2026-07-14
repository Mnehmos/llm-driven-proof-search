import Mathlib

/-!
# Erdős #647 — Layer C: squarefree divisibility characterization

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  a148f8a8-6c5a-4063-81a4-ffec7e0b0041
  episode_id          b961db4d-ce24-4401-9859-95ee6eac27ee
  root_statement_hash d5e7784a47d522086f412ab1e43c761fa22b5743a9ef940087b0dcd89329582f
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: a general-purpose (sieve-independent) fact — for squarefree `d`,
`d ∣ m ↔ ∀ p ∈ d.primeFactors, p ∣ m`. Forward direction trivial
(`Nat.dvd_of_mem_primeFactors` + transitivity). Reverse direction via
Mathlib's `Finset.prod_primes_dvd` (a product of DISTINCT primes each
dividing `m` divides `m` — no coprimality hypothesis needed explicitly,
since a `Finset`'s elements are automatically distinct and
`Finset.prod_primes_dvd` handles the unique-factorization argument
internally) combined with `Nat.prod_primeFactors_of_squarefree`
(`∏ p ∈ n.primeFactors, p = n` when `n` is squarefree) to identify `d`
with the product.

This is the bridge that will let `erdos647_forms_divisible_iff` (proven
only for prime `p`) generalize to composite squarefree `d`: `d ∣
∏formᵢ(N) ↔ ∀ p ∈ d.primeFactors, p ∣ ∏formᵢ(N)`, letting the per-prime
root-union sets combine via `erdos647_crt_card_two` into
`rootUnionCount(d) = ∏_{p∣d} rootUnionCount(p)`, extending
`erdos647_rem_bound` from prime `p` to composite `d` — required since
Mathlib's `BoundingSieve.errSum` sums over EVERY divisor of `prodPrimes(z)`.

One Lean fix: `Finset.prod_primes_dvd` requires `∀ a ∈ s, Prime a` (the
general `_root_.Prime`, from `Mathlib.Algebra.BigOperators.Associated`),
not `Nat.Prime` — needed an explicit `.prime` coercion
(`(Nat.prime_of_mem_primeFactors hp).prime`) since the two are
definitionally different classes even though logically equivalent for `ℕ`.
-/

theorem erdos647_squarefree_dvd_iff :
    ∀ (d m : ℕ), Squarefree d → (d ∣ m ↔ ∀ p ∈ d.primeFactors, p ∣ m) := by
  intro d m hd
  constructor
  · intro hdvd p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans hdvd
  · intro h
    have h2 : ∀ p ∈ d.primeFactors, Prime p := fun p hp => (Nat.prime_of_mem_primeFactors hp).prime
    have hprod : ∏ p ∈ d.primeFactors, p ∣ m := Finset.prod_primes_dvd m h2 h
    rwa [Nat.prod_primeFactors_of_squarefree hd] at hprod
