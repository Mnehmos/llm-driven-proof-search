import Mathlib

/-!
# Erdős #647 — Layer C: prodPrimes(z) squarefree

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  5d2f252a-bb16-4e94-8e26-05a0f11634b4
  episode_id          0883525e-1af6-4ea9-8401-38f1d2ceb645
  root_statement_hash 7ba91d026ab423e0535906d8d91026604a803be217ae3161474adb4a883cd3f4
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: for every level `z`, `prodPrimes(z) := ∏_{p prime ≤ z, p∉{3,5,7}} p`
is squarefree — supplies `BoundingSieve`'s `prodPrimes_squarefree`
structure field for the eventual sieve instance built from this
campaign's independently-derived admissible seven-tuple
(`{210N-1,...,2520N-1}`, primes 3, 5, 7 structurally excluded from the
active sieve set — see `Erdos647_SevenTupleAdmissibility.lean`).

Proof: the exact technique Mathlib itself uses for `primorial`'s own
squarefreeness (`squarefree_primorial` in `Mathlib.NumberTheory.Primorial`)
— `Finset.squarefree_prod_of_pairwise_isCoprime`, since distinct primes
are pairwise coprime (`Nat.coprime_primes`) and each prime is trivially
squarefree (`Nat.Prime.squarefree`). One Lean wrinkle: the pairwise-
coprimality goal appears as `Function.onFun IsRelPrime id p q` (from
`Set.Pairwise`'s unfolding), not literally `IsRelPrime p q` — resolved
with `show IsRelPrime p q` (defeq) before `rw [← Nat.coprime_iff_isRelPrime]`.

Part of the mechanical (non-analytic) structure-building for Layer C's
`BoundingSieve` instance — the harder remaining pieces (`support`,
`weights`, `totalMass`, `errSum`) require genuine analytic-counting work
and are deliberately NOT rushed; see campaign memory for the precise,
unambiguous spec of what remains.
-/

theorem erdos647_prodPrimes_squarefree :
    ∀ (z : ℕ), Squarefree (∏ p ∈ (Finset.range (z+1)).filter (fun p => p.Prime ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), p) := by
  intro z
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    show IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes hp'.2.1 hq'.2.1).mpr hpq
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact hp'.2.1.squarefree
