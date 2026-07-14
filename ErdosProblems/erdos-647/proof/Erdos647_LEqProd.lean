import Mathlib

/-!
# Erdős #647 — Layer C final-assembly prep: Euler-product closed form for L

Snapshot of the exact statement + proof term kernel-verified through the
tracked proof-search pipeline on 2026-07-14.

  problem_version_id  7a467ca6-2f6d-43c0-b125-12c5638620e0
  episode_id          78ae3432-08de-45b1-8ab4-8896f76e4ae4
  root_statement_hash 21847448bdf2801ed62abf7d3d1aa2741496622a03811552b0b2da2dd81e0943
  outcome             kernel_verified (root_proved)
  import manifest     ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]

Content: a clean Euler-product closed form for
`L := ∑_{l∣prodPrimes} selbergTerms(l)` (the denominator
`erdos647_selberg_sieve_bound_conditional`'s main term `totalMass/L`
needs bounded below via a Mertens-type estimate):

  `L = ∏_{p∈prodPrimes.primeFactors} (1-ν(p))⁻¹`

Proof: instantiate Mathlib's `sum_divisors_selbergTerms_eq_selbergTerms_
mul_nu_inv` at `d := prodPrimes` (trivially `prodPrimes∣prodPrimes`),
giving `∑_{l∈prodPrimes.divisors, l∣prodPrimes} selbergTerms(l) =
selbergTerms(prodPrimes)·ν(prodPrimes)⁻¹` — the `if l∣prodPrimes` guard
is vacuous since every `l∈prodPrimes.divisors` already satisfies it, so
this collapses to `L = selbergTerms(prodPrimes)·ν(prodPrimes)⁻¹`.
Substituting `selbergTerms_apply` (`selbergTerms(prodPrimes) =
ν(prodPrimes)·∏_{p∈prodPrimes.primeFactors}(1-ν(p))⁻¹`) and cancelling
the `ν(prodPrimes)` factor (`mul_right_comm` then `mul_inv_cancel₀`)
gives the result directly.

No Lean bugs beyond one expected fix: an initial `mul_assoc`/`mul_comm`
attempt to cancel `ν(prodPrimes)·ν(prodPrimes)⁻¹` inside a doubly-nested
product left the two factors non-adjacent (`mul_comm` couldn't find its
target pattern) — fixed by using `mul_right_comm` directly on the
original `(a*b)*c` shape to bring the cancelling factors adjacent first
(`a*b*c → a*c*b`), then `mul_inv_cancel₀`/`one_mul`.

Since `ν(p) = rootUnionCount(p)/p ≈ 7/p` for this campaign's own
seven-tuple construction (large primes `p`, `rootUnionCount(p)∈[1,7]`
uniformly), this closed form is what a Mertens-type product estimate
(generalizing Layer A's `erdos647_mertens_assembly`, but for a
bounded-multiplicity local factor rather than the classical `(1-1/p)⁻¹`)
needs to act on directly, to get `L`'s growth rate as a function of the
sieve level `z` — the remaining piece before the final `x/(log x)^7`
density bound can be extracted from `erdos647_selberg_sieve_bound_
conditional`.
-/

theorem erdos647_L_eq_prod :
    ∀ (s : SelbergSieve), (∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l) = ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)⁻¹ := by
  intro s
  have h := s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv (dvd_refl s.prodPrimes)
  have hall : ∀ l ∈ s.prodPrimes.divisors, l ∣ s.prodPrimes := fun l hl => Nat.dvd_of_mem_divisors hl
  have hsimp : (∑ l ∈ s.prodPrimes.divisors, if l ∣ s.prodPrimes then s.selbergTerms l else 0) = ∑ l ∈ s.prodPrimes.divisors, s.selbergTerms l := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [if_pos (hall l hl)]
  rw [hsimp] at h
  have hnupos : 0 < s.nu s.prodPrimes := BoundingSieve.nu_pos_of_dvd_prodPrimes (dvd_refl _)
  rw [h, s.selbergTerms_apply, mul_right_comm, mul_inv_cancel₀ hnupos.ne', one_mul]
