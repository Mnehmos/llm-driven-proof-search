import Mathlib

/-!
# Erdős #647 — finite prime-product dichotomy

For a finite coordinate family `P : Fin W → ℕ`, either two distinct
coordinates have product below `n`, or at most one coordinate has square below
`n`.  The numerical statement does not actually require primality or
injectivity, so the strongest theorem is proved for an arbitrary family and a
prime-family corollary records the intended sieve interface.

The strongest arbitrary-family dichotomy was tracked independently on
2026-07-16:

* problem version: `8ae9bbe4-91cd-4206-a4a1-ac0e3b018774`
* episode: `4cbc17df-28dd-4420-ad45-e4c7d5e7eb64`
* root statement hash:
  `f6d5f14ed6a6d4f2ffdca42063809f745c7faf9e0380d61420ed22bbc926e299`
* outcome: `kernel_verified`
-/

/-- Two values whose squares are both below `n` have product below `n`. -/
theorem erdos647_product_lt_of_squares_lt :
    ∀ {a b n : ℕ}, a ^ 2 < n → b ^ 2 < n → a * b < n := by
  intro a b n ha hb
  rcases le_total a b with hab | hba
  · have hmul : a * b ≤ b * b := Nat.mul_le_mul_right b hab
    exact hmul.trans_lt (by simpa [pow_two] using hb)
  · have hmul : a * b ≤ a * a := Nat.mul_le_mul_left a hba
    exact hmul.trans_lt (by simpa [pow_two] using ha)

/-- If no distinct pair has product below `n`, two distinct coordinates cannot
both have square below `n`. -/
theorem erdos647_no_pair_product_square_exclusion :
    ∀ {n W : ℕ} (P : Fin W → ℕ),
      (∀ i j : Fin W, i ≠ j → ¬ P i * P j < n) →
      ∀ i j : Fin W, i ≠ j →
        ¬ ((P i) ^ 2 < n ∧ (P j) ^ 2 < n) := by
  intro n W P hno i j hij hsq
  exact hno i j hij (erdos647_product_lt_of_squares_lt hsq.1 hsq.2)

/-- For every finite family, either a distinct pair has product below `n`, or
the square-below-`n` coordinates form a finset of cardinality at most one. -/
theorem erdos647_product_or_at_most_one_small_square :
    ∀ (n W : ℕ) (P : Fin W → ℕ),
      (∃ i j : Fin W, i ≠ j ∧ P i * P j < n) ∨
        (Finset.univ.filter fun i : Fin W => (P i) ^ 2 < n).card ≤ 1 := by
  intro n W P
  by_cases hp : ∃ i j : Fin W, i ≠ j ∧ P i * P j < n
  · exact Or.inl hp
  · right
    apply Finset.card_le_one.mpr
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    by_contra hij
    exact hp ⟨i, j, hij,
      erdos647_product_lt_of_squares_lt hi hj⟩

/-- The intended interface for an injective finite family of primes.  The
assumptions certify that distinct coordinates represent distinct primes; the
combinatorial dichotomy itself is supplied by the stronger theorem above. -/
theorem erdos647_prime_product_dichotomy :
    ∀ (n W : ℕ) (P : Fin W → ℕ),
      Function.Injective P →
      (∀ i : Fin W, Nat.Prime (P i)) →
      (∃ i j : Fin W, i ≠ j ∧ P i * P j < n) ∨
        (Finset.univ.filter fun i : Fin W => (P i) ^ 2 < n).card ≤ 1 := by
  intro n W P _ _
  exact erdos647_product_or_at_most_one_small_square n W P
