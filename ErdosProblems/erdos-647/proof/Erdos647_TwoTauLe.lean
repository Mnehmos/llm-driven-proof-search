import Mathlib

/-!
# Erdős #647 — a global divisor-budget inequality

This file proves the elementary inequality

```
2 * n.divisors.card ≤ n + 2
```

for every natural number `n`.  In the fixed-window construction for
Erdős #647, this is exactly the arithmetic estimate needed after a shifted
integer has been written as a known factor times a prime cofactor.  Earlier
work discharged only a finite range computationally; the theorem below has
no cutoff.

Proof-search provenance:

* preverification job: `a82ca9fb-f54b-4435-96f8-249d1fbaa2f9`
* problem version: `997ec74c-eed2-4b57-b231-f56cc22e9f75`
* episode: `db81664f-e2f9-4f8f-9263-7ce5e24db3e6`
* root statement hash:
  `73aa208d57544a01f4e7d2cd5e8aaa15616b176075d5740dedec58eb1c4543c1`
* outcome: `kernel_verified`

The proof contains no claim that the prime cofactors required by a
simultaneous finite-window construction exist.  It supplies only the
unconditional divisor-count component of that construction.
-/

/-- Twice the number of positive divisors of `n` is at most `n + 2`. -/
theorem erdos647_two_mul_card_divisors_le_add_two (n : ℕ) :
    2 * n.divisors.card ≤ n + 2 := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hn2 : 2 ≤ n := by omega
  have hnmem : n ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨dvd_rfl, hn0⟩
  have hsub : n.divisors.erase n ⊆ Finset.Icc 1 (n / 2) := by
    intro d hd
    simp only [Finset.mem_erase, Nat.mem_divisors] at hd
    rcases hd with ⟨hdne, hdn, _⟩
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnpos
    have hdlt : d < n := lt_of_le_of_ne (Nat.le_of_dvd hnpos hdn) hdne
    have htwod : d * 2 ≤ n := by
      obtain ⟨q, hq⟩ := hdn
      have hq2 : 2 ≤ q := by
        by_contra hqnot
        have hqle : q ≤ 1 := by omega
        interval_cases q <;> simp_all
      rw [hq]
      exact Nat.mul_le_mul_left d hq2
    exact Finset.mem_Icc.mpr
      ⟨hdpos, (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 htwod⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have herase : (n.divisors.erase n).card + 1 = n.divisors.card := by
    exact Finset.card_erase_add_one hnmem
  have hdouble : 2 * (n.divisors.erase n).card ≤ n := by
    calc
      2 * (n.divisors.erase n).card ≤ 2 * (n / 2) :=
        Nat.mul_le_mul_left 2 hcard
      _ ≤ n := Nat.mul_div_le n 2
  omega
