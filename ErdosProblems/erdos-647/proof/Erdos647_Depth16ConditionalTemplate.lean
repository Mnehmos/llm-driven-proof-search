import Mathlib

open ArithmeticFunction

/-!
# Erdős #647 — admissible conditional depth-16 survivor family

Let `L = lcm(1,…,16) = 720720 = 2520 * 286`.  For every `1 ≤ k ≤ 16`,

`L*A - k = k * ((L/k)*A - 1)`.

Consequently, if all sixteen affine cofactors `(L/k)*A - 1` are prime, the
divisor-count budget through shift 16 holds.  This is a conditional survivor
family, not an existence theorem: simultaneous primality is not asserted.

The coefficient order below preserves the order supplied by the computational
search.  Its entries at positions 11–15 are permuted, but as a `Finset` it is
exactly the required set `{720720/k | 1 ≤ k ≤ 16}`.  The proof explicitly
selects the correct coefficient for each shift.

The affine tuple is admissible for a simpler reason than a root-count audit:
every form has constant term `-1`, so the residue class `A = 0` modulo any
prime avoids all roots simultaneously.

Proof-search provenance:

* conditional survivor: problem `daff2ca3-9498-434f-a556-e3c23694accc`,
  episode `03477442-66df-4bd3-91bb-5c47823f27da`, `kernel_verified`;
* tuple admissibility: problem `8c9a99a7-40db-4ef9-8003-3adf48744aad`,
  episode `7fde0b14-4655-406b-a4ac-793dbdfcf1df`, `kernel_verified`.
-/

def erdos647Depth16Coefficients : Finset ℕ :=
  [720720, 360360, 240240, 180180, 144144, 120120, 102960, 90090,
    80080, 72072, 60060, 51480, 48048, 65520, 55440, 45045].toFinset

/-- Mechanical audit that every required quotient `720720/k`, `1 ≤ k ≤ 16`,
really occurs in the supplied (partly permuted) coefficient list. -/
theorem erdos647_depth16_quotient_mem (k : ℕ)
    (hk : k ∈ Finset.Icc 1 16) :
    720720 / k ∈ erdos647Depth16Coefficients := by
  simp only [Finset.mem_Icc] at hk
  have hk1 : 1 ≤ k := hk.1
  have hk16 : k ≤ 16 := hk.2
  interval_cases k <;> native_decide

/-- The sixteen affine forms are admissible in the standard modular sense. -/
theorem erdos647_depth16_tuple_admissible :
    ∀ p : ℕ, p.Prime →
      ∃ a : Fin p, ∀ c ∈ erdos647Depth16Coefficients,
        ¬ Nat.ModEq p (c * (a : ℕ)) 1 := by
  intro p hp
  refine ⟨⟨0, hp.pos⟩, ?_⟩
  intro c hc hroot
  change (c * 0) % p = 1 % p at hroot
  simp [Nat.mod_eq_of_lt hp.one_lt] at hroot

/-- Simultaneous primality of the sixteen affine cofactors gives a survivor
through every shift `1,…,16` for `n = 2520 * (286*A) = 720720*A`. -/
theorem erdos647_depth16_conditional_survivor :
    ∀ A : ℕ,
      (∀ c ∈ erdos647Depth16Coefficients, Nat.Prime (c * A - 1)) →
      ∀ k ∈ Finset.Icc 1 16,
        sigma 0 (2520 * (286 * A) - k) ≤ k + 2 := by
  intro A hprime k hk
  have hp720720 := hprime 720720 (by native_decide)
  have hA : 0 < A := by
    by_contra h
    have hA0 : A = 0 := Nat.eq_zero_of_not_pos h
    subst A
    norm_num at hp720720
  have hsigma_prime : ∀ p : ℕ, p.Prime → sigma 0 p = 2 := by
    intro p hp
    simpa using (sigma_zero_apply_prime_pow (i := 1) hp)
  have hshift : ∀ k c : ℕ,
      1 ≤ k → k ≤ 16 → 45045 ≤ c → k * c = 720720 →
      Nat.Prime (c * A - 1) →
      sigma 0 (2520 * (286 * A) - k) ≤ k + 2 := by
    intro j c hj1 hj16 hc hjc hp
    have htotal : 2520 * (286 * A) = j * (c * A) := by
      calc
        2520 * (286 * A) = 720720 * A := by ring
        _ = (j * c) * A := by rw [hjc]
        _ = j * (c * A) := by ring
    have hfactor : 2520 * (286 * A) - j = j * (c * A - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
      exact congrArg (fun x => x - j) htotal
    have hcA : c ≤ c * A := by
      nth_rewrite 1 [← mul_one c]
      exact Nat.mul_le_mul_left c hA
    have hcop : Nat.Coprime j (c * A - 1) := by
      refine ((hp.coprime_iff_not_dvd).mpr ?_).symm
      intro hd
      have hle := Nat.le_of_dvd (by omega : 0 < j) hd
      omega
    have hsigmaJ : sigma 0 j * 2 ≤ j + 2 := by
      interval_cases j <;> native_decide
    rw [hfactor, isMultiplicative_sigma.map_mul_of_coprime hcop,
      hsigma_prime _ hp]
    exact hsigmaJ
  simp only [Finset.mem_Icc] at hk
  have hk1 : 1 ≤ k := hk.1
  have hk16 : k ≤ 16 := hk.2
  interval_cases k
  · exact hshift 1 720720 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 720720 (by native_decide))
  · exact hshift 2 360360 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 360360 (by native_decide))
  · exact hshift 3 240240 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 240240 (by native_decide))
  · exact hshift 4 180180 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 180180 (by native_decide))
  · exact hshift 5 144144 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 144144 (by native_decide))
  · exact hshift 6 120120 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 120120 (by native_decide))
  · exact hshift 7 102960 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 102960 (by native_decide))
  · exact hshift 8 90090 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 90090 (by native_decide))
  · exact hshift 9 80080 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 80080 (by native_decide))
  · exact hshift 10 72072 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 72072 (by native_decide))
  · exact hshift 11 65520 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 65520 (by native_decide))
  · exact hshift 12 60060 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 60060 (by native_decide))
  · exact hshift 13 55440 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 55440 (by native_decide))
  · exact hshift 14 51480 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 51480 (by native_decide))
  · exact hshift 15 48048 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 48048 (by native_decide))
  · exact hshift 16 45045 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (hprime 45045 (by native_decide))
