import Mathlib

/-!
# Erdős #647 — shift-16 prime sharpening

This self-contained snapshot removes the residual prime-square ambiguity from
the two `σ₀ ≤ 3` branches of the shift-16 frontier.  The generic lemma and
both affine applications were independently preverified and then proved in
tracked proof-search episodes.

* generic: problem `e8bf4329-f948-4a64-8ff1-5b7765f6adf1`, episode
  `2f83b7ab-cdd1-48e6-af76-d32d841cd1db`, root hash
  `cfd585160ca963a71aed4dbe0d741a1a4de9ac81fc64a6edb5292f8d5f2d5018`;
* even cofactor: problem `8596db8c-36d6-4fe1-8380-08024536d2bd`, episode
  `259f0f20-7fa0-4ccf-9054-98d801cad533`, root hash
  `dbcbd2f9cde4116d267ba804323e05209d4a93e5a6085a508fd8f37470de54c7`;
* half cofactor: problem `68bf94d6-571b-44af-b5d0-bc2311c76512`, episode
  `e8290676-9f27-4448-b88f-989a289fb87e`, root hash
  `23b54e04aff0f7928f356c19ea3852270e2b2995355cfa57eabc7878c143f2bb`.

All three tracked outcomes are `kernel_verified` (`root_proved`).
-/

namespace Erdos647

/-- A number at least two with at most three divisors is prime once the only
possible composite case, a square, is excluded. -/
theorem prime_of_sigma_zero_le_three_of_not_square :
    ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 3 →
      (∀ a : ℕ, x ≠ a ^ 2) → Nat.Prime x := by
  intro x hx hsigma hnsq
  by_contra hprime
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Nat.not_prime_iff_exists_mul_eq hx).mp hprime
  by_cases heq : a = b
  · apply hnsq a
    simpa [heq, pow_two] using hab.symm
  have hx0 : x ≠ 0 := by omega
  have hx1 : x ≠ 1 := by omega
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, one_mul] at hab
    omega
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, mul_one] at hab
    omega
  have hsub : ({1, a, b, x} : Finset ℕ) ⊆ x.divisors := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Nat.mem_divisors]
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨one_dvd _, hx0⟩
    · exact ⟨⟨b, hab.symm⟩, hx0⟩
    · exact ⟨⟨a, by simpa [mul_comm] using hab.symm⟩, hx0⟩
    · exact ⟨dvd_rfl, hx0⟩
  have hcard : ({1, a, b, x} : Finset ℕ).card = 4 := by
    have h1not : 1 ∉ ({a, b, x} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hx1⟩
    have hanot : a ∉ ({b, x} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨heq, ne_of_lt ha⟩
    have hbnot : b ∉ ({x} : Finset ℕ) := by
      simpa only [Finset.mem_singleton] using ne_of_lt hb
    rw [Finset.card_insert_of_notMem h1not,
      Finset.card_insert_of_notMem hanot,
      Finset.card_insert_of_notMem hbnot,
      Finset.card_singleton]
  have hfour : 4 ≤ x.divisors.card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  rw [ArithmeticFunction.sigma_zero_apply] at hsigma
  omega

/-- In the even-`M` shift-16 branch, `315M-1` is `2 mod 3`, hence cannot be
a square; the existing three-divisor bound therefore forces primality. -/
theorem shift16_even_cofactor_prime :
    ∀ M : ℕ, 1 ≤ M → M % 2 = 0 →
      ArithmeticFunction.sigma 0 (315 * M - 1) ≤ 3 →
      Nat.Prime (315 * M - 1) := by
  intro M hM hMeven hsigma
  apply prime_of_sigma_zero_le_three_of_not_square (315 * M - 1)
  · omega
  · exact hsigma
  · intro a heq
    have ha_lt : a % 3 < 3 := Nat.mod_lt a (by norm_num)
    have hsqmod := Nat.mul_mod a a 3
    rw [← pow_two, ← heq] at hsqmod
    have hMdecomp := Nat.mod_add_div M 2
    have ha_decomp := Nat.mod_add_div a 3
    interval_cases h : a % 3 <;> omega

/-- If `315M-1=2t`, then `t` is `2 mod 5`, hence cannot be a square; the
existing three-divisor bound therefore forces primality. -/
theorem shift16_half_cofactor_prime :
    ∀ M t : ℕ, 1 ≤ M → 315 * M - 1 = 2 * t →
      ArithmeticFunction.sigma 0 t ≤ 3 → Nat.Prime t := by
  intro M t hM hMt hsigma
  apply prime_of_sigma_zero_le_three_of_not_square t
  · omega
  · exact hsigma
  · intro a heq
    have ha_lt : a % 5 < 5 := Nat.mod_lt a (by norm_num)
    have hsqmod := Nat.mul_mod a a 5
    rw [← pow_two, ← heq] at hsqmod
    have hMdecomp := Nat.mod_add_div M 5
    have ha_decomp := Nat.mod_add_div a 5
    interval_cases h : a % 5 <;> omega

end Erdos647
