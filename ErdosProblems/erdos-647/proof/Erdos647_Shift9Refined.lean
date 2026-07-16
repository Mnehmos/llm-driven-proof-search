import campaign.«family2-classifications»

/-!
# Erdős #647 — refined shift-9 obstruction

The existing shift-9 classification has four branches.  Congruence and parity
eliminate the square branch and attach an exact residue restriction to each
remaining branch.  This sharpens the growing-depth search interface but does
not by itself contradict every candidate.
-/

/-- A positive multiple of four, multiplied by a positive parameter and then
decremented, cannot be a square. -/
theorem erdos647_no_square_of_four_dvd :
    ∀ a N p : ℕ, 0 < a → 1 ≤ N → 4 ∣ a → a * N - 1 ≠ p ^ 2 := by
  intro a N p ha0 hN ha heq
  obtain ⟨c, hc⟩ := ha
  have hcpos : 0 < c := by
    rw [hc] at ha0
    omega
  have hcNpos : 0 < c * N := Nat.mul_pos hcpos (by omega)
  have hleft : a * N = 4 * (c * N) := by
    rw [hc]
    ring
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' p
  · have hsq : p ^ 2 = 4 * r ^ 2 := by
      rw [hr]
      ring
    rw [hleft, hsq] at heq
    omega
  · have hsq : p ^ 2 = 4 * (r * (r + 1)) + 1 := by
      rw [hr]
      ring
    rw [hleft, hsq] at heq
    omega

/-- If the shift-9 cofactor is prime, its parameter avoids `1 mod 3`. -/
theorem erdos647_shift9_prime_residue :
    ∀ N : ℕ, 1 ≤ N → Nat.Prime (280 * N - 1) →
      N % 3 = 0 ∨ N % 3 = 2 := by
  intro N hN hr
  by_cases h0 : N % 3 = 0
  · exact Or.inl h0
  by_cases h2 : N % 3 = 2
  · exact Or.inr h2
  have hmodlt : N % 3 < 3 := Nat.mod_lt N (by norm_num)
  have h1 : N % 3 = 1 := by omega
  have hdecomp := Nat.mod_add_div N 3
  have hNform : N = 3 * (N / 3) + 1 := by omega
  have hdiv : 3 ∣ 280 * N - 1 := by
    refine ⟨280 * (N / 3) + 93, ?_⟩
    conv_lhs => rw [hNform]
    omega
  have hor := Nat.Prime.eq_one_or_self_of_dvd hr 3 hdiv
  omega

/-- If the shift-9 cofactor is three times a prime, its parameter is `4` or
`7 mod 9`. -/
theorem erdos647_shift9_three_prime_residue :
    ∀ N p : ℕ, 1 ≤ N → Nat.Prime p → 280 * N - 1 = 3 * p →
      N % 9 = 4 ∨ N % 9 = 7 := by
  intro N p hN hp heq
  have hpne3 : p ≠ 3 := by
    intro hp3
    rw [hp3] at heq
    omega
  have h3np : ¬ 3 ∣ p := by
    intro h3p
    have h3prime : Nat.Prime 3 := by norm_num
    have h := (Nat.prime_dvd_prime_iff_eq h3prime hp).mp h3p
    exact hpne3 h.symm
  have hpmod : p % 3 ≠ 0 := by
    intro hzero
    exact h3np (Nat.dvd_of_mod_eq_zero hzero)
  have hNmodlt : N % 9 < 9 := Nat.mod_lt N (by norm_num)
  have hpmodlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  have hNdecomp := Nat.mod_add_div N 9
  have hpdecomp := Nat.mod_add_div p 3
  omega

/-- If the shift-9 cofactor is nine times a prime, its parameter is `1` or
`10 mod 27`. -/
theorem erdos647_shift9_nine_prime_residue :
    ∀ N p : ℕ, 1 ≤ N → Nat.Prime p → 280 * N - 1 = 9 * p →
      N % 27 = 1 ∨ N % 27 = 10 := by
  intro N p hN hp heq
  have hpne3 : p ≠ 3 := by
    intro hp3
    rw [hp3] at heq
    omega
  have h3np : ¬ 3 ∣ p := by
    intro h3p
    have h3prime : Nat.Prime 3 := by norm_num
    have h := (Nat.prime_dvd_prime_iff_eq h3prime hp).mp h3p
    exact hpne3 h.symm
  have hpmod : p % 3 ≠ 0 := by
    intro hzero
    exact h3np (Nat.dvd_of_mod_eq_zero hzero)
  have hNmodlt : N % 27 < 27 := Nat.mod_lt N (by norm_num)
  have hpmodlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  have hNdecomp := Nat.mod_add_div N 27
  have hpdecomp := Nat.mod_add_div p 3
  omega

/-- Fully refined shift-9 consequence of the existing candidate
classification.  The square branch disappears, and every surviving branch
comes with its exact forced residue class for the parameter `N`. -/
theorem erdos647_shift9_refined :
    ∀ n N : ℕ, 84 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      n = 2520 * N →
      (Nat.Prime (280 * N - 1) ∧
        (N % 3 = 0 ∨ N % 3 = 2)) ∨
      (∃ p : ℕ, Nat.Prime p ∧ 280 * N - 1 = 3 * p ∧
        (N % 9 = 4 ∨ N % 9 = 7)) ∨
      (∃ p : ℕ, Nat.Prime p ∧ 280 * N - 1 = 9 * p ∧
        (N % 27 = 1 ∨ N % 27 = 10)) := by
  intro n N hn H hnN
  have hN : 1 ≤ N := by omega
  have hdvd : 2520 ∣ n := ⟨N, hnN⟩
  have hclass := erdos647_shift9 n hn H hdvd
  have hval : (n - 9) / 9 = 280 * N - 1 := by omega
  rw [hval] at hclass
  rcases hclass with hp | hsquare | hthree | hnine
  · exact Or.inl ⟨hp, erdos647_shift9_prime_residue N hN hp⟩
  · obtain ⟨p, hp, heq⟩ := hsquare
    exact (erdos647_no_square_of_four_dvd 280 N p
      (by norm_num) hN (by norm_num) heq).elim
  · obtain ⟨p, hp, heq⟩ := hthree
    exact Or.inr <| Or.inl ⟨p, hp, heq,
      erdos647_shift9_three_prime_residue N p hN hp heq⟩
  · obtain ⟨p, hp, heq⟩ := hnine
    exact Or.inr <| Or.inr ⟨p, hp, heq,
      erdos647_shift9_nine_prime_residue N p hN hp heq⟩
