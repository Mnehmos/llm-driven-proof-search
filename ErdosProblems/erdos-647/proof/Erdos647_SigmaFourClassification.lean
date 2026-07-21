import Mathlib

/-!
# Erdős #647 — exact classification at divisor budget four

This generic arithmetic lemma classifies every integer at least two having at
most four divisors.  Such an integer is prime, a prime square, a prime cube,
or a product of two distinct primes.  It is the exact finite shape theorem
needed for the remaining `q7` residual in the sharp base gauntlet.

Tracked proof-search verification (2026-07-16):

* generic classification: preverification
  `034e3e62-7755-4fc4-aae9-6901386a2835`, problem
  `4fabc6e0-d523-45f2-a242-9294366aab5c`, episode
  `f5375b3b-e1b3-4440-80ae-9b1fba14dc80`, root hash
  `cb076e305a25d61ab72f1190f88eb4d035c85286dc04cd23a26adc493b9be59c`;
* `q7` shape: preverification `a1f75504-8760-44a1-88e0-1f479d3f9504`,
  problem `3269049f-3285-419e-9d3c-9f011eec124d`, episode
  `426f582b-bd4c-44b1-a964-9ac85b1e7987`, root hash
  `650825e7dceffca4d5beb9cf82e55ffaa12ae97f50322a18e0b218104aba78fe`;
* coupled depth-zero theorem: preverification
  `a1d70b3f-3e08-4fed-83c9-bcc79c4089dc`, problem
  `4152887d-8d9d-4ee7-8a93-a5c13de5ced0`, episode
  `003bb946-196b-40ba-9175-06d63d00f36f`, root hash
  `ca7e53b655f67a4b107b4452addc94106b37da549ab93366d98767088d7f9bd7`.

All three tracked outcomes are `kernel_verified`; all three replays are
`matched(1)`.
-/

namespace Erdos647

theorem sigma_zero_le_four_classification :
    ∀ x : ℕ, 2 ≤ x → ArithmeticFunction.sigma 0 x ≤ 4 →
      Nat.Prime x ∨
        (∃ p : ℕ, Nat.Prime p ∧ x = p ^ 2) ∨
        (∃ p : ℕ, Nat.Prime p ∧ x = p ^ 3) ∨
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ x = p * q := by
  intro x hx hsigma
  by_cases hxprime : Nat.Prime x
  · exact Or.inl hxprime
  right
  let p := x.minFac
  let c := x / p
  have hxpos : 0 < x := by omega
  have hx0 : x ≠ 0 := by omega
  have hx1 : x ≠ 1 := by omega
  have hpprime : Nat.Prime p := Nat.minFac_prime hx1
  have hpdvd : p ∣ x := Nat.minFac_dvd x
  have hxc : x = p * c := by
    dsimp [c]
    exact (Nat.mul_div_cancel' hpdvd).symm
  have hplec : p ≤ c := by
    dsimp [p, c]
    exact Nat.minFac_le_div hxpos hxprime
  by_cases hpc : p = c
  · left
    exact ⟨p, hpprime, by rw [hxc, hpc, pow_two]⟩
  have hpltc : p < c := lt_of_le_of_ne hplec hpc
  have hp2 : 2 ≤ p := hpprime.two_le
  have hc2 : 2 ≤ c := le_trans hp2 hplec
  have hplt : p < x := by
    rw [hxc]
    nlinarith
  have hclt : c < x := by
    rw [hxc]
    nlinarith
  have hcdvd : c ∣ x := by
    rw [hxc]
    exact dvd_mul_left c p
  have hsub : ({1, p, c, x} : Finset ℕ) ⊆ x.divisors := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Nat.mem_divisors]
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨one_dvd _, hx0⟩
    · exact ⟨hpdvd, hx0⟩
    · exact ⟨hcdvd, hx0⟩
    · exact ⟨dvd_rfl, hx0⟩
  have hcard : ({1, p, c, x} : Finset ℕ).card = 4 := by
    have h1not : 1 ∉ ({p, c, x} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨by omega, by omega, by omega⟩
    have hpnot : p ∉ ({c, x} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hpc, ne_of_lt hplt⟩
    have hcnot : c ∉ ({x} : Finset ℕ) := by
      simpa only [Finset.mem_singleton] using ne_of_lt hclt
    rw [Finset.card_insert_of_notMem h1not,
      Finset.card_insert_of_notMem hpnot,
      Finset.card_insert_of_notMem hcnot,
      Finset.card_singleton]
  have hdivcard : x.divisors.card ≤ 4 := by
    rw [← ArithmeticFunction.sigma_zero_apply]
    exact hsigma
  have hseteq : ({1, p, c, x} : Finset ℕ) = x.divisors := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcard]
    exact hdivcard
  by_cases hcprime : Nat.Prime c
  · right
    right
    exact ⟨p, c, hpprime, hcprime, hpc, hxc⟩
  obtain ⟨d, e, hd, he, hde⟩ :=
    (Nat.not_prime_iff_exists_mul_eq hc2).mp hcprime
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · interval_cases d <;> simp_all
    · exact h
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e <;> simp_all
    · exact h
  have hdmem : d ∈ ({1, p, c, x} : Finset ℕ) := by
    rw [hseteq, Nat.mem_divisors]
    exact ⟨(show d ∣ c from ⟨e, hde.symm⟩).trans hcdvd, hx0⟩
  have hemem : e ∈ ({1, p, c, x} : Finset ℕ) := by
    rw [hseteq, Nat.mem_divisors]
    have hedvd : e ∣ c := ⟨d, by simpa [mul_comm] using hde.symm⟩
    exact ⟨hedvd.trans hcdvd, hx0⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdmem hemem
  have hdp : d = p := by
    rcases hdmem with hd1 | hdp | hdc | hdx
    · omega
    · exact hdp
    · omega
    · omega
  have hep : e = p := by
    rcases hemem with he1 | hep | hec | hex
    · omega
    · exact hep
    · omega
    · omega
  right
  left
  refine ⟨p, hpprime, ?_⟩
  rw [hxc, ← hde, hdp, hep]
  ring

/-- The `q7` residual is `2 mod 3`, so the prime-square branch in the generic
four-divisor classification is impossible. -/
theorem base_gauntlet_q7_shape :
    ∀ N a7 q7 : ℕ, 1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      1 < q7 → ArithmeticFunction.sigma 0 q7 ≤ 4 →
      Nat.Prime q7 ∨
        (∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3) ∨
        ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q := by
  intro N a7 q7 hN hq7eq hq7gt hq7small
  have hpow7mod3 : ∀ a : ℕ, 7 ^ a % 3 = 1 := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [pow_succ, Nat.mul_mod, ih]
  have hq7nsq : ∀ b : ℕ, q7 ≠ b ^ 2 := by
    intro b hb
    have hleft : (360 * N - 1) % 3 = 2 := by omega
    have hprod := Nat.mul_mod (7 ^ a7) q7 3
    rw [← hq7eq, hleft, hb, hpow7mod3 a7] at hprod
    have hsq := Nat.mul_mod b b 3
    rw [← pow_two] at hsq
    have hbmod : b % 3 < 3 := Nat.mod_lt b (by norm_num)
    interval_cases h : b % 3 <;> omega
  rcases sigma_zero_le_four_classification q7 (by omega) hq7small with
    hprime | hsquare | hcube | hsemiprime
  · exact Or.inl hprime
  · obtain ⟨p, hp, hpq⟩ := hsquare
    exact absurd hpq (hq7nsq p)
  · exact Or.inr (Or.inl hcube)
  · exact Or.inr (Or.inr hsemiprime)

/-- The original shift-7 budget couples the 7-adic depth to the residual
shape.  A composite residual has exactly four divisors, so it can occur only
at adic depth zero. -/
theorem base_gauntlet_q7_composite_forces_depth_zero :
    ∀ N a7 q7 : ℕ, 1 ≤ N →
      360 * N - 1 = 7 ^ a7 * q7 →
      1 < q7 →
      (a7 + 2) * ArithmeticFunction.sigma 0 q7 ≤ 9 →
      (Nat.Prime q7 ∧ a7 ≤ 2) ∨
        (a7 = 0 ∧
          ((∃ p : ℕ, Nat.Prime p ∧ q7 = p ^ 3) ∨
            ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ q7 = p * q)) := by
  intro N a7 q7 hN hq7eq hq7gt hbudget
  have hq7small : ArithmeticFunction.sigma 0 q7 ≤ 4 := by
    have hlo := Nat.mul_le_mul_right (ArithmeticFunction.sigma 0 q7)
      (show 2 ≤ a7 + 2 by omega)
    omega
  rcases base_gauntlet_q7_shape N a7 q7 hN hq7eq hq7gt hq7small with
    hprime | hcube | hsemiprime
  · left
    have hsigma : ArithmeticFunction.sigma 0 q7 = 2 := by
      rw [show q7 = q7 ^ 1 from (pow_one q7).symm,
        ArithmeticFunction.sigma_zero_apply_prime_pow hprime]
    rw [hsigma] at hbudget
    exact ⟨hprime, by omega⟩
  · right
    obtain ⟨p, hp, hpq⟩ := hcube
    have hsigma : ArithmeticFunction.sigma 0 q7 = 4 := by
      rw [hpq, ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    rw [hsigma] at hbudget
    exact ⟨by omega, Or.inl ⟨p, hp, hpq⟩⟩
  · right
    obtain ⟨p, q, hp, hq, hpq, hprod⟩ := hsemiprime
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hsigmap : ArithmeticFunction.sigma 0 p = 2 := by
      rw [show p = p ^ 1 from (pow_one p).symm,
        ArithmeticFunction.sigma_zero_apply_prime_pow hp]
    have hsigmaq : ArithmeticFunction.sigma 0 q = 2 := by
      rw [show q = q ^ 1 from (pow_one q).symm,
        ArithmeticFunction.sigma_zero_apply_prime_pow hq]
    have hsigma : ArithmeticFunction.sigma 0 q7 = 4 := by
      rw [hprod, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
        hsigmap, hsigmaq]
      norm_num
    rw [hsigma] at hbudget
    exact ⟨by omega, Or.inr ⟨p, q, hp, hq, hpq, hprod⟩⟩

end Erdos647
