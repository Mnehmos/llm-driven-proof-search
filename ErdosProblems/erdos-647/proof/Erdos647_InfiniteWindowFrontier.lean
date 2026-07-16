import Mathlib

/-!
# Erdős #647 — the infinite-window frontier

The window variants are unconditional at window sizes at most two.  The first
genuinely open case, window size three (shift depth two), is exactly equivalent
to infinitude of Sophie Germain primes.  This identifies a classical open
barrier inside the third `sorry`; it does not replace that `sorry`.

Proof-search provenance:

* `shift_survivors_up_to_two_inline`: problem
  `f1717863-2574-48c0-a9d1-ae3a7b223fb9`, episode
  `e7b81c9f-8b1e-41c5-a760-d9aba712bb16`, `kernel_verified`;
* safe-prime sufficiency at depth two: problem
  `62b31233-1d14-44f2-84f0-f1af49d33e0a`, episode
  `7cf0660b-3dac-48f3-8294-7b22d8e9f593`, `kernel_verified`.

The converse and the final infinitude equivalence were then source-compiled
against the same pinned Mathlib environment.
-/

namespace Erdos647

open ArithmeticFunction

lemma five_le_card_of_chain_mem {s : Finset ℕ} {a b c d e : ℕ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s) :
    5 ≤ s.card := by
  have hsub : ({a, b, c, d, e} : Finset ℕ) ⊆ s := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ha, hb, hc, hd, he⟩
  have hanot : a ∉ ({b, c, d, e} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have hbnot : b ∉ ({c, d, e} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have hcnot : c ∉ ({d, e} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  have hdnot : d ∉ ({e} : Finset ℕ) := by
    simpa using ne_of_lt hde
  have hcard : ({a, b, c, d, e} : Finset ℕ).card = 5 := by
    rw [Finset.card_insert_of_notMem hanot,
      Finset.card_insert_of_notMem hbnot,
      Finset.card_insert_of_notMem hcnot,
      Finset.card_insert_of_notMem hdnot,
      Finset.card_singleton]
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma prime_or_prime_square_of_sigma_zero_le_three {a : ℕ}
    (ha : 1 < a) (htau : sigma 0 a ≤ 3) :
    ∃ p : ℕ, p.Prime ∧ (a = p ∨ a = p ^ 2) := by
  have ha0 : a ≠ 0 := by omega
  obtain ⟨p, hp, hpa_dvd⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  by_cases hpa : p = a
  · exact ⟨p, hp, Or.inl hpa.symm⟩
  · have hple : p ≤ a := Nat.le_of_dvd (by omega) hpa_dvd
    have hplt : p < a := lt_of_le_of_ne hple hpa
    have h1mem : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha0
    have hpmem : p ∈ a.divisors := Nat.mem_divisors.mpr ⟨hpa_dvd, ha0⟩
    have hamem : a ∈ a.divisors := Nat.mem_divisors_self a ha0
    have hsubset : ({1, p, a} : Finset ℕ) ⊆ a.divisors := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨h1mem, hpmem, hamem⟩
    have hane1 : a ≠ 1 := by omega
    have htri_card : ({1, p, a} : Finset ℕ).card = 3 := by
      have h1not : 1 ∉ ({p, a} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨Ne.symm hp.ne_one, Ne.symm hane1⟩
      have hpnot : p ∉ ({a} : Finset ℕ) := by
        simpa using hpa
      rw [Finset.card_insert_of_notMem h1not,
        Finset.card_insert_of_notMem hpnot, Finset.card_singleton]
    have hcard : a.divisors.card ≤ 3 := by
      rwa [← sigma_zero_apply]
    have hcardle : a.divisors.card ≤ ({1, p, a} : Finset ℕ).card := by
      rw [htri_card]
      exact hcard
    have hdiv_eq : ({1, p, a} : Finset ℕ) = a.divisors :=
      Finset.eq_of_subset_of_card_le hsubset hcardle
    have hqmem : a / p ∈ a.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hpa_dvd, ha0⟩
    rw [← hdiv_eq] at hqmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
    rcases hqmem with hq1 | hqp | hqa
    · have hmul := Nat.mul_div_cancel' hpa_dvd
      rw [hq1, mul_one] at hmul
      exact (hpa hmul).elim
    · refine ⟨p, hp, Or.inr ?_⟩
      have hmul := Nat.mul_div_cancel' hpa_dvd
      rw [hqp] at hmul
      simpa [pow_two] using hmul.symm
    · have hlt : a / p < a := Nat.div_lt_self (by omega) hp.one_lt
      omega

lemma four_lt_sigma_zero_prime_square_sub_one {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    4 < sigma 0 (p ^ 2 - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hfactor : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    have halg : (p - 1) * (p + 1) + 1 = p ^ 2 := by
      nlinarith [Nat.sub_add_cancel hp1]
    omega
  have hNpos : 0 < p ^ 2 - 1 := by
    have hpows : 1 < p ^ 2 := by nlinarith
    omega
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp]
    omega
  obtain ⟨t, ht⟩ := Nat.coprime_two_left.mp hcop
  have hpminus : p - 1 = 2 * t := by omega
  have h2dvd : 2 ∣ p ^ 2 - 1 := by
    refine ⟨t * (p + 1), ?_⟩
    rw [← hfactor, hpminus]
    ring
  have hpm_dvd : p - 1 ∣ p ^ 2 - 1 := by
    exact ⟨p + 1, hfactor.symm⟩
  have hpp_dvd : p + 1 ∣ p ^ 2 - 1 := by
    refine ⟨p - 1, ?_⟩
    rw [← hfactor]
    ring
  have h1mem : 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.one_mem_divisors.mpr (by omega)
  have h2mem : 2 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors.mpr ⟨h2dvd, by omega⟩
  have hpmmem : p - 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors.mpr ⟨hpm_dvd, by omega⟩
  have hppmem : p + 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors.mpr ⟨hpp_dvd, by omega⟩
  have hNmem : p ^ 2 - 1 ∈ (p ^ 2 - 1).divisors :=
    Nat.mem_divisors_self _ (by omega)
  have hfive : 5 ≤ (p ^ 2 - 1).divisors.card := by
    apply five_le_card_of_chain_mem
      (a := 1) (b := 2) (c := p - 1) (d := p + 1) (e := p ^ 2 - 1)
    · norm_num
    · omega
    · omega
    · nlinarith
    · exact h1mem
    · exact h2mem
    · exact hpmmem
    · exact hppmem
    · exact hNmem
  rw [sigma_zero_apply]
  omega

lemma two_mul_prime_of_even_sigma_zero_le_four {a : ℕ}
    (ha8 : 8 < a) (heven : 2 ∣ a) (htau : sigma 0 a ≤ 4) :
    ∃ q : ℕ, q.Prime ∧ a = 2 * q := by
  set q := a / 2 with hq_def
  have haeq : 2 * q = a := by
    simpa [hq_def] using Nat.mul_div_cancel' heven
  have hq4 : 4 < q := by omega
  by_cases hqprime : q.Prime
  · exact ⟨q, hqprime, haeq.symm⟩
  · exfalso
    obtain ⟨r, hrprime, hrdvd⟩ :=
      Nat.exists_prime_and_dvd (by omega : q ≠ 1)
    have hrne : r ≠ q := by
      intro hrq
      exact hqprime (hrq ▸ hrprime)
    have hrle : r ≤ q := Nat.le_of_dvd (by omega) hrdvd
    have hrlt : r < q := lt_of_le_of_ne hrle hrne
    have ha0 : a ≠ 0 := by omega
    have h1mem : 1 ∈ a.divisors := Nat.one_mem_divisors.mpr ha0
    have h2mem : 2 ∈ a.divisors := Nat.mem_divisors.mpr ⟨heven, ha0⟩
    have hamem : a ∈ a.divisors := Nat.mem_divisors_self a ha0
    have hq_dvd : q ∣ a := by
      exact ⟨2, by rw [← haeq]; ring⟩
    have hqmem : q ∈ a.divisors := Nat.mem_divisors.mpr ⟨hq_dvd, ha0⟩
    have hcard : a.divisors.card ≤ 4 := by
      rwa [← sigma_zero_apply]
    by_cases hr2 : r = 2
    · subst r
      have h4dvd : 4 ∣ a := by
        obtain ⟨t, ht⟩ := hrdvd
        refine ⟨t, ?_⟩
        rw [← haeq, ht]
        ring
      have h4mem : 4 ∈ a.divisors := Nat.mem_divisors.mpr ⟨h4dvd, ha0⟩
      have hfive : 5 ≤ a.divisors.card := by
        apply five_le_card_of_chain_mem
          (a := 1) (b := 2) (c := 4) (d := q) (e := a)
        · norm_num
        · norm_num
        · exact hq4
        · omega
        · exact h1mem
        · exact h2mem
        · exact h4mem
        · exact hqmem
        · exact hamem
      omega
    · have h2r_dvd : 2 * r ∣ a := by
        obtain ⟨t, ht⟩ := hrdvd
        refine ⟨t, ?_⟩
        rw [← haeq, ht]
        ring
      have hr_dvd : r ∣ a := hrdvd.trans hq_dvd
      have hrmem : r ∈ a.divisors := Nat.mem_divisors.mpr ⟨hr_dvd, ha0⟩
      have h2rmem : 2 * r ∈ a.divisors := Nat.mem_divisors.mpr ⟨h2r_dvd, ha0⟩
      have hfive : 5 ≤ a.divisors.card := by
        apply five_le_card_of_chain_mem
          (a := 1) (b := 2) (c := r) (d := 2 * r) (e := a)
        · norm_num
        · exact lt_of_le_of_ne hrprime.two_le (Ne.symm hr2)
        · nlinarith [hrprime.two_le]
        · omega
        · exact h1mem
        · exact h2mem
        · exact hrmem
        · exact h2rmem
        · exact hamem
      omega

/-- Above the finite exceptional range, surviving shifts 1 and 2 is exactly
the Sophie Germain / safe-prime pattern. -/
theorem survives_depth_two_iff_safe_prime {n : ℕ} (hn : 10 < n) :
    (∀ j : ℕ, 0 < j → j ≤ 2 → j < n → sigma 0 (n - j) ≤ j + 2) ↔
      ∃ q : ℕ, q.Prime ∧ (2 * q + 1).Prime ∧ n = 2 * q + 2 := by
  constructor
  · intro H
    have h1 : sigma 0 (n - 1) ≤ 3 := by
      simpa using H 1 (by norm_num) (by norm_num) (by omega)
    have h2 : sigma 0 (n - 2) ≤ 4 := by
      simpa using H 2 (by norm_num) (by norm_num) (by omega)
    obtain ⟨p, hp, hp_case | hp_case⟩ :=
      prime_or_prime_square_of_sigma_zero_le_three (a := n - 1) (by omega) h1
    · have hcop : Nat.Coprime 2 p := by
        rw [Nat.prime_two.coprime_iff_not_dvd]
        rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hp]
        omega
      obtain ⟨t, ht⟩ := Nat.coprime_two_left.mp hcop
      have heven : 2 ∣ n - 2 := by
        refine ⟨t, ?_⟩
        omega
      obtain ⟨q, hq, hn2⟩ :=
        two_mul_prime_of_even_sigma_zero_le_four (a := n - 2)
          (by omega) heven h2
      refine ⟨q, hq, ?_, ?_⟩
      · have hqp : 2 * q + 1 = p := by omega
        simpa [hqp] using hp
      · omega
    · have hp5 : 5 ≤ p := by
        by_contra h
        have hp4 : p ≤ 4 := by omega
        interval_cases p
        · norm_num at hp
        · norm_num at hp
        · norm_num at hp_case
          omega
        · norm_num at hp_case
          omega
        · norm_num at hp
      have hbad := four_lt_sigma_zero_prime_square_sub_one hp hp5
      have hn2eq : n - 2 = p ^ 2 - 1 := by omega
      rw [hn2eq] at h2
      omega
  · rintro ⟨q, hq, hsafe, rfl⟩
    intro j hj0 hj2 hjn
    interval_cases j
    · have hsigma : sigma 0 (2 * q + 1) = 2 := by
        simpa using (sigma_zero_apply_prime_pow (i := 1) hsafe)
      have hsub : 2 * q + 2 - 1 = 2 * q + 1 := by omega
      rw [hsub, hsigma]
      norm_num
    · by_cases hq2 : q = 2
      · subst q
        native_decide
      · have hcop : Nat.Coprime 2 q := by
          rw [Nat.prime_two.coprime_iff_not_dvd]
          rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq]
          exact Ne.symm hq2
        have hmul :=
          (isMultiplicative_sigma (k := 0)).map_mul_of_coprime hcop
        have hs2 : sigma 0 2 = 2 := by
          simpa using (sigma_zero_apply_prime_pow (i := 1) Nat.prime_two)
        have hsq : sigma 0 q = 2 := by
          simpa using (sigma_zero_apply_prime_pow (i := 1) hq)
        rw [hs2, hsq] at hmul
        norm_num at hmul ⊢
        exact hmul.le

def SurvivesThrough (n D : ℕ) : Prop :=
  ∀ j : ℕ, 0 < j → j ≤ D → j < n → sigma 0 (n - j) ≤ j + 2

theorem shift_survivors_up_to_two :
    ∀ k : ℕ, k ≤ 2 → {n | SurvivesThrough n (k - 1)}.Infinite := by
  intro k hk
  by_cases hk2 : k = 2
  · subst k
    have hprime : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOf_prime
    have hinj : Set.InjOn (fun p : ℕ => p + 1) {p : ℕ | p.Prime} := by
      intro a _ b _ hab
      exact Nat.add_right_cancel hab
    have himage : ((fun p : ℕ => p + 1) '' {p : ℕ | p.Prime}).Infinite :=
      (Set.infinite_image_iff hinj).2 hprime
    apply himage.mono
    rintro n ⟨p, hp, rfl⟩
    intro j hj0 hjD hjn
    have hj : j = 1 := by omega
    subst j
    have hsigma : sigma 0 p = 2 := by
      simpa using (sigma_zero_apply_prime_pow (i := 1) hp)
    simp [hsigma]
  · have hk1 : k ≤ 1 := by omega
    have hall : {n : ℕ | SurvivesThrough n (k - 1)} = Set.univ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j hj0 hjD
      omega
    rw [hall]
    exact Set.infinite_univ

theorem shift_survivors_up_to_two_inline :
    ∀ k : ℕ, k ≤ 2 →
      {n | ∀ j : ℕ, 0 < j → j ≤ k - 1 → j < n →
        sigma 0 (n - j) ≤ j + 2}.Infinite := by
  intro k hk
  by_cases hk2 : k = 2
  · subst k
    have hprime : {p : ℕ | p.Prime}.Infinite := Nat.infinite_setOf_prime
    have hinj : Set.InjOn (fun p : ℕ => p + 1) {p : ℕ | p.Prime} := by
      intro a _ b _ hab
      exact Nat.add_right_cancel hab
    have himage : ((fun p : ℕ => p + 1) '' {p : ℕ | p.Prime}).Infinite :=
      (Set.infinite_image_iff hinj).2 hprime
    apply himage.mono
    rintro n ⟨p, hp, rfl⟩
    intro j hj0 hjD hjn
    have hj : j = 1 := by omega
    subst j
    have hsigma : sigma 0 p = 2 := by
      simpa using (sigma_zero_apply_prime_pow (i := 1) hp)
    simp [hsigma]
  · have hk1 : k ≤ 1 := by omega
    have hall :
        {n : ℕ | ∀ j : ℕ, 0 < j → j ≤ k - 1 → j < n →
          sigma 0 (n - j) ≤ j + 2} = Set.univ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro j hj0 hjD
      omega
    rw [hall]
    exact Set.infinite_univ

/-- The first genuinely open depth follows from the safe-prime conjecture. -/
theorem shift_survivors_through_depth_two_of_infinite_safe_primes
    (hsafe : {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}.Infinite) :
    {n | ∀ j : ℕ, 0 < j → j ≤ 2 → j < n →
      sigma 0 (n - j) ≤ j + 2}.Infinite := by
  have hinj : Set.InjOn (fun q : ℕ => 2 * q + 2)
      {q : ℕ | q.Prime ∧ (2 * q + 1).Prime} := by
    intro a _ b _ hab
    have hab' : 2 * a = 2 * b := Nat.add_right_cancel hab
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hab'
  have himage :
      ((fun q : ℕ => 2 * q + 2) ''
        {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}).Infinite :=
    (Set.infinite_image_iff hinj).2 hsafe
  apply himage.mono
  rintro n ⟨q, hq, rfl⟩
  intro j hj0 hj2 hjn
  interval_cases j
  · have hsafePrime : (2 * q + 1).Prime := hq.2
    have hsigma : sigma 0 (2 * q + 1) = 2 := by
      simpa using (sigma_zero_apply_prime_pow (i := 1) hsafePrime)
    have hsub : 2 * q + 2 - 1 = 2 * q + 1 := by omega
    rw [hsub, hsigma]
    norm_num
  · by_cases hq2 : q = 2
    · subst q
      native_decide
    · have hcop : Nat.Coprime 2 q := by
        rw [Nat.prime_two.coprime_iff_not_dvd]
        rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq.1]
        exact Ne.symm hq2
      have hmul :=
        (isMultiplicative_sigma (k := 0)).map_mul_of_coprime hcop
      have hs2 : sigma 0 2 = 2 := by
        simpa using (sigma_zero_apply_prime_pow (i := 1) Nat.prime_two)
      have hsq : sigma 0 q = 2 := by
        simpa using (sigma_zero_apply_prime_pow (i := 1) hq.1)
      rw [hs2, hsq] at hmul
      norm_num at hmul ⊢
      exact hmul.le

/-- The first non-vacuous infinite-window frontier is exactly the infinitude
of Sophie Germain primes. -/
theorem depth_two_survivors_infinite_iff_safe_primes :
    {n | ∀ j : ℕ, 0 < j → j ≤ 2 → j < n →
      sigma 0 (n - j) ≤ j + 2}.Infinite ↔
      {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}.Infinite := by
  constructor
  · intro hsurvivors
    by_contra hninf
    have hsafeFinite : {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}.Finite :=
      Set.not_infinite.mp hninf
    have himageFinite :
        ((fun q : ℕ => 2 * q + 2) ''
          {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}).Finite :=
      hsafeFinite.image _
    have hsmallFinite : {n : ℕ | n ≤ 10}.Finite := Set.finite_le_nat 10
    have hunionFinite :
        ({n : ℕ | n ≤ 10} ∪
          (fun q : ℕ => 2 * q + 2) ''
            {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}).Finite :=
      hsmallFinite.union himageFinite
    apply hsurvivors
    apply hunionFinite.subset
    intro n hn
    by_cases hn10 : n ≤ 10
    · exact Or.inl hn10
    · right
      obtain ⟨q, hq, hsafe, hnq⟩ :=
        (survives_depth_two_iff_safe_prime (n := n) (by omega)).mp hn
      exact ⟨q, ⟨hq, hsafe⟩, hnq.symm⟩
  · exact shift_survivors_through_depth_two_of_infinite_safe_primes

end Erdos647
