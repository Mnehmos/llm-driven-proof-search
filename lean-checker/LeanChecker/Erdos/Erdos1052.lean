import Mathlib

/-!
# Erdős Problem 1052 — unitary perfect numbers are even (Subbarao–Warren 1966)

Independent, self-contained proof of the `research solved` variant
`even_of_isUnitaryPerfect` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
`FormalConjectures/ErdosProblems/1052.lean`, where it carries a `sorry` plus a
link to an AlphaProof-generated proof (mzhorvath1 fork). That reference relies
on formal-conjectures' own tactic infrastructure (e.g. the custom `valid`
tactic) and an older toolchain and does not replay standalone; this file
depends only on Mathlib and verifies under lean4:v4.32.0-rc1 +
mathlib@360da6fa.

**Proof.** For a unitary divisor `d ∣ n` (`gcd(d, n/d) = 1`), the sum over all
unitary divisors factors at any prime `p ∣ n` as
`σ*(n) = (1 + p^{ν_p(n)}) · σ*(ordCompl_p n)` — realized here as a toggle
bijection on the `p`-divisible part (`sum_uDiv_factor`), with the `p`-free
part identified as the unitary divisors of the `p`-free part of `n`
(`filter_not_dvd_eq_uDiv_ordCompl`). If `n` is odd and unitary perfect then
`σ*(n) = 2n ≡ 2 (mod 4)`; but `1 + p^a` is even, and for the cofactor `> 1`
the fixed-point-free involution `d ↦ m/d` pairs odd values, so the second
factor is even too (`sum_uDiv_even`) — giving `4 ∣ 2n`, contradiction. The
prime-power cofactor case degenerates to `1 + p^a = 2p^a`, also impossible.

**Audit trail.** Proven end-to-end through the tracked pipeline: benchmark
problem `0279379a` (suite ErdosProblems-FormalConjectures `4c2b3e65`,
statement hash `6ea8f9fe…`, defs inlined definitionally), episode `2cc1e02a`,
kernel_verified pass@1, result `27534f5e`. Verify:
`lake env lean LeanChecker/Erdos/Erdos1052.lean`.
-/

namespace LeanChecker.Erdos1052

/-- All unitary divisors of `n`, including `1` and `n`. -/
def uDiv (n : ℕ) : Finset ℕ := n.divisors.filter (fun d => Nat.Coprime d (n / d))

lemma mem_uDiv {n d : ℕ} (hn : n ≠ 0) :
    d ∈ uDiv n ↔ d ∣ n ∧ Nat.Coprime d (n / d) := by
  simp [uDiv, Nat.mem_divisors, hn]

lemma self_mem_uDiv {n : ℕ} (hn : n ≠ 0) : n ∈ uDiv n := by
  rw [mem_uDiv hn]
  refine ⟨dvd_rfl, ?_⟩
  rw [Nat.div_self (Nat.pos_of_ne_zero hn)]
  exact Nat.coprime_one_right n

/-- The corpus's `properUnitaryDivisors n` equals `uDiv n` minus `n` itself. -/
lemma proper_eq_erase {n : ℕ} (hn : n ≠ 0) :
    ({d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)} : Finset ℕ) = (uDiv n).erase n := by
  ext d
  rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_erase, mem_uDiv hn]
  constructor
  · rintro ⟨⟨_, hlt⟩, hdvd, hcop⟩
    exact ⟨hlt.ne, hdvd, hcop⟩
  · rintro ⟨hne, hdvd, hcop⟩
    have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn)
    have hle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    exact ⟨⟨hpos, lt_of_le_of_ne hle hne⟩, hdvd, hcop⟩

/-- In a unitary divisor divisible by `p`, the FULL `p`-part of `n` divides. -/
lemma ordProj_dvd_of_mem_uDiv {n p d : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hd : d ∈ uDiv n) (hpd : p ∣ d) : ordProj[p] n ∣ d := by
  rw [mem_uDiv hn] at hd
  obtain ⟨hdvd, hcop⟩ := hd
  have hpnd : ¬ p ∣ (n / d) := fun hpnd =>
    hp.one_lt.ne' (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hpd hpnd))
  have h0 : (n / d).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpnd
  have happ : (n / d).factorization p = n.factorization p - d.factorization p := by
    rw [Nat.factorization_div hdvd]
    rfl
  have hle : n.factorization p ≤ d.factorization p :=
    Nat.sub_eq_zero_iff_le.mp (happ ▸ h0)
  calc ordProj[p] n = p ^ n.factorization p := rfl
    _ ∣ p ^ d.factorization p := pow_dvd_pow p hle
    _ ∣ d := Nat.ordProj_dvd d p

/-- Removing the full `p`-part of `n` from a divisor leaves it `p`-free. -/
lemma not_dvd_div_ordProj {n p d : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (hdvd : d ∣ n) (hPd : ordProj[p] n ∣ d) : ¬ p ∣ d / ordProj[p] n := by
  intro hpq
  have hd_eq : ordProj[p] n * (d / ordProj[p] n) = d := Nat.mul_div_cancel' hPd
  have hstep : p ^ (n.factorization p + 1) ∣ d := by
    rw [pow_succ, ← hd_eq]
    exact mul_dvd_mul_left _ hpq
  have hcontra := (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp (hstep.trans hdvd)
  omega

/-- The `p`-free unitary divisors of `n` are exactly the unitary divisors of
the `p`-free part `ordCompl[p] n`. -/
lemma filter_not_dvd_eq_uDiv_ordCompl {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    (uDiv n).filter (fun d => ¬ p ∣ d) = uDiv (ordCompl[p] n) := by
  have hm0 : (ordCompl[p] n) ≠ 0 := (Nat.ordCompl_pos p hn).ne'
  have hPm : ordProj[p] n * ordCompl[p] n = n := Nat.ordProj_mul_ordCompl_eq_self n p
  ext e
  rw [Finset.mem_filter, mem_uDiv hn, mem_uDiv hm0]
  constructor
  · rintro ⟨⟨hedvd, hcop⟩, hpe⟩
    have hcpe : Nat.Coprime e (ordProj[p] n) :=
      Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hpe).symm)
    have hem : e ∣ ordCompl[p] n := by
      refine hcpe.dvd_of_dvd_mul_left ?_
      rw [hPm]
      exact hedvd
    refine ⟨hem, ?_⟩
    have hne : n / e = ordProj[p] n * (ordCompl[p] n / e) := by
      rw [← Nat.mul_div_assoc _ hem, hPm]
    have hdd : ordCompl[p] n / e ∣ n / e := by
      rw [hne]
      exact dvd_mul_left _ _
    exact Nat.Coprime.coprime_dvd_right hdd hcop
  · rintro ⟨hem, hcop⟩
    have hpe : ¬ p ∣ e := fun hpe =>
      Nat.not_dvd_ordCompl hp hn (hpe.trans hem)
    have hedvd : e ∣ n := hem.trans (Nat.ordCompl_dvd n p)
    refine ⟨⟨hedvd, ?_⟩, hpe⟩
    have hne : n / e = ordProj[p] n * (ordCompl[p] n / e) := by
      rw [← Nat.mul_div_assoc _ hem, hPm]
    rw [hne]
    refine Nat.Coprime.mul_right ?_ hcop
    exact Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hpe).symm)

/-- **Factorization of the unitary-divisor sum at one prime**:
`∑_{d ∈ uDiv n} d = (1 + p^{ν_p(n)}) · ∑_{d ∈ uDiv n, p ∤ d} d`. -/
lemma sum_uDiv_factor {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) :
    (∑ d ∈ uDiv n, d)
      = (1 + ordProj[p] n) * (∑ d ∈ (uDiv n).filter (fun d => ¬ p ∣ d), d) := by
  have hPpos : 0 < ordProj[p] n := pow_pos hp.pos _
  have hPn : ordProj[p] n ∣ n := Nat.ordProj_dvd n p
  have ha : n.factorization p ≠ 0 := (hp.factorization_pos_of_dvd hn hpn).ne'
  have hsplit := Finset.sum_filter_add_sum_filter_not (uDiv n) (fun d => p ∣ d) (fun d => d)
  have hbij : (∑ d ∈ (uDiv n).filter (fun d => p ∣ d), d)
      = ordProj[p] n * (∑ d ∈ (uDiv n).filter (fun d => ¬ p ∣ d), d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (i := fun d _ => d / ordProj[p] n)
      (j := fun e _ => ordProj[p] n * e) ?_ ?_ ?_ ?_ ?_
    · -- hi : d / P lands in the p-free unitary divisors
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdU, hpd⟩ := hd
      have hPd : ordProj[p] n ∣ d := ordProj_dvd_of_mem_uDiv hn hp hdU hpd
      rw [mem_uDiv hn] at hdU
      obtain ⟨hdvd, hcop⟩ := hdU
      have hd0 : d ≠ 0 := fun h => hn (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
      have hdPd : d / ordProj[p] n ∣ d := Nat.div_dvd_of_dvd hPd
      have hdPn : d / ordProj[p] n ∣ n := hdPd.trans hdvd
      have hpdP : ¬ p ∣ d / ordProj[p] n := not_dvd_div_ordProj hn hp hdvd hPd
      have hdPpos : 0 < d / ordProj[p] n :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hPd) hPpos
      rw [Finset.mem_filter, mem_uDiv hn]
      refine ⟨⟨hdPn, ?_⟩, hpdP⟩
      have hmul : d / ordProj[p] n * (n / d * ordProj[p] n) = n := by
        rw [mul_comm (n / d) (ordProj[p] n), ← mul_assoc,
          Nat.div_mul_cancel hPd, Nat.mul_div_cancel' hdvd]
      have hquot : n / (d / ordProj[p] n) = n / d * ordProj[p] n := by
        nth_rewrite 1 [← hmul]
        exact Nat.mul_div_cancel_left _ hdPpos
      rw [hquot]
      refine Nat.Coprime.mul_right ?_ ?_
      · exact Nat.Coprime.coprime_dvd_left hdPd hcop
      · exact Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd.mpr hpdP).symm)
    · -- hj : P * e lands in the p-divisible unitary divisors
      intro e he
      rw [Finset.mem_filter] at he
      obtain ⟨heU, hpe⟩ := he
      rw [mem_uDiv hn] at heU
      obtain ⟨hedvd, hcop⟩ := heU
      have hcpe : Nat.Coprime (ordProj[p] n) e :=
        Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr hpe)
      have hPe_n : ordProj[p] n * e ∣ n := hcpe.mul_dvd_of_dvd_of_dvd hPn hedvd
      have hp_Pe : p ∣ ordProj[p] n * e :=
        Dvd.dvd.mul_right (dvd_pow_self p ha) e
      have hem : e ∣ ordCompl[p] n := by
        refine (hcpe.symm).dvd_of_dvd_mul_left ?_
        rw [Nat.ordProj_mul_ordCompl_eq_self n p]
        exact hedvd
      rw [Finset.mem_filter, mem_uDiv hn]
      refine ⟨⟨hPe_n, ?_⟩, hp_Pe⟩
      have hquot : n / (ordProj[p] n * e) = ordCompl[p] n / e :=
        (Nat.div_div_eq_div_mul n (ordProj[p] n) e).symm
      have hmfree : ¬ p ∣ (ordCompl[p] n / e) := fun h =>
        Nat.not_dvd_ordCompl hp hn (h.trans (Nat.div_dvd_of_dvd hem))
      rw [hquot]
      refine Nat.Coprime.mul_left ?_ ?_
      · exact Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr hmfree)
      · have hne : n / e = ordProj[p] n * (ordCompl[p] n / e) := by
          rw [← Nat.mul_div_assoc _ hem, Nat.ordProj_mul_ordCompl_eq_self n p]
        have hdd : ordCompl[p] n / e ∣ n / e := by
          rw [hne]
          exact dvd_mul_left _ _
        exact Nat.Coprime.coprime_dvd_right hdd hcop
    · -- left inverse : P * (d / P) = d
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Nat.mul_div_cancel' (ordProj_dvd_of_mem_uDiv hn hp hd.1 hd.2)
    · -- right inverse : (P * e) / P = e
      intro e _
      exact Nat.mul_div_cancel_left e hPpos
    · -- values agree : d = P * (d / P)
      intro d hd
      rw [Finset.mem_filter] at hd
      exact (Nat.mul_div_cancel' (ordProj_dvd_of_mem_uDiv hn hp hd.1 hd.2)).symm
  rw [add_mul, one_mul, ← hbij]
  omega

/-- Unitary divisors of an odd `m > 1` have even sum: the fixed-point-free
involution `d ↦ m / d` pairs odd values. -/
lemma sum_uDiv_even {m : ℕ} (hm : 1 < m) (hodd : Odd m) :
    2 ∣ (∑ d ∈ uDiv m, d) := by
  have hm0 : m ≠ 0 := by omega
  have heven : Even (∑ d ∈ uDiv m, d) := by
    rw [← ZMod.natCast_eq_zero_iff_even]
    push_cast
    refine Finset.sum_involution (g := fun e _ => m / e) ?_ ?_ ?_ ?_
    · -- pair sums vanish in ZMod 2 : both entries odd
      intro e he
      rw [mem_uDiv hm0] at he
      have hoe : Odd e := by
        rcases Nat.even_or_odd e with h2 | h2
        · have hdm : (2 : ℕ) ∣ m := h2.two_dvd.trans he.1
          rw [Nat.odd_iff] at hodd
          omega
        · exact h2
      have hom : Odd (m / e) := by
        rcases Nat.even_or_odd (m / e) with h2 | h2
        · have hdm : (2 : ℕ) ∣ m := h2.two_dvd.trans (Nat.div_dvd_of_dvd he.1)
          rw [Nat.odd_iff] at hodd
          omega
        · exact h2
      show ((e : ZMod 2) + ((m / e : ℕ) : ZMod 2)) = 0
      rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff_even]
      exact hoe.add_odd hom
    · -- no fixed points among nonzero contributions
      intro e he _ heq
      rw [mem_uDiv hm0] at he
      have hee := Nat.div_mul_cancel he.1
      rw [heq] at hee
      have hedvd : e ∣ m / e := by
        rw [heq]
      have h1 : e = 1 := Nat.dvd_one.mp (he.2 ▸ Nat.dvd_gcd dvd_rfl hedvd)
      rw [h1] at hee
      omega
    · -- the involution stays inside uDiv m
      intro e he
      show m / e ∈ uDiv m
      rw [mem_uDiv hm0] at he ⊢
      refine ⟨Nat.div_dvd_of_dvd he.1, ?_⟩
      rw [Nat.div_div_self he.1 hm0]
      exact he.2.symm
    · -- involutive
      intro e he
      show m / (m / e) = e
      rw [mem_uDiv hm0] at he
      exact Nat.div_div_self he.1 hm0
  exact heven.two_dvd

/-- **Erdős 1052 solved variant (Subbarao–Warren 1966)**: unitary perfect
numbers are even. Statement matches the corpus with definitions inlined. -/
theorem even_of_isUnitaryPerfect (n : ℕ)
    (h : (∑ i ∈ ({d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)} : Finset ℕ), i) = n ∧ 0 < n) :
    Even n := by
  obtain ⟨hsum, hpos⟩ := h
  by_contra heven
  rw [Nat.not_even_iff_odd] at heven
  have hn0 : n ≠ 0 := hpos.ne'
  have hn1 : n ≠ 1 := by
    rintro rfl
    simp at hsum
  have hgt : 1 < n := by omega
  have htotal : (∑ d ∈ uDiv n, d) = 2 * n := by
    rw [proper_eq_erase hn0] at hsum
    have hadd := Finset.add_sum_erase (uDiv n) (fun d => d) (self_mem_uDiv hn0)
    omega
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime hn1
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.odd_iff] at heven
    have h2n : (2 : ℕ) ∣ n := h2 ▸ hpn
    omega
  have hfac := sum_uDiv_factor hn0 hp hpn
  rw [filter_not_dvd_eq_uDiv_ordCompl hn0 hp, htotal] at hfac
  have hPodd : Odd (ordProj[p] n) := (hp.odd_of_ne_two hp2).pow
  have h1P : (2 : ℕ) ∣ (1 + ordProj[p] n) := by
    obtain ⟨k, hk⟩ := hPodd
    omega
  have hm1 : 1 ≤ ordCompl[p] n := Nat.ordCompl_pos p hn0
  rcases eq_or_lt_of_le hm1 with hm | hm
  · -- ordCompl = 1 : n is an odd prime power; forces P = 1, absurd
    have hS1 : (∑ d ∈ uDiv (ordCompl[p] n), d) = 1 := by
      rw [← hm]
      decide
    have hnP : ordProj[p] n * ordCompl[p] n = n := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [← hm, mul_one] at hnP
    have hPge : 2 ≤ ordProj[p] n := by
      have ha : n.factorization p ≠ 0 := (hp.factorization_pos_of_dvd hn0 hpn).ne'
      have hle := Nat.le_self_pow ha p
      have h2le := hp.two_le
      omega
    rw [hS1, mul_one] at hfac
    omega
  · -- ordCompl > 1 : both factors even → 4 ∣ 2n → n even, contradiction
    have hmodd : Odd (ordCompl[p] n) := by
      have hmn : ordCompl[p] n ∣ n := Nat.ordCompl_dvd n p
      rcases Nat.even_or_odd (ordCompl[p] n) with h2 | h2
      · rw [Nat.odd_iff] at heven
        have h2n : (2 : ℕ) ∣ n := h2.two_dvd.trans hmn
        omega
      · exact h2
    have hSeven : (2 : ℕ) ∣ (∑ d ∈ uDiv (ordCompl[p] n), d) := sum_uDiv_even hm hmodd
    obtain ⟨u, hu⟩ := h1P
    obtain ⟨v, hv⟩ := hSeven
    rw [hu, hv] at hfac
    have h4 : 2 * n = 4 * (u * v) := by
      rw [hfac]
      ring
    rw [Nat.odd_iff] at heven
    omega

end LeanChecker.Erdos1052
