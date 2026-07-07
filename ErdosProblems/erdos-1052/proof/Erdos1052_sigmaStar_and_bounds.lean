import Mathlib

/-!
Erdős #1052 cluster — new work beyond the corpus's stated goal (Subbarao-Warren
evenness proof lives in Erdos1052_even_of_isUnitaryPerfect.lean / the living
lean-checker/LeanChecker/Erdos/Erdos1052.lean). This snapshot: sigmaStar
multiplicativity, fast verification of 87360 and Wall's 24-digit unitary
perfect number, and the omega_odd_le_two_adic_add_one structural bound.
-/

namespace LeanChecker.Erdos1052

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

def sigmaStar (n : ℕ) : ℕ := ∑ d ∈ uDiv n, d

theorem split_dvd_mul {m n d : ℕ} (hmn : m.Coprime n) (hd : d ∣ m * n) :
    Nat.gcd d m * Nat.gcd d n = d :=
  (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hmn).mpr hd

theorem quot_mul_quot {x y a b : ℕ} (ha : a ∣ x) (hb : b ∣ y) :
    (x / a) * (y / b) = x * y / (a * b) := by
  obtain ⟨x', rfl⟩ := ha
  obtain ⟨y', rfl⟩ := hb
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb0
  · simp
  rw [Nat.mul_div_cancel_left _ ha0, Nat.mul_div_cancel_left _ hb0]
  rw [show a * x' * (b * y') = (a * b) * (x' * y') by ring]
  rw [Nat.mul_div_cancel_left _ (Nat.mul_pos ha0 hb0)]

theorem gcd_mul_left_eq {x y a b : ℕ} (ha : a ∣ x) (hb : b ∣ y) (hxy : x.Coprime y) :
    Nat.gcd (a * b) x = a := by
  have hbx : b.Coprime x := (hxy.symm.coprime_dvd_left hb)
  refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (Dvd.intro b rfl) ha)
  have hcop : (Nat.gcd (a * b) x).Coprime b :=
    (hbx.coprime_dvd_right (Nat.gcd_dvd_right (a * b) x)).symm
  exact hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_left (a * b) x)

/-- **σ* is multiplicative**: for coprime `m, n` (both nonzero), `σ*(mn) = σ*(m)·σ*(n)`.
Built from scratch — Mathlib has no unitary-divisor-sum multiplicativity. -/
theorem sigmaStar_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  unfold sigmaStar
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun d => (Nat.gcd d m, Nat.gcd d n)) (fun p => p.1 * p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_uDiv hmn0] at hd
    obtain ⟨hddvd, hdcop⟩ := hd
    have hsplit := split_dvd_mul hmn hddvd
    have hg1dvd : Nat.gcd d m ∣ m := Nat.gcd_dvd_right d m
    have hg2dvd : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
    have hquot : (m / Nat.gcd d m) * (n / Nat.gcd d n) = m * n / d := by
      rw [quot_mul_quot hg1dvd hg2dvd, hsplit]
    have hcop1 : Nat.gcd (Nat.gcd d m) (m / Nat.gcd d m) ∣ Nat.gcd d (m * n / d) := by
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left (Nat.gcd d m) (m / Nat.gcd d m)).trans (Nat.gcd_dvd_left d m)
      · refine (Nat.gcd_dvd_right (Nat.gcd d m) (m / Nat.gcd d m)).trans ?_
        rw [← hquot]; exact dvd_mul_right _ _
    have hcop2 : Nat.gcd (Nat.gcd d n) (n / Nat.gcd d n) ∣ Nat.gcd d (m * n / d) := by
      apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left (Nat.gcd d n) (n / Nat.gcd d n)).trans (Nat.gcd_dvd_left d n)
      · refine (Nat.gcd_dvd_right (Nat.gcd d n) (n / Nat.gcd d n)).trans ?_
        rw [← hquot]; exact dvd_mul_left _ _
    have hdcop1 : Nat.gcd d (m * n / d) = 1 := hdcop
    simp only [Finset.mem_product]
    exact ⟨(mem_uDiv hm).mpr ⟨hg1dvd, Nat.dvd_one.mp (hdcop1 ▸ hcop1)⟩,
           (mem_uDiv hn).mpr ⟨hg2dvd, Nat.dvd_one.mp (hdcop1 ▸ hcop2)⟩⟩
  · intro p hp
    simp only [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [mem_uDiv hm] at hp1
    rw [mem_uDiv hn] at hp2
    obtain ⟨hd1dvd, hd1cop⟩ := hp1
    obtain ⟨hd2dvd, hd2cop⟩ := hp2
    rw [mem_uDiv hmn0]
    refine ⟨Nat.mul_dvd_mul hd1dvd hd2dvd, ?_⟩
    have hquot : (m / p.1) * (n / p.2) = m * n / (p.1 * p.2) := quot_mul_quot hd1dvd hd2dvd
    rw [← hquot]
    have hcross1 : p.1.Coprime (n / p.2) :=
      (hmn.coprime_dvd_left hd1dvd).coprime_dvd_right (Nat.div_dvd_of_dvd hd2dvd)
    have hcross2 : p.2.Coprime (m / p.1) :=
      ((hmn.coprime_dvd_right hd2dvd).coprime_dvd_left (Nat.div_dvd_of_dvd hd1dvd)).symm
    exact (hd1cop.mul_right hcross1).mul (hcross2.mul_right hd2cop)
  · intro d hd
    rw [mem_uDiv hmn0] at hd
    exact split_dvd_mul hmn hd.1
  · intro p hp
    simp only [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [mem_uDiv hm] at hp1
    rw [mem_uDiv hn] at hp2
    have e1 : Nat.gcd (p.1 * p.2) m = p.1 := gcd_mul_left_eq hp1.1 hp2.1 hmn
    have e2 : Nat.gcd (p.1 * p.2) n = p.2 := by
      rw [mul_comm]; exact gcd_mul_left_eq hp2.1 hp1.1 hmn.symm
    exact Prod.ext e1 e2
  · intro d hd
    rw [mem_uDiv hmn0] at hd
    exact (split_dvd_mul hmn hd.1).symm

/-- **σ* on a prime power**: `σ*(p^e) = p^e + 1`. -/
theorem sigmaStar_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    sigmaStar (p ^ e) = p ^ e + 1 := by
  have hpe : p ^ e ≠ 0 := (pow_pos hp.pos e).ne'
  unfold sigmaStar
  have heq : uDiv (p ^ e) = {1, p ^ e} := by
    ext d
    rw [mem_uDiv hpe]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hdvd, hcop⟩
      obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · left; simp
      · right
        by_contra hne
        have hklt : k < e := by
          rcases lt_or_eq_of_le hk with h | h
          · exact h
          · exact absurd (by rw [h]) hne
        have hexp : p ^ e = p ^ k * p ^ (e - k) := by
          rw [← pow_add]; congr 1; omega
        have hp_dvd_quot : p ∣ p ^ e / p ^ k := by
          rw [hexp, Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
          exact dvd_pow_self p (Nat.sub_ne_zero_of_lt hklt)
        have hp_dvd_self : p ∣ p ^ k := dvd_pow_self p hk0.ne'
        have hcontra : p ∣ Nat.gcd (p ^ k) (p ^ e / p ^ k) := Nat.dvd_gcd hp_dvd_self hp_dvd_quot
        rw [hcop] at hcontra
        exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one hcontra) |>.elim
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, by simp⟩
      · exact ⟨dvd_refl _, by simp [Nat.div_self (Nat.pos_of_ne_zero hpe)]⟩
  rw [heq]
  have h1e : (1:ℕ) ≠ p ^ e := by
    have : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  rw [Finset.sum_insert (Finset.mem_singleton.not.mpr h1e), Finset.sum_singleton]
  omega

theorem sigmaStar_prime {p : ℕ} (hp : p.Prime) : sigmaStar p = p + 1 := by
  have := sigmaStar_prime_pow hp (le_refl 1)
  simpa using this

/-- **Fast verification of `87360`** (the corpus's own test is disabled with `stop`,
"too slow" via naive divisor enumeration; this is exponentially fewer steps). -/
theorem isUnitaryPerfect_87360_fast : sigmaStar 87360 = 2 * 87360 := by
  have h1 : (87360:ℕ) = 2 ^ 6 * (3 * (5 * (7 * 13))) := by norm_num
  rw [h1]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime_pow (by norm_num) (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num), sigmaStar_prime (by norm_num)]
  norm_num

/-- **Fast verification of Wall's fifth unitary perfect number** (the corpus's own
test is a bare `sorry` with only an external, non-replaying formal_proof link). -/
theorem isUnitaryPerfect_wall_fast :
    sigmaStar 146361946186458562560000 = 2 * 146361946186458562560000 := by
  have h1 : (146361946186458562560000:ℕ)
      = 2 ^ 18 * (3 * (5 ^ 4 * (7 * (11 * (13 * (19 * (37 * (79 * (109 * (157 * 313)))))))))) := by
    norm_num
  rw [h1]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime_pow (by norm_num) (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime_pow (by norm_num) (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num)]
  rw [sigmaStar_mul_of_coprime (by norm_num) (by norm_num) (by norm_num),
      sigmaStar_prime (by norm_num), sigmaStar_prime (by norm_num)]
  norm_num

/-- Connects `sigmaStar n = 2n` to the corpus's `IsUnitaryPerfect` shape
(`∑ properUnitaryDivisors n = n ∧ 0 < n`), using the file's own `proper_eq_erase`
and the fact that `n` is always a unitary divisor of itself. -/
theorem isUnitaryPerfect_of_sigmaStar {n : ℕ} (hn : 0 < n) (h : sigmaStar n = 2 * n) :
    (∑ i ∈ ({d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)} : Finset ℕ), i) = n ∧ 0 < n := by
  refine ⟨?_, hn⟩
  rw [proper_eq_erase hn.ne']
  have hadd := Finset.add_sum_erase (uDiv n) (fun d => d) (self_mem_uDiv hn.ne')
  unfold sigmaStar at h
  omega

/-- **`87360` is unitary perfect**, matching the corpus's exact statement shape —
fills the corpus's `stop`-disabled test, proven fast via multiplicativity. -/
theorem isUnitaryPerfect_87360 :
    (∑ i ∈ ({d ∈ Finset.Ico 1 87360 | d ∣ 87360 ∧ d.Coprime (87360 / d)} : Finset ℕ), i)
      = 87360 ∧ 0 < 87360 :=
  isUnitaryPerfect_of_sigmaStar (by norm_num) isUnitaryPerfect_87360_fast

/-- **Wall's fifth unitary perfect number, verified**, matching the corpus's exact
statement shape — fills the corpus's bare `sorry`, proven fast via multiplicativity. -/
theorem isUnitaryPerfect_wall :
    (∑ i ∈ ({d ∈ Finset.Ico 1 146361946186458562560000 |
        d ∣ 146361946186458562560000 ∧ d.Coprime (146361946186458562560000 / d)} : Finset ℕ), i)
      = 146361946186458562560000 ∧ 0 < 146361946186458562560000 :=
  isUnitaryPerfect_of_sigmaStar (by norm_num) isUnitaryPerfect_wall_fast

/-- **The odd-prime-factor-count bound.** For `m` odd, `2 ^ m.primeFactors.card ∣ σ*(m)`.
Proved by strong induction: peel off the full power of the smallest prime factor at
each step. -/
theorem two_pow_card_primeFactors_dvd_sigmaStar :
    ∀ m : ℕ, Odd m → 2 ^ m.primeFactors.card ∣ sigmaStar m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmodd
    rcases eq_or_ne m 1 with rfl | hm1
    · simp [sigmaStar, uDiv]
    have hm0 : m ≠ 0 := by rintro rfl; simp at hmodd
    set p := m.minFac with hpdef
    have hp : p.Prime := Nat.minFac_prime hm1
    have hpodd : p ≠ 2 := by
      intro hp2
      have h2dvd : (2:ℕ) ∣ m := hp2 ▸ Nat.minFac_dvd m
      rw [Nat.odd_iff] at hmodd
      rw [Nat.dvd_iff_mod_eq_zero] at h2dvd
      omega
    set e := m.factorization p with hedef
    have he1 : 1 ≤ e := by
      rw [hedef, ← Nat.Prime.dvd_iff_one_le_factorization hp hm0]
      exact Nat.minFac_dvd m
    set m' := ordCompl[p] m with hm'def
    have hsplit : ordProj[p] m * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
    have hprojeq : ordProj[p] m = p ^ e := rfl
    have hm'pos : 0 < m' := Nat.ordCompl_pos p hm0
    have hcopm' : p.Coprime m' := Nat.coprime_ordCompl hp hm0
    have hm'odd : Odd m' := by
      rcases Nat.even_or_odd m' with he' | ho'
      · exfalso
        have h2dvd : (2:ℕ) ∣ m' := he'.two_dvd
        have : (2:ℕ) ∣ m := h2dvd.trans (Dvd.intro_left _ hsplit)
        rw [Nat.odd_iff] at hmodd; omega
      · exact ho'
    have hm'lt : m' < m := by
      rw [← hsplit, hprojeq]
      have hpge : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      nlinarith [hm'pos]
    have hcard : m.primeFactors.card = m'.primeFactors.card + 1 := by
      have hpf : m.primeFactors = insert p m'.primeFactors := by
        rw [← hsplit, hprojeq]
        rw [Nat.primeFactors_mul (pow_pos hp.pos e).ne' hm'pos.ne']
        rw [Nat.primeFactors_prime_pow (by omega) hp]
        rw [Finset.singleton_union]
      rw [hpf, Finset.card_insert_of_notMem]
      intro hmem
      exact absurd hmem (by
        rw [Nat.mem_primeFactors]
        push_neg
        intro _
        exact fun h => absurd h (by
          have := hcopm'.symm
          rwa [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp] at this))
    have hihm' := ih m' hm'lt hm'odd
    have hmulcop : (p ^ e).Coprime m' := hcopm'.pow_left e
    have hsigma_eq : sigmaStar m = (p ^ e + 1) * sigmaStar m' := by
      rw [← hsplit, hprojeq, sigmaStar_mul_of_coprime (pow_pos hp.pos e).ne' hm'pos.ne' hmulcop,
          sigmaStar_prime_pow hp he1]
    have hpe_even : Even (p ^ e + 1) := by
      have : Odd (p ^ e) := (Nat.Prime.odd_of_ne_two hp hpodd).pow
      rcases this with ⟨k, hk⟩
      exact ⟨k + 1, by omega⟩
    rw [hcard, hsigma_eq]
    obtain ⟨c, hc⟩ := hpe_even
    rw [hc]
    have hre : (c + c) * sigmaStar m' = 2 * (c * sigmaStar m') := by ring
    rw [hre, pow_succ']
    exact Nat.mul_dvd_mul_left 2 (hihm'.mul_left c)

/-- **The headline bound.** If `2^a * m` (with `m` odd, `a ≥ 1`) is a unitary perfect
number (`sigmaStar = 2n`), then the number of distinct odd prime factors of `m` is at
most `a + 1`. Combined with Wall's 1988 theorem (≥ 9 odd prime factors needed for a
sixth unitary perfect number), this forces `a ≥ 8`: any sixth unitary perfect number
is divisible by at least `2^8 = 256`. This narrows the search space; it does not
resolve the open finiteness question. -/
theorem omega_odd_le_two_adic_add_one (a m : ℕ) (hm_odd : Odd m) (ha : 0 < a)
    (hperfect : sigmaStar (2 ^ a * m) = 2 * (2 ^ a * m)) :
    m.primeFactors.card ≤ a + 1 := by
  have hm0 : m ≠ 0 := hm_odd.pos.ne'
  have h2apos : (2:ℕ) ^ a ≠ 0 := (pow_pos (by norm_num) a).ne'
  have hcop2 : (2:ℕ).Coprime m := (Nat.coprime_two_left).mpr hm_odd
  have hcop : (2 ^ a).Coprime m := hcop2.pow_left a
  have heq : sigmaStar (2 ^ a) * sigmaStar m = 2 * (2 ^ a * m) := by
    rw [← sigmaStar_mul_of_coprime h2apos hm0 hcop]; exact hperfect
  rw [sigmaStar_prime_pow (by norm_num) ha] at heq
  have hrhs : 2 * (2 ^ a * m) = 2 ^ (a + 1) * m := by rw [pow_succ']; ring
  rw [hrhs] at heq
  have hseedk : ∃ k, (2:ℕ) ^ a = 2 * k := ⟨2 ^ (a - 1), by rw [← pow_succ']; congr 1; omega⟩
  obtain ⟨k, hk⟩ := hseedk
  have hodd_seed : ¬ (2 ∣ 2 ^ a + 1) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hmmod := Nat.odd_iff.mp hm_odd
  have hnot2m : ¬ (2 ∣ m) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
  have hsm0 : sigmaStar m ≠ 0 := by
    intro h0; rw [h0, mul_zero] at heq
    have : (0:ℕ) < 2 ^ (a + 1) * m := by positivity
    omega
  have hne1 : (2:ℕ) ^ a + 1 ≠ 0 := by positivity
  have hne2 : (2:ℕ) ^ (a + 1) ≠ 0 := by positivity
  have hfactL : ((2 ^ a + 1) * sigmaStar m).factorization 2
      = (2 ^ a + 1).factorization 2 + (sigmaStar m).factorization 2 := by
    have h := congrArg (fun f => f 2) (Nat.factorization_mul hne1 hsm0)
    simpa using h
  have hfactR : ((2:ℕ) ^ (a + 1) * m).factorization 2
      = ((2:ℕ) ^ (a + 1)).factorization 2 + m.factorization 2 := by
    have h := congrArg (fun f => f 2) (Nat.factorization_mul hne2 hm0)
    simpa using h
  have hcongr : (2 ^ a + 1).factorization 2 + (sigmaStar m).factorization 2
      = ((2:ℕ) ^ (a + 1)).factorization 2 + m.factorization 2 := by
    rw [← hfactL, ← hfactR, heq]
  have h1 : (2 ^ a + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hodd_seed
  have h2 : m.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnot2m
  have h3 : ((2:ℕ) ^ (a + 1)).factorization 2 = a + 1 :=
    Nat.factorization_pow_self (by norm_num)
  rw [h1, h3, h2] at hcongr
  have hval : (sigmaStar m).factorization 2 = a + 1 := by omega
  have := (Nat.Prime.pow_dvd_iff_le_factorization (p := 2) (by norm_num) hsm0).mp
    (two_pow_card_primeFactors_dvd_sigmaStar m hm_odd)
  omega


end LeanChecker.Erdos1052
