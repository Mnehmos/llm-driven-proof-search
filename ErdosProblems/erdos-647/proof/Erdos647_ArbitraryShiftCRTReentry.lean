import Mathlib

/-!
# Erdős #647 — arbitrary-shift CRT re-entry

The earlier CRT re-entry theorem was indexed by a consecutive prefix.  The
exact base survivor state naturally supplies primes at shifts `5,7,9,10`.
This theorem removes that mismatch: any finite injective family of prime
divisors at arbitrary positive shifts can be multiplied and re-entered through
the remainder modulo their product.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- Arbitrary-shift CRT re-entry bound in the exact Formal Conjectures
candidate language. -/
theorem erdos647_arbitrary_shift_crt_reentry_bound :
    ∀ (n r : ℕ) (shift P : Fin r → ℕ),
      0 < r →
      Function.Injective P →
      (∀ i : Fin r,
        (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
          shift i < n ∧ P i ∣ n - shift i) →
      (∏ i : Fin r, P i) < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      2 ^ r ≤ n % (∏ i : Fin r, P i) + 2 := by
  classical
  intro n r shift P hr hinj hP hQn hcand
  let Q : ℕ := ∏ i : Fin r, P i
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun i _ => (hP i).1.pos
  have hPiQ : ∀ i : Fin r, P i ∣ Q := by
    intro i
    dsimp [Q]
    exact Finset.dvd_prod_of_mem P (Finset.mem_univ i)
  have hQnotdvd : ¬ Q ∣ n := by
    intro hQdvd
    let i : Fin r := ⟨0, hr⟩
    have hPin : P i ∣ n := (hPiQ i).trans hQdvd
    have hPshift : P i ∣ shift i := by
      have h := Nat.dvd_sub hPin (hP i).2.2.2.2
      have hrecover : n - shift i + shift i = n :=
        Nat.sub_add_cancel (hP i).2.2.2.1.le
      have heq : n - (n - shift i) = shift i := by omega
      rwa [heq] at h
    have hPle : P i ≤ shift i := Nat.le_of_dvd (hP i).2.1 hPshift
    exact (not_lt_of_ge hPle) (hP i).2.2.1
  have hrne : n % Q ≠ 0 := by
    intro hz
    exact hQnotdvd (Nat.dvd_iff_mod_eq_zero.mpr hz)
  have hrpos : 0 < n % Q := Nat.pos_of_ne_zero hrne
  have hrltQ : n % Q < Q := Nat.mod_lt n hQpos
  have hrltN : n % Q < n := lt_trans hrltQ hQn
  have hQhost : Q ∣ n - n % Q := by
    refine ⟨n / Q, ?_⟩
    have hdecomp := Nat.mod_add_div n Q
    omega
  have hhostpos : 0 < n - n % Q := by omega
  let S : Finset ℕ := Finset.univ.image P
  have hScard : S.card = r := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hS : ∀ p ∈ S, p.Prime ∧ p ∣ n - n % Q := by
    intro p hp
    dsimp [S] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact ⟨(hP i).1, (hPiQ i).trans hQhost⟩
  have htau : 2 ^ r ≤ ArithmeticFunction.sigma 0 (n - n % Q) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hhostpos.ne']
    have hsubset : S ⊆ (n - n % Q).primeFactors := by
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2,
        hhostpos.ne'⟩
    have hcard : S.card ≤ (n - n % Q).primeFactors.card :=
      Finset.card_le_card hsubset
    have hpow : 2 ^ (n - n % Q).primeFactors.card ≤
        ∏ p ∈ (n - n % Q).primeFactors,
          ((n - n % Q).factorization p + 1) := by
      apply Finset.pow_card_le_prod
      intro p hp
      have hp' : p ∈ (n - n % Q).factorization.support := by simpa using hp
      have hfac : (n - n % Q).factorization p ≠ 0 :=
        Finsupp.mem_support_iff.mp hp'
      omega
    rw [← hScard]
    exact (pow_le_pow_right' (by norm_num) hcard).trans hpow
  let f : Fin n → ℕ := fun x =>
    (x : ℕ) + ArithmeticFunction.sigma 0 x
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨2 * n, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [f]
    rw [ArithmeticFunction.sigma_zero_apply]
    have hc := Nat.card_divisors_le_self (x : ℕ)
    have hx : (x : ℕ) < n := x.isLt
    omega
  let m : Fin n := ⟨n - n % Q, by omega⟩
  have hm : f m ≤ n + 2 := le_trans (le_ciSup hbdd m) hcand
  dsimp [f, m] at hm
  have hbudget : ArithmeticFunction.sigma 0 (n - n % Q) ≤ n % Q + 2 := by
    omega
  exact htau.trans hbudget

/-- Distinct shift residues cannot both be represented by a remainder smaller
than their associated primes.  Thus every pair of different coordinates has
at least one selected prime bounded by the CRT remainder. -/
theorem erdos647_arbitrary_shift_remainder_dominates_pair :
    ∀ (n r : ℕ) (shift P : Fin r → ℕ),
      0 < r →
      (∀ i : Fin r,
        (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
          shift i < n ∧ P i ∣ n - shift i) →
      ∀ i j : Fin r, shift i ≠ shift j →
        P i ≤ n % (∏ k : Fin r, P k) ∨
          P j ≤ n % (∏ k : Fin r, P k) := by
  classical
  intro n r shift P hr hP i j hshift
  let Q : ℕ := ∏ k : Fin r, P k
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun k _ => (hP k).1.pos
  have hPkQ : ∀ k : Fin r, P k ∣ Q := by
    intro k
    dsimp [Q]
    exact Finset.dvd_prod_of_mem P (Finset.mem_univ k)
  have hresidue : ∀ k : Fin r, (n % Q) % P k = shift k := by
    intro k
    have hsplit : n = shift k + (n - shift k) := by
      simpa [Nat.add_comm] using
        (Nat.sub_add_cancel (hP k).2.2.2.1.le).symm
    have hmodzero : (n - shift k) % P k = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (hP k).2.2.2.2
    calc
      (n % Q) % P k = n % P k := Nat.mod_mod_of_dvd n (hPkQ k)
      _ = (shift k + (n - shift k)) % P k := by rw [← hsplit]
      _ = shift k := by
        simpa [Nat.add_mod, hmodzero] using
          (Nat.mod_eq_of_lt (hP k).2.2.1)
  by_cases hiBound : P i ≤ n % Q
  · exact Or.inl hiBound
  right
  by_contra hjBound
  have hiLt : n % Q < P i := Nat.lt_of_not_ge hiBound
  have hjLt : n % Q < P j := Nat.lt_of_not_ge hjBound
  have hi : n % Q = shift i := by
    have := hresidue i
    rwa [Nat.mod_eq_of_lt hiLt] at this
  have hj : n % Q = shift j := by
    have := hresidue j
    rwa [Nat.mod_eq_of_lt hjLt] at this
  exact hshift (hi.symm.trans hj)

/-- Four-rung specialization at the exact shifts produced by the normalized
base state. -/
theorem erdos647_base_four_prime_crt_reentry_bound :
    ∀ n p5 p7 p9 p10 : ℕ,
      p5.Prime → 10 < p5 → p5 ∣ n - 5 →
      p7.Prime → 10 < p7 → p7 ∣ n - 7 →
      p9.Prime → 10 < p9 → p9 ∣ n - 9 →
      p10.Prime → 10 < p10 → p10 ∣ n - 10 →
      p5 ≠ p7 → p5 ≠ p9 → p5 ≠ p10 →
      p7 ≠ p9 → p7 ≠ p10 → p9 ≠ p10 →
      p5 * p7 * p9 * p10 < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      16 ≤ n % (p5 * p7 * p9 * p10) + 2 := by
  intro n p5 p7 p9 p10
    hp5 hp5large hp5dvd hp7 hp7large hp7dvd
    hp9 hp9large hp9dvd hp10 hp10large hp10dvd
    h57 h59 h510 h79 h710 h910 hprod hcand
  let shift : Fin 4 → ℕ := ![5, 7, 9, 10]
  let P : Fin 4 → ℕ := ![p5, p7, p9, p10]
  have hinj : Function.Injective P := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [P]
  have hP : ∀ i : Fin 4,
      (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
        shift i < n ∧ P i ∣ n - shift i := by
    intro i
    have hp5le : p5 ≤ p5 * p7 * p9 * p10 := by
      apply Nat.le_of_dvd (by positivity)
      exact ⟨p7 * p9 * p10, by ring⟩
    have hn : 10 < n := lt_of_lt_of_le hp5large (hp5le.trans hprod.le)
    fin_cases i <;> simp [P, shift, hp5, hp5dvd,
      hp7, hp7dvd, hp9, hp9dvd, hp10, hp10dvd] <;> omega
  have hcore := erdos647_arbitrary_shift_crt_reentry_bound
    n 4 shift P (by norm_num) hinj hP
  have hprod_eq : (∏ i : Fin 4, P i) = p5 * p7 * p9 * p10 := by
    rw [Fin.prod_univ_four]
    rfl
  rw [hprod_eq] at hcore
  simpa using hcore hprod hcand

/-- For the four exact base shifts, every pair has at least one prime bounded
by the common CRT remainder.  Equivalently, at most one of the four primes can
lie strictly above that remainder. -/
theorem erdos647_base_four_prime_remainder_pair_bounds :
    ∀ n p5 p7 p9 p10 : ℕ,
      10 < n →
      p5.Prime → 10 < p5 → p5 ∣ n - 5 →
      p7.Prime → 10 < p7 → p7 ∣ n - 7 →
      p9.Prime → 10 < p9 → p9 ∣ n - 9 →
      p10.Prime → 10 < p10 → p10 ∣ n - 10 →
      let R := n % (p5 * p7 * p9 * p10)
      (p5 ≤ R ∨ p7 ≤ R) ∧ (p5 ≤ R ∨ p9 ≤ R) ∧
      (p5 ≤ R ∨ p10 ≤ R) ∧ (p7 ≤ R ∨ p9 ≤ R) ∧
      (p7 ≤ R ∨ p10 ≤ R) ∧ (p9 ≤ R ∨ p10 ≤ R) := by
  intro n p5 p7 p9 p10 hn
    hp5 hp5large hp5dvd hp7 hp7large hp7dvd
    hp9 hp9large hp9dvd hp10 hp10large hp10dvd
  let shift : Fin 4 → ℕ := ![5, 7, 9, 10]
  let P : Fin 4 → ℕ := ![p5, p7, p9, p10]
  have hP : ∀ i : Fin 4,
      (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
        shift i < n ∧ P i ∣ n - shift i := by
    intro i
    fin_cases i <;> simp [P, shift, hp5, hp5dvd,
      hp7, hp7dvd, hp9, hp9dvd, hp10, hp10dvd] <;> omega
  have hpair := erdos647_arbitrary_shift_remainder_dominates_pair
    n 4 shift P (by norm_num) hP
  have hprod : (∏ i : Fin 4, P i) = p5 * p7 * p9 * p10 := by
    rw [Fin.prod_univ_four]
    rfl
  dsimp
  rw [← hprod]
  exact ⟨
    hpair 0 1 (by native_decide),
    hpair 0 2 (by native_decide),
    hpair 0 3 (by native_decide),
    hpair 1 2 (by native_decide),
    hpair 1 3 (by native_decide),
    hpair 2 3 (by native_decide)⟩

/-- Six pairwise remainder bounds force some three of the four factors below
the cubic remainder scale. -/
theorem erdos647_four_pair_bounds_force_triple_product :
    ∀ R a b c d : ℕ,
      (a ≤ R ∨ b ≤ R) → (a ≤ R ∨ c ≤ R) →
      (a ≤ R ∨ d ≤ R) → (b ≤ R ∨ c ≤ R) →
      (b ≤ R ∨ d ≤ R) → (c ≤ R ∨ d ≤ R) →
      a * b * c ≤ R ^ 3 ∨ a * b * d ≤ R ^ 3 ∨
        a * c * d ≤ R ^ 3 ∨ b * c * d ≤ R ^ 3 := by
  intro R a b c d hab hac had hbc hbd hcd
  have triple_le : ∀ {x y z : ℕ}, x ≤ R → y ≤ R → z ≤ R →
      x * y * z ≤ R ^ 3 := by
    intro x y z hx hy hz
    calc
      x * y * z ≤ R * R * R := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
      _ = R ^ 3 := by ring
  by_cases ha : a ≤ R
  · by_cases hb : b ≤ R
    · by_cases hc : c ≤ R
      · exact Or.inl (triple_le ha hb hc)
      · have hd : d ≤ R := hcd.resolve_left hc
        exact Or.inr (Or.inl (triple_le ha hb hd))
    · have hc : c ≤ R := hbc.resolve_left hb
      have hd : d ≤ R := hbd.resolve_left hb
      exact Or.inr (Or.inr (Or.inl (triple_le ha hc hd)))
  · have hb : b ≤ R := hab.resolve_left ha
    have hc : c ≤ R := hac.resolve_left ha
    have hd : d ≤ R := had.resolve_left ha
    exact Or.inr (Or.inr (Or.inr (triple_le hb hc hd)))

/-- Base-rung corollary: at least one triple of selected primes is bounded by
the cube of their common CRT remainder. -/
theorem erdos647_base_four_prime_remainder_triple_bound :
    ∀ n p5 p7 p9 p10 : ℕ,
      10 < n →
      p5.Prime → 10 < p5 → p5 ∣ n - 5 →
      p7.Prime → 10 < p7 → p7 ∣ n - 7 →
      p9.Prime → 10 < p9 → p9 ∣ n - 9 →
      p10.Prime → 10 < p10 → p10 ∣ n - 10 →
      let R := n % (p5 * p7 * p9 * p10)
      p5 * p7 * p9 ≤ R ^ 3 ∨ p5 * p7 * p10 ≤ R ^ 3 ∨
        p5 * p9 * p10 ≤ R ^ 3 ∨ p7 * p9 * p10 ≤ R ^ 3 := by
  intro n p5 p7 p9 p10 hn
    hp5 hp5large hp5dvd hp7 hp7large hp7dvd
    hp9 hp9large hp9dvd hp10 hp10large hp10dvd
  obtain ⟨h57, h59, h510, h79, h710, h910⟩ :=
    erdos647_base_four_prime_remainder_pair_bounds
      n p5 p7 p9 p10 hn
      hp5 hp5large hp5dvd hp7 hp7large hp7dvd
      hp9 hp9large hp9dvd hp10 hp10large hp10dvd
  exact erdos647_four_pair_bounds_force_triple_product
    _ p5 p7 p9 p10 h57 h59 h510 h79 h710 h910

/-- Pure finite engine behind the remainder argument: if every distinct pair
has a coordinate bounded by `R`, then one exceptional coordinate can be
removed so that all remaining values are bounded by `R`. -/
theorem erdos647_pair_dominance_exists_exceptional_index :
    ∀ (r R : ℕ) (P : Fin r → ℕ),
      0 < r →
      (∀ i j : Fin r, i ≠ j → P i ≤ R ∨ P j ≤ R) →
      ∃ e : Fin r, ∀ i : Fin r, i ≠ e → P i ≤ R := by
  intro r R P hr hpair
  by_cases hlarge : ∃ e : Fin r, R < P e
  · obtain ⟨e, he⟩ := hlarge
    refine ⟨e, ?_⟩
    intro i hie
    rcases hpair i e hie with hi | he'
    · exact hi
    · omega
  · let e : Fin r := ⟨0, hr⟩
    refine ⟨e, ?_⟩
    intro i _
    exact le_of_not_gt (fun hi => hlarge ⟨i, hi⟩)

/-- In an arbitrary injective shift family, two selected primes cannot both
exceed the common CRT remainder. -/
theorem erdos647_arbitrary_shift_unique_prime_above_remainder :
    ∀ (n r : ℕ) (shift P : Fin r → ℕ),
      0 < r →
      Function.Injective shift →
      (∀ i : Fin r,
        (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
          shift i < n ∧ P i ∣ n - shift i) →
      let R := n % (∏ k : Fin r, P k)
      ∀ i j : Fin r, R < P i → R < P j → i = j := by
  intro n r shift P hr hshift hP
  dsimp
  intro i j hi hj
  by_contra hij
  have hshift_ne : shift i ≠ shift j := by
    intro h
    exact hij (hshift h)
  have hpair := erdos647_arbitrary_shift_remainder_dominates_pair
    n r shift P hr hP i j hshift_ne
  omega

/-- Cardinal form of the arbitrary-shift exceptional-prime theorem: the set
of coordinates whose selected prime exceeds the CRT remainder has size at
most one. -/
theorem erdos647_arbitrary_shift_large_prime_card_le_one :
    ∀ (n r : ℕ) (shift P : Fin r → ℕ),
      0 < r →
      Function.Injective shift →
      (∀ i : Fin r,
        (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
          shift i < n ∧ P i ∣ n - shift i) →
      let R := n % (∏ k : Fin r, P k)
      (Finset.univ.filter (fun i : Fin r => R < P i)).card ≤ 1 := by
  intro n r shift P hr hshift hP
  let R := n % (∏ k : Fin r, P k)
  have hunique := erdos647_arbitrary_shift_unique_prime_above_remainder
    n r shift P hr hshift hP
  dsimp at hunique ⊢
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hunique i j hi hj

/-- Exceptional-index form: one coordinate can be named so that every other
selected prime is bounded by the common CRT remainder. -/
theorem erdos647_arbitrary_shift_exists_exceptional_index :
    ∀ (n r : ℕ) (shift P : Fin r → ℕ),
      0 < r →
      Function.Injective shift →
      (∀ i : Fin r,
        (P i).Prime ∧ 0 < shift i ∧ shift i < P i ∧
          shift i < n ∧ P i ∣ n - shift i) →
      let R := n % (∏ k : Fin r, P k)
      ∃ e : Fin r, ∀ i : Fin r, i ≠ e → P i ≤ R := by
  intro n r shift P hr hshift hP
  dsimp
  apply erdos647_pair_dominance_exists_exceptional_index r _ P hr
  intro i j hij
  have hshift_ne : shift i ≠ shift j := by
    intro h
    exact hij (hshift h)
  exact erdos647_arbitrary_shift_remainder_dominates_pair
    n r shift P hr hP i j hshift_ne

end Erdos647
