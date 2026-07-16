import Mathlib

/-!
# Erdős #647 — CRT re-entry exclusion

This file turns a block of distinct large prime divisors, one supplied by each
shift, into a single new failed-shift certificate.  If the primes are
`P i ∣ n - (1 + i)` and `Q = ∏ i ∈ I, P i`, then the remainder
`r = n % Q` gives a re-entry shift: every `P i` divides `n - r`.

The exact Formal Conjectures candidate condition bounds
`σ₀ (n - r) ≤ r + 2`, while the distinct prime divisors force
`2 ^ I.card ≤ σ₀ (n - r)`.  Consequently a strict reverse inequality
`r + 2 < 2 ^ I.card` is a kernel-checkable exclusion certificate.

This is a structural reduction, not a resolution of Erdős #647: it identifies
a reusable way for information from many shifts to re-enter the original
candidate condition at one additional shift.

Tracked proof-search verification (2026-07-16, all `kernel_verified` with
`termination_reason = root_proved`):

* `erdos647_distinct_prime_divisors_force_tau`:
  problem `28a705ef-b9f9-4d94-b64c-2326353a9ca3`,
  episode `dbaf459e-7de3-4049-878b-0b6b0c4bf201`;
* `erdos647_crt_reentry_arithmetic`:
  problem `34756065-a1fc-4104-9c13-b51103dd4a4a`,
  episode `26aec94e-2c97-4018-a881-a55ea4e73b33`;
* `erdos647_formal_candidate_crt_reentry_sandwich`:
  problem `e3696cfd-9dee-4b0f-97b2-6009159306c4`,
  episode `63caad59-40e2-494c-9820-8bd4cd140c1c`.

The numerical, uniform-bound, and contrapositive corollaries below were
source-compiled against the pinned project from these verified roots.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- A finite set of distinct prime divisors of `H` supplies at least one
divisor for every subset, hence forces the standard `2 ^ card` lower bound on
the divisor-counting function. -/
theorem erdos647_distinct_prime_divisors_force_tau :
    ∀ (H : ℕ) (S : Finset ℕ), H ≠ 0 →
      (∀ p ∈ S, p.Prime ∧ p ∣ H) →
      2 ^ S.card ≤ ArithmeticFunction.sigma 0 H := by
  intro H S hH hS
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hH]
  have hsubset : S ⊆ H.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨(hS p hp).1, (hS p hp).2, hH⟩
  have hcard : S.card ≤ H.primeFactors.card :=
    Finset.card_le_card hsubset
  have hpow : 2 ^ H.primeFactors.card ≤
      ∏ p ∈ H.primeFactors, (H.factorization p + 1) := by
    apply Finset.pow_card_le_prod
    intro p hp
    have hp' : p ∈ H.factorization.support := by
      simpa using hp
    have hfac : H.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    omega
  exact (pow_le_pow_right' (by norm_num) hcard).trans hpow

/-- Arithmetic facts carried by the CRT re-entry remainder.  Besides
squarefreeness and coprimality of the prime product, the remainder remembers
every original shift exactly modulo its associated prime.  Two distinct
shift residues cannot both occur below or at `W`, so a block containing at
least two shifts automatically has `W < n % Q`. -/
theorem erdos647_crt_reentry_arithmetic :
    ∀ (n W : ℕ) (I : Finset (Fin W)) (P : Fin W → ℕ),
      1 ≤ W →
      I.Nonempty →
      Function.Injective P →
      (∀ i ∈ I,
        (P i).Prime ∧ W < P i ∧ P i ∣ n - (1 + (i : ℕ))) →
      (∏ i ∈ I, P i) < n →
      Squarefree (∏ i ∈ I, P i) ∧
        Nat.Coprime (∏ i ∈ I, P i) n ∧
        ¬(∏ i ∈ I, P i) ∣ n ∧
        (∀ i ∈ I,
          (n % (∏ j ∈ I, P j)) % P i = 1 + (i : ℕ)) ∧
        (2 ≤ I.card → W < n % (∏ i ∈ I, P i)) := by
  classical
  intro n W I P hW hI hinj hP hQn
  let Q : ℕ := ∏ i ∈ I, P i
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos fun i hi => (hP i hi).1.pos
  have hPiQ : ∀ i ∈ I, P i ∣ Q := by
    intro i hi
    dsimp [Q]
    exact Finset.dvd_prod_of_mem P hi
  have hPinot : ∀ i ∈ I, ¬P i ∣ n := by
    intro i hi hPin
    have hPiltQ : P i ≤ Q := Nat.le_of_dvd hQpos (hPiQ i hi)
    have hPiltN : P i < n := lt_of_le_of_lt hPiltQ hQn
    have hiW : (i : ℕ) < W := i.isLt
    have hWP : W < P i := (hP i hi).2.1
    have hshiftltP : 1 + (i : ℕ) < P i := by omega
    have hshiftltN : 1 + (i : ℕ) < n :=
      lt_trans hshiftltP hPiltN
    have hdifference : P i ∣ n - (n - (1 + (i : ℕ))) :=
      Nat.dvd_sub hPin (hP i hi).2.2
    have hshiftDvd : P i ∣ 1 + (i : ℕ) := by
      convert hdifference using 1
      all_goals omega
    have hPileShift : P i ≤ 1 + (i : ℕ) :=
      Nat.le_of_dvd (by omega) hshiftDvd
    omega
  have hsquarefree : Squarefree Q := by
    dsimp [Q]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply ((hP i hi).1.coprime_iff_not_dvd).mpr
      intro hdvd
      have hPeq : P i = P j :=
        (Nat.prime_dvd_prime_iff_eq (hP i hi).1 (hP j hj).1).mp hdvd
      exact hij (hinj hPeq)
    · intro i hi
      exact (hP i hi).1.squarefree
  have hcoprime : Nat.Coprime Q n := by
    dsimp [Q]
    rw [Nat.coprime_prod_left_iff]
    intro i hi
    exact ((hP i hi).1.coprime_iff_not_dvd).mpr (hPinot i hi)
  have hQnotdvd : ¬Q ∣ n := by
    intro hQdvd
    obtain ⟨i, hi⟩ := hI
    exact hPinot i hi ((hPiQ i hi).trans hQdvd)
  have hresidue : ∀ i ∈ I, (n % Q) % P i = 1 + (i : ℕ) := by
    intro i hi
    have hiW : (i : ℕ) < W := i.isLt
    have hWP : W < P i := (hP i hi).2.1
    have hshiftltP : 1 + (i : ℕ) < P i := by omega
    have hPiltQ : P i ≤ Q := Nat.le_of_dvd hQpos (hPiQ i hi)
    have hPiltN : P i < n := lt_of_le_of_lt hPiltQ hQn
    have hshiftltN : 1 + (i : ℕ) < n :=
      lt_trans hshiftltP hPiltN
    have hsplit : n = 1 + (i : ℕ) + (n - (1 + (i : ℕ))) := by
      omega
    have hmodzero : (n - (1 + (i : ℕ))) % P i = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (hP i hi).2.2
    calc
      (n % Q) % P i = n % P i := Nat.mod_mod_of_dvd n (hPiQ i hi)
      _ = (1 + (i : ℕ) + (n - (1 + (i : ℕ)))) % P i := by rw [← hsplit]
      _ = 1 + (i : ℕ) := by
        simpa [Nat.add_mod, hmodzero] using
          (Nat.mod_eq_of_lt hshiftltP)
  have hremainder_large : 2 ≤ I.card → W < n % Q := by
    intro hcard
    have hone : 1 < I.card := by omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hone
    by_contra hnot
    have hrleW : n % Q ≤ W := by omega
    have hri : n % Q = 1 + (i : ℕ) := by
      have hlt : n % Q < P i := lt_of_le_of_lt hrleW (hP i hi).2.1
      simpa [Nat.mod_eq_of_lt hlt] using hresidue i hi
    have hrj : n % Q = 1 + (j : ℕ) := by
      have hlt : n % Q < P j := lt_of_le_of_lt hrleW (hP j hj).2.1
      simpa [Nat.mod_eq_of_lt hlt] using hresidue j hj
    apply hij
    apply Fin.ext
    omega
  simpa [Q] using
    And.intro hsquarefree
      (And.intro hcoprime
        (And.intro hQnotdvd (And.intro hresidue hremainder_large)))

/-- CRT re-entry bound in the exact candidate language used by Formal
Conjectures #647.

For a nonempty set `I` of shifts, assume that the `i`-th shift produces a
prime `P i > W`, that these primes are distinct, and put
`Q = ∏ i ∈ I, P i`.  If `Q < n`, then the candidate condition forces
`2 ^ I.card ≤ n % Q + 2`.
-/
theorem erdos647_formal_candidate_crt_reentry_sandwich :
    ∀ (n W : ℕ) (I : Finset (Fin W)) (P : Fin W → ℕ),
      1 ≤ W →
      I.Nonempty →
      Function.Injective P →
      (∀ i ∈ I,
        (P i).Prime ∧ W < P i ∧ P i ∣ n - (1 + (i : ℕ))) →
      (∏ i ∈ I, P i) < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      2 ^ I.card ≤
          ArithmeticFunction.sigma 0
            (n - n % (∏ i ∈ I, P i)) ∧
        ArithmeticFunction.sigma 0
            (n - n % (∏ i ∈ I, P i)) ≤
          n % (∏ i ∈ I, P i) + 2 := by
  classical
  intro n W I P hW hI hinj hP hQn hcand
  set Q : ℕ := ∏ i ∈ I, P i with hQ
  have hQpos : 0 < Q := by
    rw [hQ]
    exact Finset.prod_pos fun i hi => (hP i hi).1.pos
  have hQnotdvd : ¬ Q ∣ n := by
    intro hQdvd
    obtain ⟨i, hi⟩ := hI
    have hPiQ : P i ∣ Q := by
      rw [hQ]
      exact Finset.dvd_prod_of_mem P hi
    have hPin : P i ∣ n := hPiQ.trans hQdvd
    have hPiltQ : P i ≤ Q := Nat.le_of_dvd hQpos hPiQ
    have hPiltN : P i < n := lt_of_le_of_lt hPiltQ hQn
    have hiW : (i : ℕ) < W := i.isLt
    have hWP : W < P i := (hP i hi).2.1
    have hshiftltP : 1 + (i : ℕ) < P i := by omega
    have hshiftltN : 1 + (i : ℕ) < n :=
      lt_trans hshiftltP hPiltN
    have hdifference : P i ∣ n - (n - (1 + (i : ℕ))) :=
      Nat.dvd_sub hPin (hP i hi).2.2
    have hshiftDvd : P i ∣ 1 + (i : ℕ) := by
      convert hdifference using 1
      all_goals omega
    have hPileShift : P i ≤ 1 + (i : ℕ) :=
      Nat.le_of_dvd (by omega) hshiftDvd
    omega
  have hrne : n % Q ≠ 0 := by
    intro hr
    exact hQnotdvd (Nat.dvd_iff_mod_eq_zero.mpr hr)
  have hrpos : 0 < n % Q := Nat.pos_of_ne_zero hrne
  have hrltQ : n % Q < Q := Nat.mod_lt n hQpos
  have hrltN : n % Q < n := lt_trans hrltQ hQn
  have hQhost : Q ∣ n - n % Q := by
    refine ⟨n / Q, ?_⟩
    have hdecomp := Nat.mod_add_div n Q
    omega
  have hhostpos : 0 < n - n % Q := by omega
  let S : Finset ℕ := I.image P
  have hScard : S.card = I.card := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hinj.injOn]
  have hS : ∀ p ∈ S, p.Prime ∧ p ∣ n - n % Q := by
    intro p hp
    dsimp [S] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    refine ⟨(hP i hi).1, ?_⟩
    have hPiQ : P i ∣ Q := by
      rw [hQ]
      exact Finset.dvd_prod_of_mem P hi
    exact hPiQ.trans hQhost
  have htau : 2 ^ I.card ≤
      ArithmeticFunction.sigma 0 (n - n % Q) := by
    have h := erdos647_distinct_prime_divisors_force_tau
      (n - n % Q) S (ne_of_gt hhostpos) hS
    rwa [hScard] at h
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
  exact ⟨htau, hbudget⟩

/-- Uniform upper bounds on the selected large primes are enough to discharge
the product-size hypothesis in the CRT re-entry sandwich.  This isolates the
remaining quantitative seam: find enough selected shift factors whose common
upper bound `B` satisfies `B ^ I.card < n`. -/
theorem erdos647_formal_candidate_crt_reentry_sandwich_of_uniform_bound :
    ∀ (n W B : ℕ) (I : Finset (Fin W)) (P : Fin W → ℕ),
      1 ≤ W →
      I.Nonempty →
      Function.Injective P →
      (∀ i ∈ I,
        (P i).Prime ∧ W < P i ∧ P i ∣ n - (1 + (i : ℕ))) →
      (∀ i ∈ I, P i ≤ B) →
      B ^ I.card < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      2 ^ I.card ≤
          ArithmeticFunction.sigma 0
            (n - n % (∏ i ∈ I, P i)) ∧
        ArithmeticFunction.sigma 0
            (n - n % (∏ i ∈ I, P i)) ≤
          n % (∏ i ∈ I, P i) + 2 := by
  intro n W B I P hW hI hinj hP hPB hBn hcand
  have hQle : (∏ i ∈ I, P i) ≤ B ^ I.card := by
    calc
      (∏ i ∈ I, P i) ≤ ∏ i ∈ I, B := by
        apply Finset.prod_le_prod'
        intro i hi
        exact hPB i hi
      _ = B ^ I.card := by simp
  have hQn : (∏ i ∈ I, P i) < n := lt_of_le_of_lt hQle hBn
  exact erdos647_formal_candidate_crt_reentry_sandwich
    n W I P hW hI hinj hP hQn hcand

/-- Numerical consequence of the exact CRT re-entry sandwich. -/
theorem erdos647_formal_candidate_crt_reentry_bound :
    ∀ (n W : ℕ) (I : Finset (Fin W)) (P : Fin W → ℕ),
      1 ≤ W →
      I.Nonempty →
      Function.Injective P →
      (∀ i ∈ I,
        (P i).Prime ∧ W < P i ∧ P i ∣ n - (1 + (i : ℕ))) →
      (∏ i ∈ I, P i) < n →
      (⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 →
      2 ^ I.card ≤ n % (∏ i ∈ I, P i) + 2 := by
  intro n W I P hW hI hinj hP hQn hcand
  obtain ⟨hlower, hupper⟩ :=
    erdos647_formal_candidate_crt_reentry_sandwich
      n W I P hW hI hinj hP hQn hcand
  exact hlower.trans hupper

/-- Contrapositive form: a CRT remainder too small to pay for all the distinct
prime divisors is an explicit certificate that `n` is not a candidate for
Formal Conjectures #647. -/
theorem erdos647_not_formal_candidate_of_crt_reentry :
    ∀ (n W : ℕ) (I : Finset (Fin W)) (P : Fin W → ℕ),
      1 ≤ W →
      I.Nonempty →
      Function.Injective P →
      (∀ i ∈ I,
        (P i).Prime ∧ W < P i ∧ P i ∣ n - (1 + (i : ℕ))) →
      (∏ i ∈ I, P i) < n →
      n % (∏ i ∈ I, P i) + 2 < 2 ^ I.card →
      ¬(⨆ m : Fin n,
        (m : ℕ) + ArithmeticFunction.sigma 0 m) ≤ n + 2 := by
  intro n W I P hW hI hinj hP hQn hsmall hcand
  have hbound := erdos647_formal_candidate_crt_reentry_bound
    n W I P hW hI hinj hP hQn hcand
  omega

end Erdos647
