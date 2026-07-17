import Mathlib

/-!
# Erdős #647 — maximal CRT re-entry subsets

A maximal selected-prime subproduct below `n` simultaneously supplies a
valid CRT re-entry modulus and bounds every omitted complementary cofactor.
This is the finite induction interface connecting the first-layer prime family
to the second-layer catalog.
-/

open scoped ArithmeticFunction

namespace Erdos647

/-- Every positive finite family admits a cardinality-maximal subset whose
product is below `n`.  Adding any omitted coordinate then reaches `n`. -/
theorem erdos647_exists_maximal_subproduct_lt :
    forall (n W : Nat) (P : Fin W -> Nat),
      1 < n ->
      (forall i : Fin W, 0 < P i) ->
      exists I : Finset (Fin W),
        I ⊆ Finset.univ /\
        (∏ i ∈ I, P i) < n /\
        (forall j : Fin W, j ∉ I ->
          n <= (∏ i ∈ I, P i) * P j) := by
  classical
  intro n W P hn hP
  let good : Finset (Finset (Fin W)) :=
    Finset.univ.powerset.filter
      (fun I => (∏ i ∈ I, P i) < n)
  have hempty : (∅ : Finset (Fin W)) ∈ good := by
    simp [good, hn]
  have hgood : good.Nonempty := ⟨∅, hempty⟩
  let cards : Finset Nat := good.image Finset.card
  have hcards : cards.Nonempty := hgood.image Finset.card
  let t : Nat := cards.max' hcards
  have htmem : t ∈ cards := by
    dsimp [t]
    exact Finset.max'_mem _ _
  obtain ⟨I, hIgood, hIcard⟩ := by
    simpa [cards] using htmem
  have hIparts : I ⊆ Finset.univ /\ (∏ i ∈ I, P i) < n := by
    have hmem := Finset.mem_filter.mp hIgood
    exact ⟨Finset.mem_powerset.mp hmem.1, hmem.2⟩
  refine ⟨I, hIparts.1, hIparts.2, ?_⟩
  intro j hj
  by_contra hprod
  have hjuniv : j ∈ (Finset.univ : Finset (Fin W)) := Finset.mem_univ j
  have hinsert_sub : insert j I ⊆ (Finset.univ : Finset (Fin W)) := by
    exact Finset.insert_subset hjuniv hIparts.1
  have hinsert_prod :
      (∏ i ∈ insert j I, P i) < n := by
    rw [Finset.prod_insert hj]
    simpa [Nat.mul_comm] using (Nat.lt_of_not_ge hprod)
  have hinsert_good : insert j I ∈ good := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hinsert_sub, hinsert_prod⟩
  have hinsert_card_mem : (insert j I).card ∈ cards := by
    exact Finset.mem_image.mpr ⟨insert j I, hinsert_good, rfl⟩
  have hle : (insert j I).card <= t := by
    dsimp [t]
    exact Finset.le_max' cards _ hinsert_card_mem
  rw [Finset.card_insert_of_notMem hj, hIcard] at hle
  omega

/-- For shifted factorizations `n - shift j = P j * q j`, every coordinate
omitted from a cardinality-maximal re-entry subset has cofactor strictly below
the selected subproduct. -/
theorem erdos647_maximal_subproduct_bounds_omitted_cofactors :
    forall (n W : Nat) (shift P q : Fin W -> Nat),
      1 < n ->
      0 < W ->
      (forall i : Fin W, 0 < P i) ->
      (forall i : Fin W,
        0 < shift i /\ shift i < n /\
          n - shift i = P i * q i) ->
      exists I : Finset (Fin W),
        I.Nonempty /\
        I ⊆ Finset.univ /\
        (∏ i ∈ I, P i) < n /\
        (forall j : Fin W, j ∉ I ->
          q j < (∏ i ∈ I, P i)) := by
  intro n W shift P q hn hW hP hfactor
  obtain ⟨I, hIsub, hQn, hmax⟩ :=
    erdos647_exists_maximal_subproduct_lt n W P hn hP
  have hIne : I.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    let j : Fin W := ⟨0, hW⟩
    have hmaxj := hmax j (by simp [hne])
    have hPdvd : P j ∣ n - shift j := by
      rw [(hfactor j).2.2]
      exact dvd_mul_right _ _
    have hPbound : P j < n := by
      have hhostpos : 0 < n - shift j :=
        Nat.sub_pos_of_lt (hfactor j).2.1
      exact (Nat.le_of_dvd hhostpos hPdvd).trans_lt
        (Nat.sub_lt (by omega) (hfactor j).1)
    simp [hne] at hmaxj
    omega
  refine ⟨I, hIne, hIsub, hQn, ?_⟩
  intro j hj
  have hshiftlt : n - shift j < n :=
    Nat.sub_lt (by omega) (hfactor j).1
  have hmul :
      P j * q j < P j * (∏ i ∈ I, P i) := by
    calc
      P j * q j = n - shift j := (hfactor j).2.2.symm
      _ < n := hshiftlt
      _ <= (∏ i ∈ I, P i) * P j := hmax j hj
      _ = P j * (∏ i ∈ I, P i) := by ring
  exact (Nat.mul_lt_mul_left (hP j)).mp hmul

/-- Any nonempty injective prime subset whose product lies below `n` re-enters
the exact candidate budget through the remainder modulo that subproduct. -/
theorem erdos647_prime_subset_reentry_bound :
    forall (n W : Nat) (I : Finset (Fin W)) (P : Fin W -> Nat),
      I.Nonempty ->
      Function.Injective P ->
      (forall i, i ∈ I -> (P i).Prime) ->
      0 < n % (∏ i ∈ I, P i) ->
      (∏ i ∈ I, P i) < n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      2 ^ I.card <= n % (∏ i ∈ I, P i) + 2 := by
  classical
  intro n W I P hI hinj hprime hRpos hQn hcand
  let Q : Nat := ∏ i ∈ I, P i
  let R : Nat := n % Q
  have hRpos' : 0 < R := by simpa [R, Q] using hRpos
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun i hi => (hprime i hi).pos)
  have hRltQ : R < Q := by
    dsimp [R]
    exact Nat.mod_lt n hQpos
  have hRltN : R < n := lt_trans hRltQ hQn
  have hQhost : Q ∣ n - R := by
    refine ⟨n / Q, ?_⟩
    have hdecomp := Nat.mod_add_div n Q
    dsimp [R]
    omega
  have hhostpos : 0 < n - R := Nat.sub_pos_of_lt hRltN
  let S : Finset Nat := I.image P
  have hScard : S.card = I.card := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hinj.injOn]
  have hPiQ : forall i, i ∈ I -> P i ∣ Q := by
    intro i hi
    dsimp [Q]
    exact Finset.dvd_prod_of_mem P hi
  have hS : forall p, p ∈ S -> p.Prime /\ p ∣ n - R := by
    intro p hp
    dsimp [S] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact ⟨hprime i hi, (hPiQ i hi).trans hQhost⟩
  have htau : 2 ^ I.card <= ArithmeticFunction.sigma 0 (n - R) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hhostpos.ne']
    have hsubset : S ⊆ (n - R).primeFactors := by
      intro p hp
      exact Nat.mem_primeFactors.mpr
        ⟨(hS p hp).1, (hS p hp).2, hhostpos.ne'⟩
    have hcard : S.card <= (n - R).primeFactors.card :=
      Finset.card_le_card hsubset
    have hpow : 2 ^ (n - R).primeFactors.card <=
        ∏ p ∈ (n - R).primeFactors,
          ((n - R).factorization p + 1) := by
      apply Finset.pow_card_le_prod
      intro p hp
      have hp' : p ∈ (n - R).factorization.support := by simpa using hp
      have hfac : (n - R).factorization p ≠ 0 :=
        Finsupp.mem_support_iff.mp hp'
      omega
    rw [← hScard]
    exact (pow_le_pow_right' (by norm_num) hcard).trans hpow
  let f : Fin n -> Nat := fun x =>
    (x : Nat) + ArithmeticFunction.sigma 0 x
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨2 * n, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [f]
    rw [ArithmeticFunction.sigma_zero_apply]
    have hc := Nat.card_divisors_le_self (x : Nat)
    have hx : (x : Nat) < n := x.isLt
    omega
  let m : Fin n :=
    ⟨n - R, Nat.sub_lt (lt_trans hQpos hQn) hRpos'⟩
  have hm : f m <= n + 2 := le_trans (le_ciSup hbdd m) hcand
  dsimp [f, m] at hm
  have hbudget : ArithmeticFunction.sigma 0 (n - R) <= R + 2 := by
    omega
  simpa [R, Q] using htau.trans hbudget

/-- Candidate-facing maximal-subset feedback theorem.  A maximal proper prime
subproduct re-enters the divisor budget, while every omitted first-layer
cofactor is strictly smaller than that same modulus. -/
theorem erdos647_candidate_maximal_reentry_subset :
    forall (n W : Nat) (shift P q : Fin W -> Nat),
      1 < n ->
      0 < W ->
      Function.Injective P ->
      (forall i : Fin W,
        (P i).Prime /\
        0 < shift i /\ shift i < P i /\ shift i < n /\
        n - shift i = P i * q i) ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      exists I : Finset (Fin W),
        I.Nonempty /\
        I ⊆ Finset.univ /\
        (∏ i ∈ I, P i) < n /\
        (forall j : Fin W, j ∉ I ->
          q j < (∏ i ∈ I, P i)) /\
        0 < n % (∏ i ∈ I, P i) /\
        2 ^ I.card <= n % (∏ i ∈ I, P i) + 2 := by
  classical
  intro n W shift P q hn hW hinj hdata hcand
  have hPpos : forall i : Fin W, 0 < P i :=
    fun i => (hdata i).1.pos
  obtain ⟨I, hIne, hIsub, hQn, hqbound⟩ :=
    erdos647_maximal_subproduct_bounds_omitted_cofactors
      n W shift P q hn hW hPpos
        (fun i => ⟨(hdata i).2.1, (hdata i).2.2.2.1,
          (hdata i).2.2.2.2⟩)
  have hRpos : 0 < n % (∏ i ∈ I, P i) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hQdvd : (∏ i ∈ I, P i) ∣ n :=
      Nat.dvd_iff_mod_eq_zero.mpr hz
    obtain ⟨i, hi⟩ := hIne
    have hPiQ : P i ∣ (∏ j ∈ I, P j) :=
      Finset.dvd_prod_of_mem P hi
    have hPin : P i ∣ n := hPiQ.trans hQdvd
    have hPidiff : P i ∣ n - shift i := by
      rw [(hdata i).2.2.2.2]
      exact dvd_mul_right _ _
    have hPshift : P i ∣ shift i := by
      have h := Nat.dvd_sub hPin hPidiff
      have heq : n - (n - shift i) = shift i := by
        exact Nat.sub_sub_self (hdata i).2.2.2.1.le
      rwa [heq] at h
    have hPle : P i <= shift i :=
      Nat.le_of_dvd (hdata i).2.1 hPshift
    exact (not_lt_of_ge hPle) (hdata i).2.2.1
  have hreentry :=
    erdos647_prime_subset_reentry_bound n W I P hIne hinj
      (fun i _ => (hdata i).1) hRpos hQn hcand
  exact ⟨I, hIne, hIsub, hQn, hqbound, hRpos, hreentry⟩

/-- Cardinal bookkeeping for the maximal feedback subset: selected and
omitted coordinates partition the whole width. -/
theorem erdos647_candidate_maximal_reentry_card_split :
    forall (n W : Nat) (shift P q : Fin W -> Nat),
      1 < n ->
      0 < W ->
      Function.Injective P ->
      (forall i : Fin W,
        (P i).Prime /\
        0 < shift i /\ shift i < P i /\ shift i < n /\
        n - shift i = P i * q i) ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      exists I : Finset (Fin W),
        I.Nonempty /\
        I ⊆ Finset.univ /\
        (∏ i ∈ I, P i) < n /\
        (forall j : Fin W, j ∉ I ->
          q j < (∏ i ∈ I, P i)) /\
        0 < n % (∏ i ∈ I, P i) /\
        2 ^ I.card <= n % (∏ i ∈ I, P i) + 2 /\
        I.card + (Finset.univ \ I).card = W := by
  intro n W shift P q hn hW hinj hdata hcand
  obtain ⟨I, hIne, hIsub, hQn, hq, hR, hreentry⟩ :=
    erdos647_candidate_maximal_reentry_subset
      n W shift P q hn hW hinj hdata hcand
  have hpartition :
      (Finset.univ \ I).card + I.card = W := by
    simpa using Finset.card_sdiff_add_card_eq_card hIsub
  exact ⟨I, hIne, hIsub, hQn, hq, hR, hreentry, by omega⟩

/-- Threshold form of the induction interface.  Either the maximal re-entry
subset has at least `T` coordinates and pays a `2^T` budget, or its omitted
cofactor block has the complementary quantitative size. -/
theorem erdos647_candidate_maximal_reentry_threshold :
    forall (n W T : Nat) (shift P q : Fin W -> Nat),
      1 < n ->
      0 < W ->
      0 < T ->
      Function.Injective P ->
      (forall i : Fin W,
        (P i).Prime /\
        0 < shift i /\ shift i < P i /\ shift i < n /\
        n - shift i = P i * q i) ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      exists I : Finset (Fin W),
        I.Nonempty /\
        I ⊆ Finset.univ /\
        (∏ i ∈ I, P i) < n /\
        (forall j : Fin W, j ∉ I ->
          q j < (∏ i ∈ I, P i)) /\
        0 < n % (∏ i ∈ I, P i) /\
        ((T <= I.card /\
            2 ^ T <= n % (∏ i ∈ I, P i) + 2) \/
          (I.card < T /\
            W <= (Finset.univ \ I).card + (T - 1))) := by
  intro n W T shift P q hn hW hT hinj hdata hcand
  obtain ⟨I, hIne, hIsub, hQn, hq, hR, hreentry, hcard⟩ :=
    erdos647_candidate_maximal_reentry_card_split
      n W shift P q hn hW hinj hdata hcand
  refine ⟨I, hIne, hIsub, hQn, hq, hR, ?_⟩
  by_cases hlarge : T <= I.card
  · left
    refine ⟨hlarge, ?_⟩
    exact (pow_le_pow_right' (by norm_num) hlarge).trans hreentry
  · right
    constructor
    · omega
    · omega

/-- Balanced specialization: either roughly half the selected primes re-enter
at exponential strength, or more than half the coordinates survive as
uniformly bounded second-layer cofactors. -/
theorem erdos647_candidate_balanced_reentry_or_cofactor_block :
    forall (n W : Nat) (shift P q : Fin W -> Nat),
      1 < n ->
      0 < W ->
      Function.Injective P ->
      (forall i : Fin W,
        (P i).Prime /\
        0 < shift i /\ shift i < P i /\ shift i < n /\
        n - shift i = P i * q i) ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      exists I : Finset (Fin W),
        I.Nonempty /\
        I ⊆ Finset.univ /\
        (∏ i ∈ I, P i) < n /\
        (forall j : Fin W, j ∉ I ->
          q j < (∏ i ∈ I, P i)) /\
        0 < n % (∏ i ∈ I, P i) /\
        (2 ^ ((W + 1) / 2) <=
            n % (∏ i ∈ I, P i) + 2 \/
          W / 2 + 1 <= (Finset.univ \ I).card) := by
  intro n W shift P q hn hW hinj hdata hcand
  have hT : 0 < (W + 1) / 2 := by omega
  obtain ⟨I, hIne, hIsub, hQn, hq, hR, halt⟩ :=
    erdos647_candidate_maximal_reentry_threshold
      n W ((W + 1) / 2) shift P q
        hn hW hT hinj hdata hcand
  refine ⟨I, hIne, hIsub, hQn, hq, hR, ?_⟩
  rcases halt with hmany | hcof
  · exact Or.inl hmany.2
  · right
    omega

end Erdos647
