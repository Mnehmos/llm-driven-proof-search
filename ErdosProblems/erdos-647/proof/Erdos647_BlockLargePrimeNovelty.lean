import Mathlib

/-!
# Erdos #647 - a block of budgets produces distinct large prime factors

This module assembles the smooth-number large-factor alternative with the
shift-difference non-reuse mechanism.  If the `W` consecutive positive shifts

`K, K + 1, ..., K + W - 1`

all satisfy their Erdos #647 divisor budgets, and every shifted value is
larger than the corresponding `W`-smooth power threshold, then one can choose
a prime divisor larger than `W` from each shifted value.  The choices are
automatically distinct: a common divisor of two shifted values divides the
difference of their shift coordinates, which is strictly smaller than `W`.

The theorem is deliberately generic and Mathlib-only.  It is an accumulation
interface, not by itself a contradiction or a closure of a Formal Conjectures
declaration.

Four roots were independently verified through the tracked
proof-search pipeline on 2026-07-16:

* generic block production:
  * preverification `ff7d027d-4b1e-4bd7-8d1f-6147120f19c3`
  * problem `dc7583e6-1191-4efe-b5bf-b750143ffc2f`
  * episode `89548463-5d2f-4d59-b2b9-61da4cc90823`
  * root hash `4aa50a77ae7ae2d6a5fc8bb16b2eb5928cb09301185145a36ef5b8381734f0d4`
* exact candidate-prefix production:
  * preverification `ead8fdb0-3824-488f-b583-bfc0afc9f26f`
  * problem `bd1e6750-61a1-4e03-8dbb-8265a2f5d7ba`
  * episode `cd4d5dd1-defd-4e21-bf64-651832299806`
  * root hash `17478478d42c32978b0fddf2709732754868f7c6aa172ba6ffccdba430a3277a`
* scalar endpoint production:
  * preverification `77c57c03-b15c-408f-8687-d78f38edc50c`
  * problem `c1a506f8-1e07-4518-b004-543a126a334e`
  * episode `8fd6a3b7-39fd-40ee-b4b9-81141eec9f58`
  * root hash `92616fb36ecae4e56d9bbe4cb535b454e97c0b1f387b65e011058d6e1bf9a60e`
* shared-host product bound:
  * preverification `6312694c-73e8-4fbd-b382-d91ed4c24b8e`
  * problem `b31522a1-256b-4f90-8085-37bb393b0a1b`
  * episode `522f2296-f902-44bf-826f-277cf7c366d8`
  * root hash `4d129e29cd375a4d3a9647788207d58abecac39007863d7364f0d97f67538240`

All four tracked outcomes are `kernel_verified`.
-/

/-- Consecutive divisor budgets plus the smoothness-escape inequalities
produce an injective family of prime factors, one for each coordinate. -/
theorem erdos647_block_budgets_produce_distinct_large_primes :
    forall (n K W : Nat),
      1 <= W ->
      0 < K ->
      K + W <= n ->
      (forall i : Fin W,
        ArithmeticFunction.sigma 0 (n - (K + (i : Nat))) <=
          K + (i : Nat) + 2) ->
      (forall i : Fin W,
        W ^ (K + (i : Nat) + 1) < n - (K + (i : Nat))) ->
      exists P : Fin W -> Nat,
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (K + (i : Nat))) /\
        Function.Injective P := by
  classical
  intro n K W hW hK hKW hbudget hlarge
  have hone_add_sum_le_prod_succ : forall (s : Finset Nat) (a : Nat -> Nat),
      1 + s.sum a <= s.prod (fun x => a x + 1) := by
    intro s a
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.prod_insert hx]
        have hprod : 1 <= s.prod (fun y => a y + 1) := by
          exact Finset.one_le_prod (fun y _ => by omega)
        have hmul : a x <= s.prod (fun y => a y + 1) * a x := by
          simpa [one_mul] using Nat.mul_le_mul_right (a x) hprod
        calc
          1 + (a x + s.sum a) = a x + (1 + s.sum a) := by omega
          _ <= a x + s.prod (fun y => a y + 1) := Nat.add_le_add_left ih _
          _ <= s.prod (fun y => a y + 1) * a x +
                s.prod (fun y => a y + 1) := Nat.add_le_add_right hmul _
          _ = (a x + 1) * s.prod (fun y => a y + 1) := by ring
  have hsmooth_bound : forall (m V : Nat),
      0 < m ->
      (forall p : Nat, p.Prime -> p ∣ m -> p <= V) ->
      m <= V ^ (ArithmeticFunction.sigma 0 m - 1) := by
    intro m V hm hsmooth
    by_cases hm1 : m = 1
    · subst m
      simp
    have hm0 : m ≠ 0 := by omega
    obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hm1
    have hV : 1 <= V := le_trans hqprime.one_lt.le (hsmooth q hqprime hqdvd)
    have hsigma : ArithmeticFunction.sigma 0 m =
        m.primeFactors.prod (fun p => m.factorization p + 1) := by
      rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
      simp
    have hmprod : m.primeFactors.prod (fun p =>
        p ^ (m.factorization p)) = m := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact Nat.prod_factorization_pow_eq_self hm0
    have hsum : m.primeFactors.sum m.factorization <=
        ArithmeticFunction.sigma 0 m - 1 := by
      have h := hone_add_sum_le_prod_succ m.primeFactors m.factorization
      rw [← hsigma] at h
      omega
    calc
      m = m.primeFactors.prod (fun p => p ^ (m.factorization p)) := hmprod.symm
      _ <= m.primeFactors.prod (fun p => V ^ (m.factorization p)) := by
        apply Finset.prod_le_prod'
        intro p hp
        exact Nat.pow_le_pow_left
          (hsmooth p (Nat.prime_of_mem_primeFactors hp)
            (Nat.dvd_of_mem_primeFactors hp)) _
      _ = V ^ m.primeFactors.sum m.factorization := by
        exact Finset.prod_pow_eq_pow_sum _ _ _
      _ <= V ^ (ArithmeticFunction.sigma 0 m - 1) :=
        pow_le_pow_right' hV hsum
  have hexists : forall i : Fin W, exists p : Nat,
      p.Prime /\ W < p /\ p ∣ n - (K + (i : Nat)) := by
    intro i
    have hiW : (i : Nat) < W := i.isLt
    have hkpos : 0 < K + (i : Nat) := by omega
    have hkn : K + (i : Nat) < n := by omega
    have hmpos : 0 < n - (K + (i : Nat)) := by omega
    by_contra hnone
    push Not at hnone
    have hsmooth : forall p : Nat, p.Prime ->
        p ∣ n - (K + (i : Nat)) -> p <= W := by
      intro p hp hpdvd
      apply le_of_not_gt
      intro hWp
      exact hnone p hp hWp hpdvd
    have hbase := hsmooth_bound (n - (K + (i : Nat))) W hmpos hsmooth
    have hsub := Nat.sub_le_sub_right (hbudget i) 1
    have hexp : ArithmeticFunction.sigma 0 (n - (K + (i : Nat))) - 1 <=
        K + (i : Nat) + 1 := by omega
    have hpbound : n - (K + (i : Nat)) <=
        W ^ (K + (i : Nat) + 1) :=
      hbase.trans (pow_le_pow_right' hW hexp)
    exact (not_lt_of_ge hpbound) (hlarge i)
  choose P hPprime hPlarge hPdvd using hexists
  refine ⟨P, ?_, ?_⟩
  · intro i
    exact ⟨hPprime i, hPlarge i, hPdvd i⟩
  · intro i j hij
    by_contra hne
    have hcoe : (i : Nat) ≠ (j : Nat) := by
      intro h
      apply hne
      exact Fin.ext h
    rcases lt_or_gt_of_ne hcoe with hijlt | hjilt
    · have hjW : (j : Nat) < W := j.isLt
      have hjn : K + (j : Nat) < n := by omega
      have hdvdj : P i ∣ n - (K + (j : Nat)) := by
        simpa [hij] using hPdvd j
      have hgapdvd : P i ∣ (j : Nat) - (i : Nat) := by
        have h := Nat.dvd_sub (hPdvd i) hdvdj
        have hgap : (n - (K + (i : Nat))) - (n - (K + (j : Nat))) =
            (j : Nat) - (i : Nat) := by omega
        rwa [hgap] at h
      have hgap_pos : 0 < (j : Nat) - (i : Nat) := by omega
      have hPle : P i <= (j : Nat) - (i : Nat) :=
        Nat.le_of_dvd hgap_pos hgapdvd
      have hPW : W < P i := hPlarge i
      omega
    · have hiW : (i : Nat) < W := i.isLt
      have hin : K + (i : Nat) < n := by omega
      have hdvdi : P j ∣ n - (K + (i : Nat)) := by
        simpa [hij] using hPdvd i
      have hgapdvd : P j ∣ (i : Nat) - (j : Nat) := by
        have h := Nat.dvd_sub (hPdvd j) hdvdi
        have hgap : (n - (K + (j : Nat))) - (n - (K + (i : Nat))) =
            (i : Nat) - (j : Nat) := by omega
        rwa [hgap] at h
      have hgap_pos : 0 < (i : Nat) - (j : Nat) := by omega
      have hPle : P j <= (i : Nat) - (j : Nat) :=
        Nat.le_of_dvd hgap_pos hgapdvd
      have hPW : W < P j := hPlarge j
      omega

/-- Exact Formal-Conjectures-shaped first-block corollary.  A candidate whose
first `W` shifted values all escape their `W`-smooth size thresholds supplies
`W` distinct prime factors larger than `W`. -/
theorem erdos647_candidate_prefix_produces_distinct_large_primes :
    forall (n W : Nat),
      1 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      (forall i : Fin W,
        W ^ ((i : Nat) + 2) < n - (1 + (i : Nat))) ->
      exists P : Fin W -> Nat,
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P := by
  classical
  intro n W hW hWn hcand hlarge
  have hnpos : 0 < n := by omega
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hbudget : forall i : Fin W,
      ArithmeticFunction.sigma 0 (n - (1 + (i : Nat))) <=
        1 + (i : Nat) + 2 := by
    intro i
    have hiW : (i : Nat) < W := i.isLt
    have hshiftpos : 0 < 1 + (i : Nat) := by omega
    have hshiftn : 1 + (i : Nat) < n := by omega
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
    let m : Fin n := ⟨n - (1 + (i : Nat)), by omega⟩
    have hm : f m <= n + 2 := le_trans (le_ciSup hbdd m) hcand
    dsimp [f, m] at hm
    omega
  have hcore := erdos647_block_budgets_produce_distinct_large_primes
    n 1 W hW (by omega) (by omega) hbudget
    (fun i => by
      have hexp : 1 + (i : Nat) + 1 = (i : Nat) + 2 := by omega
      rw [hexp]
      exact hlarge i)
  simpa [Nat.add_assoc] using hcore

/-- Scalar growing-gauntlet interface.  The single endpoint inequality
`W^(W+1) < n-W` implies every power threshold required by the first-`W`
candidate-prefix theorem. -/
theorem erdos647_candidate_scalar_gap_produces_distinct_large_primes :
    forall (n W : Nat),
      1 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      W ^ (W + 1) < n - W ->
      exists P : Fin W -> Nat,
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P := by
  intro n W hW hWn hcand hscalar
  apply erdos647_candidate_prefix_produces_distinct_large_primes
    n W hW hWn hcand
  intro i
  have hiW : (i : Nat) < W := i.isLt
  have hexp : (i : Nat) + 2 <= W + 1 := by omega
  have hpow : W ^ ((i : Nat) + 2) <= W ^ (W + 1) :=
    pow_le_pow_right' hW hexp
  have hsub : n - W <= n - (1 + (i : Nat)) := by omega
  exact lt_of_le_of_lt hpow (lt_of_lt_of_le hscalar hsub)

/-- Quantitative shared-host consequence.  An injective family of `W` primes,
all strictly larger than `W` and all dividing one positive integer `H`, forces
the sharper accumulation bound `(W + 1)^W <= H`. -/
theorem erdos647_injective_large_primes_shared_host_bound :
    forall (W H : Nat) (P : Fin W -> Nat),
      0 < H ->
      (forall i : Fin W, (P i).Prime /\ W < P i /\ P i ∣ H) ->
      Function.Injective P ->
      (W + 1) ^ W <= H := by
  classical
  intro W H P hH hP hinj
  let primes : Finset Nat := Finset.univ.image P
  have hcard : primes.card = W := by
    dsimp [primes]
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hprime : ∀ p ∈ primes, p.Prime := by
    intro p hp
    dsimp [primes] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact (hP i).1
  have hsubset : primes ⊆ H.primeFactors := by
    intro p hp
    have hpimage := hp
    dsimp [primes] at hpimage
    simp only [Finset.mem_image] at hpimage
    obtain ⟨i, _, rfl⟩ := hpimage
    exact Nat.mem_primeFactors.mpr
      ⟨(hP i).1, (hP i).2.2, ne_of_gt hH⟩
  have hprodDvd : (∏ p ∈ primes, p) ∣ H := by
    exact (Finset.prod_dvd_prod_of_subset primes H.primeFactors
      (fun p => p) hsubset).trans (Nat.prod_primeFactors_dvd H)
  calc
    (W + 1) ^ W = (W + 1) ^ primes.card := by rw [hcard]
    _ = ∏ p ∈ primes, (W + 1) := by simp
    _ <= ∏ p ∈ primes, p := by
      apply Finset.prod_le_prod'
      intro p hp
      have hpW : W < p := by
        dsimp [primes] at hp
        simp only [Finset.mem_image] at hp
        obtain ⟨i, _, rfl⟩ := hp
        exact (hP i).2.1
      omega
    _ <= H := Nat.le_of_dvd hH hprodDvd

/-- A candidate prefix satisfying the scalar smoothness-escape condition
produces an injective prime family with pairwise CRT-remainder dominance. -/
theorem erdos647_candidate_scalar_gap_crt_pair_dominance :
    forall (n W : Nat),
      1 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      W ^ (W + 1) < n - W ->
      exists P : Fin W -> Nat,
        ((forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P) /\
        (forall i j : Fin W, i ≠ j ->
          P i <= n % (∏ k : Fin W, P k) \/
          P j <= n % (∏ k : Fin W, P k)) := by
  classical
  intro n W hW hWn hcand hscalar
  obtain ⟨P, hP, hinj⟩ :=
    erdos647_candidate_scalar_gap_produces_distinct_large_primes
      n W hW hWn hcand hscalar
  refine ⟨P, ⟨hP, hinj⟩, ?_⟩
  intro i j hij
  let Q : Nat := ∏ k : Fin W, P k
  let R : Nat := n % Q
  have hPkQ : forall k : Fin W, P k ∣ Q := by
    intro k
    dsimp [Q]
    exact Finset.dvd_prod_of_mem P (Finset.mem_univ k)
  have hresidue : forall k : Fin W, R % P k = 1 + (k : Nat) := by
    intro k
    have hshiftP : 1 + (k : Nat) < P k := by
      have hshiftW : 1 + (k : Nat) <= W := by omega
      exact lt_of_le_of_lt hshiftW (hP k).2.1
    have hshiftn : 1 + (k : Nat) < n := by omega
    have hsplit : n = (1 + (k : Nat)) + (n - (1 + (k : Nat))) := by
      simpa [Nat.add_comm] using (Nat.sub_add_cancel hshiftn.le).symm
    have hzero : (n - (1 + (k : Nat))) % P k = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (hP k).2.2
    calc
      R % P k = n % P k := Nat.mod_mod_of_dvd n (hPkQ k)
      _ = ((1 + (k : Nat)) + (n - (1 + (k : Nat)))) % P k := by
        rw [← hsplit]
      _ = 1 + (k : Nat) := by
        simpa [Nat.add_mod, hzero] using Nat.mod_eq_of_lt hshiftP
  have hpair : P i <= R \/ P j <= R := by
    by_cases hi : P i <= R
    · exact Or.inl hi
    right
    by_contra hj
    have hRi : R < P i := Nat.lt_of_not_ge hi
    have hRj : R < P j := Nat.lt_of_not_ge hj
    have hei : R = 1 + (i : Nat) := by
      have h := hresidue i
      rwa [Nat.mod_eq_of_lt hRi] at h
    have hej : R = 1 + (j : Nat) := by
      have h := hresidue j
      rwa [Nat.mod_eq_of_lt hRj] at h
    apply hij
    apply Fin.ext
    omega
  simpa [R, Q] using hpair

/-- Exceptional-index form of the candidate-prefix CRT accumulation theorem. -/
theorem erdos647_candidate_scalar_gap_crt_exceptional_index :
    forall (n W : Nat),
      1 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      W ^ (W + 1) < n - W ->
      exists (P : Fin W -> Nat) (e : Fin W),
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P /\
        (forall i : Fin W, i ≠ e ->
          P i <= n % (∏ k : Fin W, P k)) := by
  intro n W hW hWn hcand hscalar
  obtain ⟨P, ⟨hP, hinj⟩, hpair⟩ :=
    erdos647_candidate_scalar_gap_crt_pair_dominance
      n W hW hWn hcand hscalar
  let R := n % (∏ k : Fin W, P k)
  have hex : exists e : Fin W, forall i : Fin W, i ≠ e -> P i <= R := by
    by_cases hlarge : exists e : Fin W, R < P e
    · obtain ⟨e, he⟩ := hlarge
      refine ⟨e, ?_⟩
      intro i hie
      rcases hpair i e hie with hi | he'
      · exact hi
      · omega
    · let e : Fin W := ⟨0, by omega⟩
      refine ⟨e, ?_⟩
      intro i _
      exact le_of_not_gt (fun hi => hlarge ⟨i, hi⟩)
  obtain ⟨e, he⟩ := hex
  exact ⟨P, e, hP, hinj, by simpa [R] using he⟩

/-- Candidate-facing arbitrary-prefix product envelope: after deleting one
selected prime, every other selected prime accumulates below the corresponding
power of the common CRT remainder. -/
theorem erdos647_candidate_scalar_gap_crt_product_envelope :
    forall (n W : Nat),
      1 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      W ^ (W + 1) < n - W ->
      exists (P : Fin W -> Nat) (e : Fin W),
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P /\
        (∏ i ∈ Finset.univ.erase e, P i) <=
          (n % (∏ k : Fin W, P k)) ^ (W - 1) := by
  intro n W hW hWn hcand hscalar
  obtain ⟨P, e, hP, hinj, he⟩ :=
    erdos647_candidate_scalar_gap_crt_exceptional_index
      n W hW hWn hcand hscalar
  refine ⟨P, e, hP, hinj, ?_⟩
  calc
    (∏ i ∈ Finset.univ.erase e, P i) <=
        ∏ _i ∈ Finset.univ.erase e,
          (n % (∏ k : Fin W, P k)) := by
      apply Finset.prod_le_prod'
      intro i hi
      exact he i (Finset.ne_of_mem_erase hi)
    _ = (n % (∏ k : Fin W, P k)) ^
        (Finset.univ.erase e).card := by simp
    _ = (n % (∏ k : Fin W, P k)) ^ (W - 1) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ e)]
      simp

/-- If all but one of `W` factors exceed `W`, a product envelope at
exponent `W - 1` forces the envelope base itself to exceed `W`. -/
theorem erdos647_product_envelope_forces_remainder_large :
    forall (W R : Nat) (P : Fin W -> Nat) (e : Fin W),
      2 <= W ->
      (forall i : Fin W, W < P i) ->
      (∏ i ∈ Finset.univ.erase e, P i) <= R ^ (W - 1) ->
      W < R := by
  classical
  intro W R P e hW hP henv
  have hcard : (Finset.univ.erase e).card = W - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ e)]
    simp
  have hlower :
      (W + 1) ^ (W - 1) <=
        (∏ i ∈ Finset.univ.erase e, P i) := by
    calc
      (W + 1) ^ (W - 1) =
          ∏ _i ∈ Finset.univ.erase e, (W + 1) := by
        simp [hcard]
      _ <= ∏ i ∈ Finset.univ.erase e, P i := by
        apply Finset.prod_le_prod'
        intro i _
        exact hP i
  have hpowers : (W + 1) ^ (W - 1) <= R ^ (W - 1) :=
    hlower.trans henv
  have hexp : W - 1 ≠ 0 := by omega
  have hbase : W + 1 <= R :=
    (Nat.pow_le_pow_iff_left hexp).mp hpowers
  omega

/-- Candidate-facing remainder growth: under the scalar prefix gap, the
common CRT remainder is already larger than the entire prefix width. -/
theorem erdos647_candidate_scalar_gap_crt_remainder_large :
    forall (n W : Nat),
      2 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      W ^ (W + 1) < n - W ->
      exists (P : Fin W -> Nat) (e : Fin W),
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P /\
        W < n % (∏ k : Fin W, P k) /\
        (∏ i ∈ Finset.univ.erase e, P i) <=
          (n % (∏ k : Fin W, P k)) ^ (W - 1) := by
  intro n W hW hWn hcand hscalar
  obtain ⟨P, e, hP, hinj, henv⟩ :=
    erdos647_candidate_scalar_gap_crt_product_envelope
      n W (by omega) hWn hcand hscalar
  have hR :=
    erdos647_product_envelope_forces_remainder_large
      W (n % (∏ k : Fin W, P k)) P e hW
        (fun i => (hP i).2.1) henv
  exact ⟨P, e, hP, hinj, hR, henv⟩

/-- A full injective family of prime factors re-enters the candidate budget at
the remainder modulo its product.  The positive-remainder hypothesis is kept
explicit so this lemma can be reused independently of how the residues arose. -/
theorem erdos647_full_prime_product_reentry_bound :
    forall (n W : Nat) (P : Fin W -> Nat),
      0 < W ->
      Function.Injective P ->
      (forall i : Fin W, (P i).Prime) ->
      0 < n % (∏ i : Fin W, P i) ->
      (∏ i : Fin W, P i) < n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      2 ^ W <= n % (∏ i : Fin W, P i) + 2 := by
  classical
  intro n W P hW hinj hprime hRpos hQn hcand
  let Q : Nat := ∏ i : Fin W, P i
  let R : Nat := n % Q
  have hRpos' : 0 < R := by
    simpa [R, Q] using hRpos
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun i _ => (hprime i).pos)
  have hRltQ : R < Q := by
    dsimp [R]
    exact Nat.mod_lt n hQpos
  have hRltN : R < n := lt_trans hRltQ hQn
  have hQhost : Q ∣ n - R := by
    refine ⟨n / Q, ?_⟩
    have hdecomp := Nat.mod_add_div n Q
    dsimp [R]
    omega
  have hhostpos : 0 < n - R := by
    exact Nat.sub_pos_of_lt hRltN
  let S : Finset Nat := Finset.univ.image P
  have hScard : S.card = W := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr hinj.injOn]
    simp
  have hPiQ : forall i : Fin W, P i ∣ Q := by
    intro i
    dsimp [Q]
    exact Finset.dvd_prod_of_mem P (Finset.mem_univ i)
  have hS : forall p, p ∈ S -> p.Prime /\ p ∣ n - R := by
    intro p hp
    dsimp [S] at hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact ⟨hprime i, (hPiQ i).trans hQhost⟩
  have htau : 2 ^ W <= ArithmeticFunction.sigma 0 (n - R) := by
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

/-- The scalar-gap construction now carries both quantitative consequences:
its CRT remainder exceeds the prefix width, and if the complete selected
product lies below `n`, candidatehood forces the exponential re-entry
budget. -/
theorem erdos647_candidate_scalar_gap_crt_accumulation :
    forall (n W : Nat),
      2 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      W ^ (W + 1) < n - W ->
      exists (P : Fin W -> Nat) (e : Fin W),
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P /\
        W < n % (∏ k : Fin W, P k) /\
        (∏ i ∈ Finset.univ.erase e, P i) <=
          (n % (∏ k : Fin W, P k)) ^ (W - 1) /\
        ((∏ k : Fin W, P k) < n ->
          2 ^ W <= n % (∏ k : Fin W, P k) + 2) := by
  intro n W hW hWn hcand hscalar
  obtain ⟨P, e, hP, hinj, hR, henv⟩ :=
    erdos647_candidate_scalar_gap_crt_remainder_large
      n W hW hWn hcand hscalar
  refine ⟨P, e, hP, hinj, hR, henv, ?_⟩
  intro hQn
  exact erdos647_full_prime_product_reentry_bound
    n W P (by omega) hinj (fun i => (hP i).1)
      (by omega) hQn hcand

/-- Clean global alternative for a scalar-gap candidate prefix: either the
selected prime product has crossed `n`, or its CRT remainder must pay the
full exponential divisor budget. -/
theorem erdos647_candidate_scalar_gap_product_or_reentry :
    forall (n W : Nat),
      2 <= W ->
      W + 1 <= n ->
      (⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2 ->
      W ^ (W + 1) < n - W ->
      exists (P : Fin W -> Nat) (e : Fin W),
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) /\
        Function.Injective P /\
        W < n % (∏ k : Fin W, P k) /\
        (∏ i ∈ Finset.univ.erase e, P i) <=
          (n % (∏ k : Fin W, P k)) ^ (W - 1) /\
        (n < (∏ k : Fin W, P k) \/
          2 ^ W <= n % (∏ k : Fin W, P k) + 2) := by
  intro n W hW hWn hcand hscalar
  obtain ⟨P, e, hP, hinj, hR, henv, hreentry⟩ :=
    erdos647_candidate_scalar_gap_crt_accumulation
      n W hW hWn hcand hscalar
  refine ⟨P, e, hP, hinj, hR, henv, ?_⟩
  by_cases hcross : n < (∏ k : Fin W, P k)
  · exact Or.inl hcross
  right
  apply hreentry
  have hne : (∏ k : Fin W, P k) ≠ n := by
    intro heq
    rw [heq, Nat.mod_self] at hR
    omega
  omega

/-- Scalar-gap exclusion engine.  To rule out candidatehood it now suffices
to show that every admissible selected prime family both fails to cross `n`
and has a CRT remainder too small to pay the exponential re-entry budget. -/
theorem erdos647_not_candidate_of_scalar_gap_crt_obstruction :
    forall (n W : Nat),
      2 <= W ->
      W + 1 <= n ->
      W ^ (W + 1) < n - W ->
      (forall P : Fin W -> Nat,
        (forall i : Fin W,
          (P i).Prime /\ W < P i /\ P i ∣ n - (1 + (i : Nat))) ->
        Function.Injective P ->
        (∏ k : Fin W, P k) <= n /\
        n % (∏ k : Fin W, P k) + 2 < 2 ^ W) ->
      ¬((⨆ m : Fin n,
        (m : Nat) + ArithmeticFunction.sigma 0 m) <= n + 2) := by
  intro n W hW hWn hscalar hobstruct hcand
  obtain ⟨P, _e, hP, hinj, _hR, _henv, halt⟩ :=
    erdos647_candidate_scalar_gap_product_or_reentry
      n W hW hWn hcand hscalar
  obtain ⟨hQle, hsmall⟩ := hobstruct P hP hinj
  rcases halt with hcross | hreentry
  · omega
  · omega
