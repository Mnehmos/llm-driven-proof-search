import Mathlib

/-!
# Erdos #647 - conditional second-layer catalog assembly

This theorem packages the deterministic conclusion available after two
one-element exceptional catalogs have been bounded.  Away from the possible
first-layer square exception and the possible cofactor large-prime exception,
each retained coordinate has a proper coprime factorization, a square-small
cofactor, a `W`-smooth cofactor, and an explicit smoothness bound.

The theorem is conditional: it assembles already-established local
factorization data and two cardinality bounds.  It does not assert that those
hypotheses hold for every candidate.

The complete assembly root was independently verified through the tracked
proof-search pipeline on 2026-07-16:

* preverification `b60dd07f-5c69-4d31-87fb-d346dfdffe50`
* problem `d3ae4373-0f5d-452a-85f7-22ed6a171a8c`
* episode `d50528e3-f045-4a4a-ae5f-df336cc05a8b`
* root hash `d4eaaaf497e5809d922373d35a6bdc4a0a6599df65857c42cf7f748e4ffbc333`
* outcome `kernel_verified`
-/

/-- Removing at most one square exception and at most one large-cofactor-prime
exception leaves at least `W-2` fully controlled second-layer coordinates. -/
theorem erdos647_second_layer_catalog_assembly :
    forall (n W : Nat) (P q : Fin W -> Nat),
      1 <= W ->
      (Finset.univ.filter (fun i : Fin W => (P i) ^ 2 < n)).card <= 1 ->
      (Finset.univ.filter (fun i : Fin W =>
        ∃ r ∈ (q i).primeFactors, W < r)).card <= 1 ->
      (forall i : Fin W,
        i ∉ Finset.univ.filter (fun j : Fin W => (P j) ^ 2 < n) ->
        (P i).Prime /\
        0 < q i /\
        n - (1 + (i : Nat)) = P i * q i /\
        q i < P i /\
        Nat.Coprime (P i) (q i) /\
        2 * ArithmeticFunction.sigma 0 (q i) <= 1 + (i : Nat) + 2) ->
      exists J : Finset (Fin W),
        W <= J.card + 2 /\
        ∀ i ∈ J,
          (P i).Prime /\
          0 < q i /\
          n - (1 + (i : Nat)) = P i * q i /\
          q i < P i /\
          Nat.Coprime (P i) (q i) /\
          2 * ArithmeticFunction.sigma 0 (q i) <= 1 + (i : Nat) + 2 /\
          (q i) ^ 2 < n /\
          (forall r : Nat, r.Prime -> r ∣ q i -> r <= W) /\
          q i <= W ^ ((1 + (i : Nat)) / 2) := by
  classical
  intro n W P q hW hAcard hBcard hdata
  let A : Finset (Fin W) :=
    Finset.univ.filter (fun i : Fin W => (P i) ^ 2 < n)
  let B : Finset (Fin W) :=
    Finset.univ.filter (fun i : Fin W =>
      ∃ r ∈ (q i).primeFactors, W < r)
  let J : Finset (Fin W) := Finset.univ \ (A ∪ B)
  change A.card <= 1 at hAcard
  change B.card <= 1 at hBcard
  change forall i : Fin W, i ∉ A ->
    (P i).Prime /\
    0 < q i /\
    n - (1 + (i : Nat)) = P i * q i /\
    q i < P i /\
    Nat.Coprime (P i) (q i) /\
    2 * ArithmeticFunction.sigma 0 (q i) <= 1 + (i : Nat) + 2 at hdata
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
    obtain ⟨s, hsprime, hsdvd⟩ := Nat.exists_prime_and_dvd hm1
    have hV : 1 <= V := le_trans hsprime.one_lt.le (hsmooth s hsprime hsdvd)
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
  have hUnionCard : (A ∪ B).card <= 2 := by
    calc
      (A ∪ B).card <= A.card + B.card := Finset.card_union_le _ _
      _ <= 2 := by omega
  have hUnionSub : A ∪ B ⊆ (Finset.univ : Finset (Fin W)) := by
    exact Finset.subset_univ _
  have hsplit : J.card + (A ∪ B).card = W := by
    dsimp [J]
    simpa using Finset.card_sdiff_add_card_eq_card hUnionSub
  refine ⟨J, by omega, ?_⟩
  intro i hiJ
  have hiParts := Finset.mem_sdiff.mp hiJ
  have hiA : i ∉ A := by
    intro hi
    exact hiParts.2 (Finset.mem_union_left B hi)
  have hiB : i ∉ B := by
    intro hi
    exact hiParts.2 (Finset.mem_union_right A hi)
  obtain ⟨hPprime, hqpos, hfactor, hqP, hcop, hbudget⟩ := hdata i hiA
  have hsmooth : forall r : Nat, r.Prime -> r ∣ q i -> r <= W := by
    intro r hrprime hrdvd
    apply le_of_not_gt
    intro hWr
    apply hiB
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨r, Nat.mem_primeFactors.mpr ⟨hrprime, hrdvd, by omega⟩, hWr⟩
  have hqSquare : (q i) ^ 2 < n := by
    have hmul : q i * q i < P i * q i :=
      Nat.mul_lt_mul_of_pos_right hqP hqpos
    have hshiftPos : 0 < n - (1 + (i : Nat)) := by
      rw [hfactor]
      exact Nat.mul_pos hPprime.pos hqpos
    calc
      (q i) ^ 2 = q i * q i := by ring
      _ < P i * q i := hmul
      _ = n - (1 + (i : Nat)) := hfactor.symm
      _ < n := by omega
  have hbase : q i <= W ^ (ArithmeticFunction.sigma 0 (q i) - 1) :=
    hsmooth_bound (q i) W hqpos hsmooth
  have hexp : ArithmeticFunction.sigma 0 (q i) - 1 <=
      (1 + (i : Nat)) / 2 := by
    omega
  have hfinal : q i <= W ^ ((1 + (i : Nat)) / 2) :=
    hbase.trans (pow_le_pow_right' hW hexp)
  exact ⟨hPprime, hqpos, hfactor, hqP, hcop, hbudget,
    hqSquare, hsmooth, hfinal⟩
