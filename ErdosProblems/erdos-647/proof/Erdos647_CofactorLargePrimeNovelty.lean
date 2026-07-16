import Mathlib

/-!
# Erdos #647 - second-layer cofactor prime novelty

This module records the shift-difference mechanism after one factor has
already been peeled from each shifted value.  If `q_j` divides `n-k_j` and a
selected prime `r_j` divides `q_j`, then `r_j` still divides the original
shifted value.  A prime larger than the width cannot be shared by two distinct
coordinates, since any shared divisor would divide their shift gap.

The block-injectivity root was independently verified through the tracked
proof-search pipeline on 2026-07-16:

* preverification `16c930fa-9320-45d3-adc7-30f8f3797058`
* problem `d4ec93d0-d1e3-4795-9e78-e16218b8d08d`
* episode `5f3b332c-a77c-41a3-bbce-1df5cd67c5ec`
* root hash `98961511386661ef5278869e6cbca3db524dbb7d1b161aa1e0584c184175277a`
* outcome `kernel_verified`
-/

/-- Large prime factors of cofactors at two ordered nearby shifts are
distinct. -/
theorem erdos647_cofactor_large_primes_distinct :
    forall (n W k1 k2 q1 q2 r1 r2 : Nat),
      k1 < k2 ->
      k2 < n ->
      k2 - k1 <= W ->
      q1 ∣ n - k1 ->
      q2 ∣ n - k2 ->
      r1.Prime ->
      r1 ∣ q1 ->
      W < r1 ->
      r2.Prime ->
      r2 ∣ q2 ->
      W < r2 ->
      r1 ≠ r2 := by
  intro n W k1 k2 q1 q2 r1 r2 hk12 hk2n hgap hq1 hq2
    hr1prime hr1q1 hr1large hr2prime hr2q2 hr2large heq
  have hr1shift1 : r1 ∣ n - k1 := hr1q1.trans hq1
  have hr1shift2 : r1 ∣ n - k2 := by
    rw [heq]
    exact hr2q2.trans hq2
  have hr1gap : r1 ∣ k2 - k1 := by
    have h := Nat.dvd_sub hr1shift1 hr1shift2
    have hdiff : (n - k1) - (n - k2) = k2 - k1 := by omega
    rwa [hdiff] at h
  have hgapPos : 0 < k2 - k1 := by omega
  have hr1le : r1 <= k2 - k1 := Nat.le_of_dvd hgapPos hr1gap
  omega

/-- In a consecutive width-`W` block, selecting a prime larger than `W` from
each cofactor produces an injective family of second-layer primes. -/
theorem erdos647_cofactor_large_prime_block_injective :
    forall (n K W : Nat) (q r : Fin W -> Nat),
      K + W <= n ->
      (forall i : Fin W, q i ∣ n - (K + (i : Nat))) ->
      (forall i : Fin W,
        (r i).Prime /\ r i ∣ q i /\ W < r i) ->
      Function.Injective r := by
  intro n K W q r hKW hq hr i j hij
  by_contra hne
  have hcoe : (i : Nat) ≠ (j : Nat) := by
    intro h
    apply hne
    exact Fin.ext h
  rcases lt_or_gt_of_ne hcoe with hijlt | hjilt
  · have hjW : (j : Nat) < W := j.isLt
    have hjn : K + (j : Nat) < n := by omega
    have hgap : (K + (j : Nat)) - (K + (i : Nat)) <= W := by omega
    exact erdos647_cofactor_large_primes_distinct
      n W (K + (i : Nat)) (K + (j : Nat))
      (q i) (q j) (r i) (r j)
      (by omega) hjn hgap (hq i) (hq j)
      (hr i).1 (hr i).2.1 (hr i).2.2
      (hr j).1 (hr j).2.1 (hr j).2.2 hij
  · have hiW : (i : Nat) < W := i.isLt
    have hin : K + (i : Nat) < n := by omega
    have hgap : (K + (i : Nat)) - (K + (j : Nat)) <= W := by omega
    have hne' : r j ≠ r i :=
      erdos647_cofactor_large_primes_distinct
        n W (K + (j : Nat)) (K + (i : Nat))
        (q j) (q i) (r j) (r i)
        (by omega) hin hgap (hq j) (hq i)
        (hr j).1 (hr j).2.1 (hr j).2.2
        (hr i).1 (hr i).2.1 (hr i).2.2
    exact hne' hij.symm
