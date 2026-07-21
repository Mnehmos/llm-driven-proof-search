import Mathlib

/-!
# Erdős #647: injective selection of large shift primes

Large primes extracted from distinct shifts cannot collide once the
smoothness threshold dominates every shift.  This is the selection seam
needed to feed the nonsmooth branch of the maximal-subset descent back into
the CRT re-entry engine.
-/

namespace Erdos647

theorem erdos647_large_shift_prime_injective :
    forall (W n B : Nat) (shift P : Fin W -> Nat),
      Function.Injective shift ->
      (forall i : Fin W,
        shift i < n /\
        shift i <= B /\
        (P i).Prime /\
        B < P i /\
        P i ∣ n - shift i) ->
      Function.Injective P := by
  intro W n B shift P hshift hdata i j hij
  apply hshift
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hdvd_i : P i ∣ n - shift i := (hdata i).2.2.2.2
    have hdvd_j : P i ∣ n - shift j := by
      simpa [hij] using (hdata j).2.2.2.2
    have hdvd_z :
        (P i : Int) ∣ (shift j : Int) - (shift i : Int) := by
      have hi_le : shift i <= n := (hdata i).1.le
      have hj_le : shift j <= n := (hdata j).1.le
      have hdvd_i_z : (P i : Int) ∣ (n - shift i : Nat) := by
        exact_mod_cast hdvd_i
      have hdvd_j_z : (P i : Int) ∣ (n - shift j : Nat) := by
        exact_mod_cast hdvd_j
      have hsub := dvd_sub hdvd_i_z hdvd_j_z
      simpa [Nat.cast_sub hi_le, Nat.cast_sub hj_le] using hsub
    have hdvd_cast :
        (P i : Int) ∣ ((shift j - shift i : Nat) : Int) := by
      simpa [Nat.cast_sub hlt.le] using hdvd_z
    have hdvd_nat : P i ∣ shift j - shift i := by
      exact_mod_cast hdvd_cast
    have hP_le : P i <= shift j - shift i :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hdvd_nat
    have hdiff_le : shift j - shift i <= B := by
      exact (Nat.sub_le (shift j) (shift i)).trans (hdata j).2.1
    exact (not_lt_of_ge (hP_le.trans hdiff_le)) (hdata i).2.2.2.1
  · have hdvd_j : P j ∣ n - shift j := (hdata j).2.2.2.2
    have hdvd_i : P j ∣ n - shift i := by
      simpa [hij] using (hdata i).2.2.2.2
    have hdvd_z :
        (P j : Int) ∣ (shift i : Int) - (shift j : Int) := by
      have hi_le : shift i <= n := (hdata i).1.le
      have hj_le : shift j <= n := (hdata j).1.le
      have hdvd_j_z : (P j : Int) ∣ (n - shift j : Nat) := by
        exact_mod_cast hdvd_j
      have hdvd_i_z : (P j : Int) ∣ (n - shift i : Nat) := by
        exact_mod_cast hdvd_i
      have hsub := dvd_sub hdvd_j_z hdvd_i_z
      simpa [Nat.cast_sub hi_le, Nat.cast_sub hj_le] using hsub
    have hdvd_cast :
        (P j : Int) ∣ ((shift i - shift j : Nat) : Int) := by
      simpa [Nat.cast_sub hgt.le] using hdvd_z
    have hdvd_nat : P j ∣ shift i - shift j := by
      exact_mod_cast hdvd_cast
    have hP_le : P j <= shift i - shift j :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdvd_nat
    have hdiff_le : shift i - shift j <= B := by
      exact (Nat.sub_le (shift i) (shift j)).trans (hdata i).2.1
    exact (not_lt_of_ge (hP_le.trans hdiff_le)) (hdata j).2.2.2.1

/-- Pointwise large-prime witnesses on distinct bounded shifts can be chosen
as an injective prime family. -/
theorem erdos647_exists_injective_large_shift_primes :
    forall (W n B : Nat) (shift q : Fin W -> Nat),
      Function.Injective shift ->
      (forall i : Fin W,
        shift i < n /\
        shift i <= B /\
        q i ∣ n - shift i /\
        exists p : Nat, p.Prime /\ p ∣ q i /\ B < p) ->
      exists P : Fin W -> Nat,
        Function.Injective P /\
        forall i : Fin W,
          (P i).Prime /\ P i ∣ q i /\ B < P i := by
  intro W n B shift q hshift hdata
  choose P hPprime hPq hPB using fun i => (hdata i).2.2.2
  refine ⟨P, ?_, fun i => ⟨hPprime i, hPq i, hPB i⟩⟩
  apply erdos647_large_shift_prime_injective W n B shift P hshift
  intro i
  exact ⟨(hdata i).1, (hdata i).2.1, hPprime i, hPB i,
    (hPq i).trans (hdata i).2.2.1⟩

end Erdos647
