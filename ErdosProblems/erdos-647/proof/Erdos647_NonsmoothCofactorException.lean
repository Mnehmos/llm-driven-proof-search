import Mathlib

/-!
# Erdős #647 — uniqueness of a nonsmooth square-small cofactor

In a consecutive width-`W` shift block, a prime larger than `W` cannot divide
cofactors at two distinct coordinates: it would divide their nonzero shift
gap, which is smaller than `W`.  Consequently, under a no-cross-pair
hypothesis, at most one cofactor can both have square below `n` and contain a
prime larger than `W`.

Proof-search provenance for the strongest cardinality theorem:

* preverification job: `8e431113-22b7-4246-a622-02c5b150a369`
  (`kernel_pass`);
* problem version: `a8c2aa39-9bb1-4079-9c4f-166c12155df3`;
* episode: `09aa8061-de5e-4466-b815-82a8d7bf55c2`;
* root statement hash:
  `4e4436410270a822217b9c5f3cab8013406e97d750317c095a0533e3760fe316`;
* tracked outcome: `kernel_verified` (`root_proved`).
-/

/-- Large prime factors selected from cofactors at distinct coordinates of a
consecutive shift block are distinct. -/
theorem erdos647_nonsmooth_cofactor_large_primes_distinct :
    ∀ {n K W : ℕ} (q : Fin W → ℕ) (i j : Fin W) {r s : ℕ},
      K + W ≤ n →
      (∀ u : Fin W, q u ∣ n - (K + (u : ℕ))) →
      i ≠ j →
      Nat.Prime r → W < r → r ∣ q i →
      Nat.Prime s → W < s → s ∣ q j →
      r ≠ s := by
  intro n K W q i j r s hKW hq hij hrprime hrW hri
    hsprime hsW hsj hrs
  have hcoe : (i : ℕ) ≠ (j : ℕ) := by
    intro h
    apply hij
    exact Fin.ext h
  rcases lt_or_gt_of_ne hcoe with hijlt | hjilt
  · have hjn : K + (j : ℕ) < n := by
      have hjW := j.isLt
      omega
    have hrshift_i : r ∣ n - (K + (i : ℕ)) := hri.trans (hq i)
    have hrshift_j : r ∣ n - (K + (j : ℕ)) := by
      rw [hrs]
      exact hsj.trans (hq j)
    have hrgap : r ∣ (j : ℕ) - (i : ℕ) := by
      have h := Nat.dvd_sub hrshift_i hrshift_j
      have hdiff :
          (n - (K + (i : ℕ))) - (n - (K + (j : ℕ))) =
            (j : ℕ) - (i : ℕ) := by omega
      rwa [hdiff] at h
    have hgap_pos : 0 < (j : ℕ) - (i : ℕ) := by omega
    have hrle : r ≤ (j : ℕ) - (i : ℕ) :=
      Nat.le_of_dvd hgap_pos hrgap
    have hjW := j.isLt
    omega
  · have hin : K + (i : ℕ) < n := by
      have hiW := i.isLt
      omega
    have hsshift_j : s ∣ n - (K + (j : ℕ)) := hsj.trans (hq j)
    have hsshift_i : s ∣ n - (K + (i : ℕ)) := by
      rw [← hrs]
      exact hri.trans (hq i)
    have hsgap : s ∣ (i : ℕ) - (j : ℕ) := by
      have h := Nat.dvd_sub hsshift_j hsshift_i
      have hdiff :
          (n - (K + (j : ℕ))) - (n - (K + (i : ℕ))) =
            (i : ℕ) - (j : ℕ) := by omega
      rwa [hdiff] at h
    have hgap_pos : 0 < (i : ℕ) - (j : ℕ) := by omega
    have hsle : s ≤ (i : ℕ) - (j : ℕ) :=
      Nat.le_of_dvd hgap_pos hsgap
    have hiW := i.isLt
    omega

/-- Two natural numbers whose squares are below `n` have product below `n`. -/
theorem erdos647_cofactor_product_lt_of_squares_lt :
    ∀ {a b n : ℕ}, a ^ 2 < n → b ^ 2 < n → a * b < n := by
  intro a b n ha hb
  rcases le_total a b with hab | hba
  · have hmul : a * b ≤ b * b := Nat.mul_le_mul_right b hab
    exact hmul.trans_lt (by simpa [pow_two] using hb)
  · have hmul : a * b ≤ a * a := Nat.mul_le_mul_left a hba
    exact hmul.trans_lt (by simpa [pow_two] using ha)

/-- Under the no-cross-pair hypothesis, at most one coordinate has both a
square-small cofactor and a prime divisor larger than the block width. -/
theorem erdos647_nonsmooth_square_small_cofactor_card_le_one :
    ∀ (n K W : ℕ) (q : Fin W → ℕ),
      K + W ≤ n →
      (∀ i : Fin W, q i ∣ n - (K + (i : ℕ))) →
      (∀ (i j : Fin W) (r s : ℕ),
        i ≠ j →
        Nat.Prime r → W < r → r ∣ q i →
        Nat.Prime s → W < s → s ∣ q j →
        r ≠ s → ¬ r * s < n) →
      let S := @Finset.filter (Fin W)
        (fun i : Fin W =>
          (q i) ^ 2 < n ∧
            ∃ r : ℕ, Nat.Prime r ∧ W < r ∧ r ∣ q i)
        (Classical.decPred _)
        Finset.univ
      S.card ≤ 1 := by
  classical
  intro n K W q hKW hq hno
  dsimp
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  by_contra hij
  obtain ⟨hi_sq, r, hrprime, hrW, hri⟩ := hi
  obtain ⟨hj_sq, s, hsprime, hsW, hsj⟩ := hj
  have hrs : r ≠ s :=
    erdos647_nonsmooth_cofactor_large_primes_distinct q i j hKW hq hij
      hrprime hrW hri hsprime hsW hsj
  have hqprod : q i * q j < n :=
    erdos647_cofactor_product_lt_of_squares_lt hi_sq hj_sq
  have hshift_i : 0 < n - (K + (i : ℕ)) := by
    have hiW := i.isLt
    omega
  have hshift_j : 0 < n - (K + (j : ℕ)) := by
    have hjW := j.isLt
    omega
  have hqi_pos : 0 < q i := Nat.pos_of_dvd_of_pos (hq i) hshift_i
  have hqj_pos : 0 < q j := Nat.pos_of_dvd_of_pos (hq j) hshift_j
  have hrle : r ≤ q i := Nat.le_of_dvd hqi_pos hri
  have hsle : s ≤ q j := Nat.le_of_dvd hqj_pos hsj
  have hrsprod : r * s ≤ q i * q j := Nat.mul_le_mul hrle hsle
  exact hno i j r s hij hrprime hrW hri hsprime hsW hsj hrs
    (hrsprod.trans_lt hqprod)
