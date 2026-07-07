import Mathlib

/-!
# Erdős Problem 291, part (ii) — companion lemma

Erdős #291 (open): with `L_n = lcm(1,…,n)` and `a_n` defined by
`∑_{1≤k≤n} 1/k = a_n / L_n`, is `gcd(a_n, L_n) = 1` for infinitely many `n`?

Part (ii) — the EASY, **already-known** direction (answer: yes, trivially,
Steinerberger): `gcd(a_n, L_n) > 1` occurs for infinitely many `n`. This file
gives a self-contained, kernel-verified proof.

**We do NOT resolve the open #291 (part i).** This is the companion `research
solved` statement, shipped `sorry` in google-deepmind/formal-conjectures.

## Construction

Take `n = 2·3^k` (`k ≥ 1`). Then `v₃(L_n) = k`, so in
`a_n = ∑_{j=1}^n L_n/j` every term `L_n/j` is divisible by 3 EXCEPT the two
with `3^k ∣ j`, namely `j = 3^k` and `j = 2·3^k`. Writing `L_n = 3^k · M`
(`3 ∤ M`, and `2 ∣ M` since `2 ≤ n`), those two contributions are
`M + M/2 = 3·(M/2) ≡ 0 (mod 3)`. Hence `3 ∣ a_n`; also `3 ∣ L_n` (as `3 ≤ n`),
so `3 ∣ gcd(a_n, L_n)` and the gcd exceeds 1. The map `k ↦ 2·3^k` is
injective, so the set is infinite. ∎
-/

namespace Erdos291

open Nat Finset

/-- `L n` is the least common multiple of `{1,…,n}` (corpus definition). -/
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm (fun x ↦ x)

/-- `a n` defined by `∑_{1≤k≤n} 1/k = a n / L n` (corpus definition). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, L n / k

-- Sanity: match the corpus's own `test` evaluations.
example : L 1 = 1 ∧ L 2 = 2 ∧ L 3 = 6 ∧ L 4 = 12 := by decide
example : a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 25 := by decide

-- Sanity: the construction n = 2·3^k lands in the target set for small k.
example : Nat.gcd (a 6) (L 6) > 1 := by decide
example : Nat.gcd (a 18) (L 18) > 1 := by decide

/-- `L n ≠ 0`: the lcm of a set of positive numbers. -/
lemma L_ne_zero (n : ℕ) : L n ≠ 0 := by
  rw [L, Finset.lcm_ne_zero_iff]
  intro i hi
  simp only [Finset.mem_Icc] at hi
  omega

/-- Every `j ∈ {1,…,n}` divides `L n`. -/
lemma dvd_L {j n : ℕ} (h : j ∈ Finset.Icc 1 n) : j ∣ L n := by
  rw [L]; exact Finset.dvd_lcm h

/-- The multiples of `3^k` in `{1, …, 2·3^k}` are exactly `3^k` and `2·3^k`. -/
lemma filter_multiples (k : ℕ) :
    (Finset.Icc 1 (2 * 3 ^ k)).filter (fun j => 3 ^ k ∣ j)
      = {3 ^ k, 2 * 3 ^ k} := by
  have hpos : 0 < 3 ^ k := pow_pos (by norm_num) k
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hj1, hj2⟩, t, rfl⟩
    -- 1 ≤ 3^k * t ≤ 2 * 3^k  ⟹  t = 1 ∨ t = 2
    rw [mul_comm 2 (3 ^ k)] at hj2
    have hle : t ≤ 2 := Nat.le_of_mul_le_mul_left hj2 hpos
    have hge : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; simp at hj1
      · exact h
    interval_cases t
    · left; ring
    · right; ring
  · rintro (rfl | rfl)
    · exact ⟨⟨hpos, by omega⟩, dvd_refl _⟩
    · exact ⟨⟨by omega, le_refl _⟩, ⟨2, by ring⟩⟩

/-- `3 ∣ L n` whenever `3 ≤ n` (since `3 ∈ {1,…,n}`). -/
lemma three_dvd_L {n : ℕ} (hn : 3 ≤ n) : 3 ∣ L n :=
  dvd_L (by simp only [Finset.mem_Icc]; omega)

/-- **Crux.** For `n = 2·3^k` (`k ≥ 1`), `3 ∣ a n`. Every term `L n / j` of
`a n = ∑ⱼ L n / j` is divisible by 3 except `j = 3^k` and `j = 2·3^k`, whose
contributions `2t + t = 3t` (where `L n = 2·3^k·t`) are also divisible by 3. -/
lemma three_dvd_a (k : ℕ) : 3 ∣ a (2 * 3 ^ k) := by
  have prime3 : Nat.Prime 3 := by norm_num
  have hpos : 0 < 3 ^ k := pow_pos (by norm_num) k
  have hLne : L (2 * 3 ^ k) ≠ 0 := L_ne_zero _
  -- 3^k ∣ L n, hence v₃(L n) ≥ k
  have h3k_dvd_L : 3 ^ k ∣ L (2 * 3 ^ k) :=
    dvd_L (by simp only [Finset.mem_Icc]; exact ⟨hpos, by omega⟩)
  have vL : k ≤ (L (2 * 3 ^ k)).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization prime3 hLne).mp h3k_dvd_L
  -- vanishing terms: 3 ∣ L n / j when ¬ 3^k ∣ j
  have hvanish : ∀ j ∈ (Finset.Icc 1 (2 * 3 ^ k)).filter (fun j => ¬ 3 ^ k ∣ j),
      3 ∣ L (2 * 3 ^ k) / j := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨⟨hj1, hj2⟩, hjnk⟩ := hj
    have hj_dvd : j ∣ L (2 * 3 ^ k) := dvd_L (by simp only [Finset.mem_Icc]; exact ⟨hj1, hj2⟩)
    have hj_ne : j ≠ 0 := by omega
    have hvj : (j).factorization 3 < k := by
      by_contra h
      exact hjnk ((Nat.Prime.pow_dvd_iff_le_factorization prime3 hj_ne).mpr (not_lt.mp h))
    have hquot_pos : 0 < L (2 * 3 ^ k) / j :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hLne) hj_dvd) (by omega)
    have hone : 1 ≤ (L (2 * 3 ^ k) / j).factorization 3 := by
      rw [Nat.factorization_div hj_dvd]
      simp only [Finsupp.coe_tsub, Pi.sub_apply]
      omega
    exact (Nat.Prime.dvd_iff_one_le_factorization prime3 hquot_pos.ne').mpr hone
  -- the two surviving terms
  have hLn_dvd : 2 * 3 ^ k ∣ L (2 * 3 ^ k) := by
    have hcop : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h2 : 2 ∣ L (2 * 3 ^ k) := dvd_L (by simp only [Finset.mem_Icc]; omega)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2 h3k_dvd_L
  obtain ⟨t, ht⟩ := hLn_dvd
  have e1 : L (2 * 3 ^ k) / 3 ^ k = 2 * t := by
    rw [ht, show 2 * 3 ^ k * t = 3 ^ k * (2 * t) by ring, Nat.mul_div_cancel_left _ hpos]
  have e2 : L (2 * 3 ^ k) / (2 * 3 ^ k) = t := by
    rw [ht, Nat.mul_div_cancel_left _ (by positivity)]
  have hfirst : 3 ∣ (L (2 * 3 ^ k) / 3 ^ k + L (2 * 3 ^ k) / (2 * 3 ^ k)) := by
    rw [e1, e2]; exact ⟨t, by ring⟩
  have hsecond : 3 ∣ ∑ j ∈ (Finset.Icc 1 (2 * 3 ^ k)).filter (fun j => ¬ 3 ^ k ∣ j),
      L (2 * 3 ^ k) / j := Finset.dvd_sum hvanish
  -- split a n and combine
  rw [a, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (2 * 3 ^ k)) (fun j => 3 ^ k ∣ j),
    filter_multiples k, Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
    Finset.sum_singleton]
  exact Nat.dvd_add hfirst hsecond

/-- **Erdős #291, part (ii).** `gcd(aₙ, Lₙ) > 1` for infinitely many `n`
(Steinerberger; the easy already-known direction). We do *not* resolve the
open part (i). -/
theorem infinite_gcd_gt_one :
    {n : ℕ | 1 < Nat.gcd (a n) (L n)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => 2 * 3 ^ (k + 1))
  · intro x y hxy
    simp only [] at hxy
    have h3 : 3 ^ (x + 1) = 3 ^ (y + 1) := by omega
    have := Nat.pow_right_injective (by norm_num) h3
    omega
  · intro k
    have ha := three_dvd_a (k + 1)
    have hL : 3 ∣ L (2 * 3 ^ (k + 1)) :=
      three_dvd_L (by have := pow_pos (show 0 < 3 by norm_num) (k + 1); omega)
    obtain ⟨c, hc⟩ := Nat.dvd_gcd ha hL
    have hgpos : 0 < Nat.gcd (a (2 * 3 ^ (k + 1))) (L (2 * 3 ^ (k + 1))) :=
      Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (L_ne_zero _))
    simp only [Set.mem_setOf_eq]
    omega

/-- Corpus statement shape (`erdos_291.parts.ii`): in the corpus this reads
`answer(True) ↔ {n | gcd(aₙ,Lₙ) > 1}.Infinite`, where `answer(True)` elaborates
to `True`. Discharged directly from `infinite_gcd_gt_one`. -/
theorem erdos_291_parts_ii :
    True ↔ {n : ℕ | Nat.gcd (a n) (L n) > 1}.Infinite :=
  iff_of_true trivial infinite_gcd_gt_one

end Erdos291
