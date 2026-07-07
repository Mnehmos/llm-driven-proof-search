import Mathlib

/-!
# Fermat's theorem `x⁴ − y⁴ ≠ z²` (no right triangle with square area)

Mathlib has `not_fermat_42` (`a⁴ + b⁴ ≠ c²`, in `Mathlib.NumberTheory.FLT.Four`)
but **not** the companion minus-version `x⁴ − y⁴ ≠ z²` (Fermat's theorem that no
right triangle with integer sides has a perfect-square area; equivalently the
elliptic curve `y² = x³ − x` has rank 0).

This file proves it by infinite descent on `a.natAbs`, using
`PythagoreanTriple.coprime_classification` (applied twice) and
`Int.sq_of_gcd_eq_one`. The headline result is `Int.sq_ne_fourth_sub_fourth`:
`x⁴ − y⁴ = z²` forces `y = 0` or `z = 0`.

This is a self-contained, Mathlib-import-only extraction intended for upstream
contribution as a companion to `not_fermat_42`.

## Main statements
* `Int.not_fermat_sub_coprime` : the coprime core, `a⁴ ≠ b⁴ + c²`.
* `Int.sq_ne_fourth_sub_fourth` : the general form, `x⁴ − y⁴ = z² → y = 0 ∨ z = 0`.
-/

namespace Int

/-- From `2mn = b²` with `gcd(m,n)=1` and `m` even: `m² = 4k0⁴`, `n² = n0⁴` with
`gcd(k0,n0)=1` and `n0²` odd. -/
private theorem beven_factor (m n b : ℤ) (hcopmn : IsCoprime m n) (hb2 : b ^ 2 = 2 * m * n)
    (hb : b ≠ 0) (hmev : (2 : ℤ) ∣ m) :
    ∃ k0 n0 : ℤ, m ^ 2 = 4 * k0 ^ 4 ∧ n ^ 2 = n0 ^ 4 ∧ IsCoprime k0 n0 ∧ Odd (n0 ^ 2) := by
  obtain ⟨k, rfl⟩ := hmev
  have hkn : IsCoprime k n := hcopmn.of_isCoprime_of_dvd_left ⟨2, by ring⟩
  have hnodd : ¬ (2 : ℤ) ∣ n := by
    intro h2n
    have hu : IsUnit (2 : ℤ) := hcopmn.isUnit_of_dvd' ⟨k, by ring⟩ h2n
    rcases Int.isUnit_iff.mp hu with h | h <;> norm_num at h
  have hbev : (2 : ℤ) ∣ b := by
    have he : Even (b ^ 2) := ⟨2 * k * n, by rw [hb2]; ring⟩
    rcases Int.even_or_odd b with h | h
    · exact h.two_dvd
    · exact absurd he (by simpa [parity_simps] using h)
  obtain ⟨b', rfl⟩ := hbev
  have hkn2 : k * n = b' ^ 2 := by nlinarith [hb2]
  obtain ⟨k0, hk0⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hkn) hkn2
  obtain ⟨n0, hn0⟩ := Int.sq_of_gcd_eq_one (Int.isCoprime_iff_gcd_eq_one.mp hkn.symm)
    (by rw [mul_comm]; exact hkn2)
  have hmsq : (2 * k) ^ 2 = 4 * k0 ^ 4 := by rcases hk0 with h | h <;> rw [h] <;> ring
  have hnsq : n ^ 2 = n0 ^ 4 := by rcases hn0 with h | h <;> rw [h] <;> ring
  refine ⟨k0, n0, hmsq, hnsq, ?_, ?_⟩
  · have hcop2 : IsCoprime (k0 ^ 2) (n0 ^ 2) := by
      rcases hk0 with h | h <;> rcases hn0 with h' | h' <;> rw [h, h'] at hkn <;>
        simpa [IsCoprime.neg_left_iff, IsCoprime.neg_right_iff] using hkn
    exact (IsCoprime.pow_right_iff (by norm_num)).mp ((IsCoprime.pow_left_iff (by norm_num)).mp hcop2)
  · have h2 : ¬ (2 : ℤ) ∣ n0 ^ 2 := by
      rcases hn0 with h | h
      · rw [← h]; exact hnodd
      · rw [show n0 ^ 2 = -n by rw [h]; ring]; rwa [dvd_neg]
    rw [Int.odd_iff]; omega

/-- The `b`-even second-level descent: from `a² = n0⁴ + 4k0⁴` re-classify down to
`u⁴ = v⁴ + n0²`, a strictly smaller instance, closed by the induction hypothesis. -/
private theorem beven_step (N : ℕ) (a k0 n0 : ℤ) (hN : a.natAbs = N) (ha : a ≠ 0) (hk00 : k0 ≠ 0)
    (hcop : IsCoprime k0 n0) (hodd : Odd (n0 ^ 2)) (ha2 : a ^ 2 = n0 ^ 4 + 4 * k0 ^ 4)
    (ih : ∀ M, M < N → ∀ (u v w : ℤ), u.natAbs = M → IsCoprime u v → v ≠ 0 → w ≠ 0 →
      u ^ 4 ≠ v ^ 4 + w ^ 2) : False := by
  have hn0 : n0 ≠ 0 := by rintro rfl; simp at hodd
  have hn2pos : 0 < n0 ^ 2 := by rcases lt_or_gt_of_ne hn0 with h | h <;> nlinarith
  have hnd : ¬ (2 : ℤ) ∣ n0 ^ 2 := (Int.two_dvd_ne_zero).mpr (Int.odd_iff.mp hodd)
  have hpt : PythagoreanTriple (n0 ^ 2) (2 * k0 ^ 2) a := by
    show n0 ^ 2 * n0 ^ 2 + 2 * k0 ^ 2 * (2 * k0 ^ 2) = a * a; nlinarith [ha2]
  have hcop_leg : IsCoprime (n0 ^ 2) (2 * k0 ^ 2) := by
    have h2 : IsCoprime (n0 ^ 2) 2 := ((Int.prime_two.coprime_iff_not_dvd).mpr hnd).symm
    exact h2.mul_right ((hcop.symm.pow_left).pow_right)
  have hgcd : (n0 ^ 2).gcd (2 * k0 ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop_leg
  obtain ⟨P, Q, hleg, hhyp, hPQ, _⟩ := PythagoreanTriple.coprime_classification.mp ⟨hpt, hgcd⟩
  have hcase : n0 ^ 2 = P ^ 2 - Q ^ 2 ∧ 2 * k0 ^ 2 = 2 * P * Q := by
    rcases hleg with h | h
    · exact h
    · exfalso; obtain ⟨he, _⟩ := h; exact hnd ⟨P * Q, by rw [he]; ring⟩
  obtain ⟨hn2, hk2⟩ := hcase
  have hPQprod : P * Q = k0 ^ 2 := by linarith [hk2]
  obtain ⟨u, hu⟩ := Int.sq_of_gcd_eq_one hPQ hPQprod
  obtain ⟨v, hv⟩ := Int.sq_of_gcd_eq_one (by rw [Int.gcd_comm]; exact hPQ)
    (by rw [mul_comm]; exact hPQprod)
  have hP2 : P ^ 2 = u ^ 4 := by rcases hu with h | h <;> rw [h] <;> ring
  have hQ2 : Q ^ 2 = v ^ 4 := by rcases hv with h | h <;> rw [h] <;> ring
  have hkey : u ^ 4 = v ^ 4 + n0 ^ 2 := by rw [← hP2, ← hQ2]; linarith [hn2]
  have hcopuv : IsCoprime u v := by
    have hc : IsCoprime (P ^ 2) (Q ^ 2) := ((Int.isCoprime_iff_gcd_eq_one.mpr hPQ).pow_left).pow_right
    rw [hP2, hQ2] at hc
    exact (IsCoprime.pow_right_iff (by norm_num)).mp ((IsCoprime.pow_left_iff (by norm_num)).mp hc)
  have hv0 : v ≠ 0 := by
    rintro rfl; apply hk00
    have hQ0 : Q = 0 := by
      have hqz : Q ^ 2 = 0 := by rw [hQ2]; ring
      exact pow_eq_zero_iff (by norm_num) |>.mp hqz
    have hkz : k0 ^ 2 = 0 := by rw [← hPQprod, hQ0]; ring
    exact pow_eq_zero_iff (by norm_num) |>.mp hkz
  have hu0 : u ≠ 0 := by rintro rfl; nlinarith [sq_nonneg (v ^ 2), hn2pos, hkey]
  have hu2 : 1 ≤ u ^ 2 := by
    have h1 : 0 ≤ u ^ 2 := sq_nonneg u
    have h2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0
    omega
  have hv4 : 1 ≤ v ^ 4 := by
    have h1 : 0 ≤ v ^ 4 := by positivity
    have h2 : v ^ 4 ≠ 0 := pow_ne_zero 4 hv0
    omega
  have hml : u.natAbs < N := by
    rw [← hN]
    have haval : a ^ 2 = (u ^ 4 + v ^ 4) ^ 2 := by
      rcases hhyp with h | h <;> rw [h] <;> rw [← hP2, ← hQ2] <;> ring
    have hlt : u ^ 2 < a ^ 2 := by
      rw [haval]
      have h4 : u ^ 2 ≤ u ^ 4 := by nlinarith [hu2, sq_nonneg (u ^ 2 - 1)]
      nlinarith [h4, hv4, sq_nonneg (u ^ 4 + v ^ 4 - 1)]
    have e1 : ((u.natAbs : ℤ)) ^ 2 = u ^ 2 := by rw [← Int.abs_eq_natAbs]; exact sq_abs u
    have e2 : ((a.natAbs : ℤ)) ^ 2 = a ^ 2 := by rw [← Int.abs_eq_natAbs]; exact sq_abs a
    have h1 : u.natAbs ^ 2 < a.natAbs ^ 2 := by
      have : ((u.natAbs : ℤ)) ^ 2 < ((a.natAbs : ℤ)) ^ 2 := by rw [e1, e2]; exact hlt
      exact_mod_cast this
    by_contra hcon; exact absurd h1 (not_lt.mpr (Nat.pow_le_pow_left (not_lt.mp hcon) 2))
  exact ih u.natAbs hml u v n0 rfl hcopuv hv0 hn0 hkey

/-- **Fermat's `x⁴ − y⁴ ≠ z²` (coprime core).** No nonzero `b, c` with
`IsCoprime a b` satisfy `a⁴ = b⁴ + c²`, by infinite descent on `a.natAbs`.
Companion to Mathlib's `not_fermat_42`. -/
theorem not_fermat_sub_coprime :
    ∀ (a b c : ℤ), IsCoprime a b → b ≠ 0 → c ≠ 0 → a ^ 4 ≠ b ^ 4 + c ^ 2 := by
  suffices H : ∀ (N : ℕ) (a b c : ℤ), a.natAbs = N → IsCoprime a b → b ≠ 0 → c ≠ 0 →
      a ^ 4 ≠ b ^ 4 + c ^ 2 by
    intro a b c; exact H a.natAbs a b c rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b c hN hcop hb hc heq
    have ha : a ≠ 0 := by
      rintro rfl; apply hb
      have hb4 : b ^ 4 ≤ 0 := by nlinarith [sq_nonneg c]
      exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm hb4 (by positivity))
    have hbc : IsCoprime b c := by
      have h1 : IsCoprime b (a ^ 4) := hcop.symm.pow_right
      have h2 : IsCoprime b (c ^ 2) := by
        have hce : c ^ 2 = a ^ 4 + b * (-b ^ 3) := by linear_combination -heq
        rw [hce]; exact h1.add_mul_left_right (-b ^ 3)
      exact (IsCoprime.pow_right_iff (by norm_num)).mp h2
    have hpt : PythagoreanTriple (b ^ 2) c (a ^ 2) := by
      show b ^ 2 * b ^ 2 + c * c = a ^ 2 * a ^ 2; nlinarith [heq]
    have hgcd : (b ^ 2).gcd c = 1 := Int.isCoprime_iff_gcd_eq_one.mp hbc.pow_left
    obtain ⟨m, n, hleg, hhyp, hmn, hpar⟩ :=
      PythagoreanTriple.coprime_classification.mp ⟨hpt, hgcd⟩
    have ha2pos : 0 < a ^ 2 := by rcases lt_or_gt_of_ne ha with h | h <;> nlinarith
    have ha2 : a ^ 2 = m ^ 2 + n ^ 2 := by
      rcases hhyp with h | h
      · exact h
      · exfalso; nlinarith [sq_nonneg m, sq_nonneg n, h, ha2pos]
    have hcopmn : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn
    rcases hleg with ⟨hb2, hc2⟩ | ⟨hb2, hc2⟩
    · have hn0 : n ≠ 0 := by rintro rfl; simp at hc2; exact hc hc2
      have hkey : m ^ 4 = n ^ 4 + (a * b) ^ 2 := by
        have h : (a * b) ^ 2 = (m ^ 2 + n ^ 2) * (m ^ 2 - n ^ 2) := by rw [mul_pow, ← ha2, ← hb2]
        rw [h]; ring
      have hml : m.natAbs < N := by
        rw [← hN]
        have hn2 : 0 < n ^ 2 := by rcases lt_or_gt_of_ne hn0 with h | h <;> nlinarith
        have hlt : m ^ 2 < a ^ 2 := by nlinarith [hn2, ha2]
        have e1 : ((m.natAbs : ℤ)) ^ 2 = m ^ 2 := by rw [← Int.abs_eq_natAbs]; exact sq_abs m
        have e2 : ((a.natAbs : ℤ)) ^ 2 = a ^ 2 := by rw [← Int.abs_eq_natAbs]; exact sq_abs a
        have h1 : m.natAbs ^ 2 < a.natAbs ^ 2 := by
          have : ((m.natAbs : ℤ)) ^ 2 < ((a.natAbs : ℤ)) ^ 2 := by rw [e1, e2]; exact hlt
          exact_mod_cast this
        by_contra hcon
        exact absurd h1 (not_lt.mpr (Nat.pow_le_pow_left (not_lt.mp hcon) 2))
      exact ih m.natAbs hml m n (a * b) rfl hcopmn hn0 (mul_ne_zero ha hb) hkey
    · have hbb : b ^ 2 = 2 * m * n := by rw [hb2]
      have hn0 : n ≠ 0 := by
        rintro rfl; apply hb
        have : b ^ 2 = 0 := by rw [hbb]; ring
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      have hm0 : m ≠ 0 := by
        rintro rfl; apply hb
        have : b ^ 2 = 0 := by rw [hbb]; ring
        exact pow_eq_zero_iff (by norm_num) |>.mp this
      rcases hpar with ⟨hme, _⟩ | ⟨_, hne⟩
      · obtain ⟨k0, n0, hmsq, hnsq, hcopk, hoddn⟩ := beven_factor m n b hcopmn hbb hb (by omega)
        have hk00 : k0 ≠ 0 := by
          rintro rfl; apply hm0
          have : m ^ 2 = 0 := by rw [hmsq]; ring
          exact pow_eq_zero_iff (by norm_num) |>.mp this
        have ha2' : a ^ 2 = n0 ^ 4 + 4 * k0 ^ 4 := by rw [ha2]; linear_combination hmsq + hnsq
        exact beven_step N a k0 n0 hN ha hk00 hcopk hoddn ha2' ih
      · obtain ⟨k0, m0, hnsq, hmsq, hcopk, hoddm⟩ :=
          beven_factor n m b hcopmn.symm (by rw [hbb]; ring) hb (by omega)
        have hk00 : k0 ≠ 0 := by
          rintro rfl; apply hn0
          have : n ^ 2 = 0 := by rw [hnsq]; ring
          exact pow_eq_zero_iff (by norm_num) |>.mp this
        have ha2' : a ^ 2 = m0 ^ 4 + 4 * k0 ^ 4 := by rw [ha2]; linear_combination hmsq + hnsq
        exact beven_step N a k0 m0 hN ha hk00 hcopk hoddm ha2' ih

/-- **Fermat's `x⁴ − y⁴ ≠ z²` (general form).** If `x⁴ − y⁴ = z²` then `y = 0` or
`z = 0` (Conrad, *Proofs by Descent*, Cor. 3.14). Reduces to the coprime core by
dividing out `gcd x y`. -/
theorem sq_ne_fourth_sub_fourth (x y z : ℤ) (h : x ^ 4 - y ^ 4 = z ^ 2) :
    y = 0 ∨ z = 0 := by
  rcases eq_or_ne y 0 with hy | hy
  · exact Or.inl hy
  right
  by_contra hz
  have hx : x ≠ 0 := by
    rintro rfl
    apply hy
    norm_num at h
    have hy4 : y ^ 4 = 0 := by nlinarith [sq_nonneg z, sq_nonneg (y ^ 2), h]
    exact pow_eq_zero_iff (by norm_num) |>.mp hy4
  set d : ℕ := Int.gcd x y with hd
  have hd0 : d ≠ 0 := by simp only [hd, Ne, Int.gcd_eq_zero_iff]; tauto
  obtain ⟨x', hx'⟩ : (d : ℤ) ∣ x := Int.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ : (d : ℤ) ∣ y := Int.gcd_dvd_right x y
  have hcop : IsCoprime x' y' := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : d = d * Int.gcd x' y' := by
      conv_lhs => rw [hd, hx', hy']
      rw [Int.gcd_mul_left]; simp
    have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) (by omega : d * 1 = d * Int.gcd x' y')
    omega
  have hy'0 : y' ≠ 0 := by rintro rfl; exact hy (by rw [hy', mul_zero])
  have hfac : (d : ℤ) ^ 4 * (x' ^ 4 - y' ^ 4) = z ^ 2 := by rw [← h, hx', hy']; ring
  have hg2z : (d : ℤ) ^ 2 ∣ z := by
    have hdvd : ((d : ℤ) ^ 2) ^ 2 ∣ z ^ 2 := ⟨x' ^ 4 - y' ^ 4, by rw [← hfac]; ring⟩
    exact (pow_dvd_pow_iff (two_ne_zero)).mp hdvd
  obtain ⟨w, hw⟩ := hg2z
  have hdpos : (0 : ℤ) < (d : ℤ) ^ 4 := by positivity
  have hw2 : x' ^ 4 - y' ^ 4 = w ^ 2 := by
    have : (d : ℤ) ^ 4 * (x' ^ 4 - y' ^ 4) = (d : ℤ) ^ 4 * w ^ 2 := by rw [hfac, hw]; ring
    exact mul_left_cancel₀ hdpos.ne' this
  have hw0 : w ≠ 0 := by rintro rfl; rw [mul_zero] at hw; exact hz hw
  exact not_fermat_sub_coprime x' y' w hcop hy'0 hw0 (by linarith [hw2])

end Int
