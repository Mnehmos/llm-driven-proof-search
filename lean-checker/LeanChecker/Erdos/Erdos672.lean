import Mathlib

/-!
# Erdős Problem #672 (Euler) — MARATHON IN PROGRESS

**Target (corpus `research solved`, shipped `sorry`):** the product of a 4-term
arithmetic progression `n, n+d, n+2d, n+3d` with `gcd(n,d)=1` is never a perfect
square (Euler). A genuine Fermat-**descent** theorem — see
`ErdosProblems/erdos-672/attack-plan.md`.

## Status
- ☑ backbone identities, gcd foundations
- ☑ **M3 CRUX `no_fermat_sub` (Fermat's `x⁴ − y⁴ ≠ z²`) — FULLY PROVED**, both
  the `b`-odd and `b`-even descent cases, built from scratch on
  `PythagoreanTriple.coprime_classification` (this theorem is not in Mathlib).
- ☐ M4 reduction: `euler_four_ap` from the crux + case analysis (`sorry`)
- ☐ M1 bridge to the corpus `Erdos672With 4 2` shape
-/

namespace Erdos672

/-! ## Backbone identities (kernel-verified) -/

theorem prod_eq_AB (n d : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) = (n * (n + 3 * d)) * ((n + d) * (n + 2 * d)) := by
  ring

theorem B_eq_A_add (n d : ℕ) :
    (n + d) * (n + 2 * d) = n * (n + 3 * d) + 2 * d ^ 2 := by ring

theorem prod_add_pow_four (n d : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) + d ^ 4 = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 := by
  ring

/-! ## gcd foundations (kernel-verified) -/

theorem coprime_A_d {n d : ℕ} (hnd : n.Coprime d) : (n * (n + 3 * d)).Coprime d := by
  refine Nat.Coprime.mul hnd ?_
  have : (n + 3 * d).Coprime d ↔ n.Coprime d := by
    rw [Nat.coprime_comm, Nat.coprime_add_mul_right_right d n 3, Nat.coprime_comm]
  exact this.mpr hnd

theorem gcd_A_B_dvd_two {n d : ℕ} (hnd : n.Coprime d) :
    Nat.gcd (n * (n + 3 * d)) ((n + d) * (n + 2 * d)) ∣ 2 := by
  set A := n * (n + 3 * d) with hA
  set g := Nat.gcd A ((n + d) * (n + 2 * d)) with hg
  have hB : (n + d) * (n + 2 * d) = A + 2 * d ^ 2 := B_eq_A_add n d
  have hgA : g ∣ A := Nat.gcd_dvd_left _ _
  have hgB : g ∣ A + 2 * d ^ 2 := hB ▸ Nat.gcd_dvd_right _ _
  have hg2d2 : g ∣ 2 * d ^ 2 := (Nat.dvd_add_right hgA).mp hgB
  have hAd2 : A.Coprime (d ^ 2) := (coprime_A_d hnd).pow_right 2
  have hgcop : g.Coprime (d ^ 2) := Nat.Coprime.coprime_dvd_left hgA hAd2
  exact hgcop.dvd_of_dvd_mul_right hg2d2

/-! ## M3 CRUX — Fermat's `x⁴ − y⁴ ≠ z²`, by infinite descent (kernel-verified)

Built on `PythagoreanTriple.coprime_classification`. `beven_factor` extracts the
square structure from `2mn = b²`; `beven_step` performs the second-level
classification descent for the `b`-even case; `no_fermat_sub` is the full
theorem by strong induction on `a.natAbs`. -/

/-- From `2mn = b²` with `gcd(m,n)=1` and `m` even: `m² = 4k0⁴`, `n² = n0⁴` with
`gcd(k0,n0)=1` and `n0²` odd. -/
theorem beven_factor (m n b : ℤ) (hcopmn : IsCoprime m n) (hb2 : b ^ 2 = 2 * m * n) (hb : b ≠ 0)
    (hmev : (2 : ℤ) ∣ m) :
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

/-- The `b`-even second-level descent: from `a² = n0⁴ + 4k0⁴` (`k0 ≠ 0`,
`gcd(k0,n0)=1`, `n0²` odd) re-classify `(n0², 2k0², a)` down to `u⁴ = v⁴ + n0²`,
a strictly smaller instance, closed by the induction hypothesis. -/
theorem beven_step (N : ℕ) (a k0 n0 : ℤ) (hN : a.natAbs = N) (ha : a ≠ 0) (hk00 : k0 ≠ 0)
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

/-- **CRUX (kernel-verified).** No nonzero `b, c` with `IsCoprime a b` satisfy
`a⁴ = b⁴ + c²` — Fermat's "right triangle with square area" theorem (`x⁴−y⁴≠z²`),
by infinite descent on `a.natAbs`. -/
theorem no_fermat_sub :
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
    · -- b odd: b² = m²−n², c = 2mn  →  m⁴ = n⁴ + (ab)², a strictly smaller instance
      have hn0 : n ≠ 0 := by rintro rfl; simp at hc2; exact hc hc2
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
    · -- b even: b² = 2mn. Two parity sub-cases, each via beven_factor + beven_step.
      have hbb : b ^ 2 = 2 * m * n := by rw [hb2]
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

/-! ## Arithmetic core (M4) — depends on the (now-proved) crux -/

/-- **Euler's theorem (arithmetic core, M4 in progress).** The product of a
4-term AP with `gcd(n,d)=1` is never a perfect square. The reduction to the two
structural cases is kernel-verified; via the primitive Pythagorean triple
`(q, d², X)` with `X = n²+3nd+d²` (since `P + d⁴ = X²`), classification splits into
case (i) `d²=2MN` ⟹ `A=(M−N)²`, `B=(M+N)²` (both squares ⟹ four squares in AP),
and case (ii) `d²=M²−N²` ⟹ `A=2N²`, `B=2M²`. The two case-descents remain. -/
theorem euler_four_ap (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hnd : n.Coprime d)
    (q : ℕ) : n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  intro heqn
  have hnd' : IsCoprime (n : ℤ) (d : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd_natCast_natCast] using hnd
  have heq : (n : ℤ) * (n + d) * (n + 2 * d) * (n + 3 * d) = (q : ℤ) ^ 2 := by exact_mod_cast heqn
  set X := (n : ℤ) ^ 2 + 3 * n * d + d ^ 2 with hX
  have hpt : PythagoreanTriple (q : ℤ) ((d : ℤ) ^ 2) X := by
    show (q : ℤ) * q + (d : ℤ) ^ 2 * (d : ℤ) ^ 2 = X * X; rw [hX]; nlinarith [heq]
  have hqd : IsCoprime (q : ℤ) (d : ℤ) := by
    have hcop : IsCoprime ((q : ℤ) ^ 2) (d : ℤ) := by
      rw [← heq]
      have h1 : IsCoprime ((n : ℤ) + d) d := by simpa using IsCoprime.add_mul_right_left hnd' 1
      have h2 : IsCoprime ((n : ℤ) + 2 * d) d := by simpa using IsCoprime.add_mul_right_left hnd' 2
      have h3 : IsCoprime ((n : ℤ) + 3 * d) d := by simpa using IsCoprime.add_mul_right_left hnd' 3
      exact ((hnd'.mul_left h1).mul_left h2).mul_left h3
    exact (IsCoprime.pow_left_iff (by norm_num)).mp hcop
  have hqd2 : (q : ℤ).gcd ((d : ℤ) ^ 2) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hqd.pow_right
  obtain ⟨M, N, hleg, hhyp, hMN, hpar⟩ := PythagoreanTriple.coprime_classification.mp ⟨hpt, hqd2⟩
  have hXpos : 0 < X := by rw [hX]; positivity
  have hXval : X = M ^ 2 + N ^ 2 := by
    rcases hhyp with h | h
    · exact h
    · exfalso; nlinarith [sq_nonneg M, sq_nonneg N, h, hXpos]
  have hA : (n : ℤ) * (n + 3 * d) = X - (d : ℤ) ^ 2 := by rw [hX]; ring
  have hB : ((n : ℤ) + d) * (n + 2 * d) = X + (d : ℤ) ^ 2 := by rw [hX]; ring
  rcases hleg with ⟨hq2, hd2⟩ | ⟨hq2, hd2⟩
  · -- case (i): d² = 2MN ⟹ A = (M−N)², B = (M+N)²  (four squares in AP)
    have hAsq : (n : ℤ) * (n + 3 * d) = (M - N) ^ 2 := by rw [hA, hXval, hd2]; ring
    have hBsq : ((n : ℤ) + d) * (n + 2 * d) = (M + N) ^ 2 := by rw [hB, hXval, hd2]; ring
    sorry
  · -- case (ii): d² = M²−N² ⟹ A = 2N², B = 2M²
    have hA2 : (n : ℤ) * (n + 3 * d) = 2 * N ^ 2 := by rw [hA, hXval, hd2]; ring
    have hB2 : ((n : ℤ) + d) * (n + 2 * d) = 2 * M ^ 2 := by rw [hB, hXval, hd2]; ring
    sorry

end Erdos672
