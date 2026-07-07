import Mathlib

/-!
# Erdős Problem #672 (Euler) — MARATHON IN PROGRESS

**Target (corpus `research solved`, shipped `sorry`):** the product of a 4-term
arithmetic progression `n, n+d, n+2d, n+3d` with `gcd(n,d)=1` is never a perfect
square (Euler). This is a genuine Fermat-**descent** theorem being built over
multiple sessions — see `ErdosProblems/erdos-672/attack-plan.md`.

This file is the working artifact. The kernel-verified foundations (backbone
identities, gcd facts) are complete; the **crux** `noFourthPowerDiffSq`
(Fermat's `x⁴ − y⁴ ≠ z²`, not in Mathlib) and the top-level `euler_four_ap` that
depends on it are the remaining obligations, marked `sorry`.

## Status
- ☑ backbone identities, gcd foundations (below)
- ☐ M3 crux: `noFourthPowerDiffSq` (Fermat descent via Pythagorean triples)
- ☐ M4 reduction: `euler_four_ap` from the crux + case analysis
- ☐ M1 bridge to the corpus `Erdos672With 4 2` shape
-/

namespace Erdos672

/-! ## Backbone identities (kernel-verified) -/

/-- `P = A · B` with `A = n(n+3d)`, `B = (n+d)(n+2d)`. -/
theorem prod_eq_AB (n d : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) = (n * (n + 3 * d)) * ((n + d) * (n + 2 * d)) := by
  ring

/-- `B = A + 2d²`. -/
theorem B_eq_A_add (n d : ℕ) :
    (n + d) * (n + 2 * d) = n * (n + 3 * d) + 2 * d ^ 2 := by ring

/-- The square-sandwich backbone: `P + d⁴ = (n²+3nd+d²)²`, i.e. `P = X² − d⁴`. -/
theorem prod_add_pow_four (n d : ℕ) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) + d ^ 4 = (n ^ 2 + 3 * n * d + d ^ 2) ^ 2 := by
  ring

/-! ## gcd foundations (kernel-verified) -/

/-- `gcd(n,d)=1 ⟹ gcd(n(n+3d), d) = 1` (since `n(n+3d) ≡ n² (mod d)`). -/
theorem coprime_A_d {n d : ℕ} (hnd : n.Coprime d) : (n * (n + 3 * d)).Coprime d := by
  refine Nat.Coprime.mul hnd ?_
  -- Coprime (n + 3*d) d  ↔  Coprime n d
  have : (n + 3 * d).Coprime d ↔ n.Coprime d := by
    rw [Nat.coprime_comm, Nat.coprime_add_mul_right_right d n 3, Nat.coprime_comm]
  exact this.mpr hnd

/-- `gcd(n,d)=1 ⟹ gcd(A, B) ∣ 2` where `A = n(n+3d)`, `B = (n+d)(n+2d) = A + 2d²`. -/
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

/-! ## Crux (M3) — Fermat's `x⁴ − y⁴ ≠ z²`, by infinite descent

Not in Mathlib; built here on `PythagoreanTriple.coprime_classification`. The
`b`-odd descent case (`a²b² = (m²+n²)(m²−n²) = m⁴−n⁴`, a strictly smaller
instance) is **kernel-verified**; the `b`-even case (a second-level
double-classification descent) is the remaining `sorry`. -/

/-- **CRUX.** No nonzero `b, c` (with `IsCoprime a b`) satisfy `a⁴ = b⁴ + c²` —
Fermat's "right triangle with square area" theorem, by infinite descent on
`a.natAbs`. `b`-odd case done; `b`-even case remaining. -/
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
    obtain ⟨m, n, hleg, hhyp, hmn, _hpar⟩ :=
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
        have h : (a * b) ^ 2 = (m ^ 2 + n ^ 2) * (m ^ 2 - n ^ 2) := by
          rw [mul_pow, ← ha2, ← hb2]
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
    · -- b even: b² = 2mn, c = m²−n². Second-level double-classification descent.
      sorry

/-! ## Arithmetic core (M4) — depends on the crux -/

/-- **Euler's theorem (arithmetic core, open).** The product of a 4-term AP with
`gcd(n,d)=1` is never a perfect square. -/
theorem euler_four_ap (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hnd : n.Coprime d)
    (q : ℕ) : n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  sorry

end Erdos672
