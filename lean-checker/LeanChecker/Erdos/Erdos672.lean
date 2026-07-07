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

/-! ## Crux obligation (M3) — Fermat's `x⁴ − y⁴ ≠ z²`

Not in Mathlib. To be proved by infinite descent on
`PythagoreanTriple.coprime_classification`. This is the hard, multi-session part
of the marathon. -/

/-- **CRUX (open).** No positive integers with `x⁴ = y⁴ + z²`; equivalently
`x⁴ − y⁴` is never a nonzero square. Fermat's "right triangle with square area"
theorem. -/
theorem noFourthPowerDiffSq (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hxy : x.Coprime y) :
    x ^ 4 ≠ y ^ 4 + z ^ 2 := by
  sorry

/-! ## Arithmetic core (M4) — depends on the crux -/

/-- **Euler's theorem (arithmetic core, open).** The product of a 4-term AP with
`gcd(n,d)=1` is never a perfect square. -/
theorem euler_four_ap (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hnd : n.Coprime d)
    (q : ℕ) : n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  sorry

end Erdos672
