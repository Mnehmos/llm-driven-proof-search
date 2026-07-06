import Mathlib

/-!
# Recurrence & generating-function kit (issue #90)

The DISCRETE generating-function and recurrence layer, complementary to the
analytic `PowerSeriesKit` (which handles coefficient uniqueness for
convergent real power series). This kit works with formal power series over a
commutative ring (`R⟦X⟧`) and closed forms of linear recurrences — the
combinatorial side of contest and Erdős-style sequence problems.

## Relationship to PowerSeriesKit

Kept separate on purpose: `PowerSeriesKit` is real-analytic (radius of
convergence, `HasFPowerSeriesAt`, `exp`/`cos` coefficients); this kit is
formal/discrete (`PowerSeries.mk`, coefficient comparison, integer/nat
sequences). A problem that mixes them can import both; neither depends on the
other.

## Target problem families

- Linear recurrences with a closed form via characteristic roots
  (`closed_form_satisfies_linrec`): Fibonacci/Lucas/Pell-recurrence style.
- Ordinary generating functions and coefficient comparison (`ogf_ext`) —
  "two OGFs are equal iff their coefficient sequences agree".
- Finite-sum ↔ generating-function bridges (`one_sub_X_mul_geom`, the
  telescoping `1/(1−X)` identity).
- Closed forms of geometric and geometric-like sums (`geom_sum_eq` reuse).

## Route notes

v1 supplies the reusable bridges and small fixtures. Deliberately out of
scope: rational-GF partial-fraction closed forms, Binet-type formulas over
`ℝ`, and multivariate GFs — scoped when a concrete target needs them.
-/

namespace LeanChecker.RecurrenceGeneratingFunctionKit

open PowerSeries

/-- **Characteristic-root bridge** (recurrence ← closed form): if `r` is a
root of the characteristic equation `x² = p·x + q`, then the closed form
`aₙ = rⁿ` satisfies the linear recurrence `a(n+2) = p·a(n+1) + q·a(n)`. One
`ring` step after substituting the root relation. -/
theorem closed_form_satisfies_linrec {R : Type*} [CommRing R] {r p q : R}
    (h : r ^ 2 = p * r + q) (n : ℕ) :
    r ^ (n + 2) = p * r ^ (n + 1) + q * r ^ n := by
  have hstep : r ^ (n + 2) = r ^ n * r ^ 2 := by ring
  rw [hstep, h]; ring

/-- **Coefficient comparison** for ordinary generating functions: two OGFs
built from sequences are equal iff the sequences agree pointwise. Repackages
`PowerSeries.ext` in the `mk`-of-sequence form coefficient arguments use. -/
theorem ogf_ext {R : Type*} [CommRing R] {f g : ℕ → R} (h : ∀ n, f n = g n) :
    (mk f : R⟦X⟧) = mk g := by
  ext n
  simp only [coeff_mk, h n]

/-- **Finite-sum → generating function** (telescoping): the OGF of the
all-ones sequence is `1/(1 − X)`, i.e. `(1 − X)·∑ Xⁿ = 1`. This is the
partial-sum bridge — multiplying an OGF by `(1 − X)` differences its
coefficients, and the all-ones sequence differences to the unit. -/
theorem one_sub_X_mul_geom {R : Type*} [CommRing R] :
    (1 - X) * (mk fun _ => (1 : R)) = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub]
  cases n with
  | zero =>
    have hX : coeff 0 (X * mk fun _ => (1 : R)) = 0 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul]
    rw [coeff_mk, hX, coeff_one]
    simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one]
    simp

/-! ## Fixtures -/

/-- Fixture (issue #90 acceptance — recurrence ↔ closed form): the powers of
`2` satisfy `a(n+2) = 3·a(n+1) − 2·a(n)` (characteristic roots `1, 2`),
derived from the closed-form bridge rather than induction. -/
example (n : ℕ) : (2 : ℤ) ^ (n + 2) = 3 * 2 ^ (n + 1) + (-2) * 2 ^ n :=
  closed_form_satisfies_linrec (by norm_num) n

/-- Fixture (linear recurrence, discrete side): the Fibonacci numbers satisfy
their defining recurrence — the anchor for characteristic-root closed-form
work. -/
example (n : ℕ) : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
  Nat.fib_add_two

/-- Fixture (issue #90 acceptance — generating-function coefficient
comparison): two OGFs whose coefficient sequences are equal by a ring
identity are the same power series. -/
example : (mk fun n => ((n : ℤ) + n)) = mk fun n => 2 * (n : ℤ) :=
  ogf_ext fun n => by ring

/-- Fixture (closed form of a geometric sum): the finite geometric series has
the standard closed form — the scalar identity behind rational OGFs. -/
example (x : ℝ) (h : x ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) :=
  geom_sum_eq h n

end LeanChecker.RecurrenceGeneratingFunctionKit
