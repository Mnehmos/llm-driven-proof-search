import Mathlib

/-!
# Erdős #647 — cofactor gap rigidity

Two elementary arithmetic facts used by the second-layer cofactor analysis.
Common divisors of cofactors from two shifted values divide the gap between
the shifts.  If the two cofactors are actually equal and their complementary
factors are odd primes, parity doubles that divisibility: `2 * q` divides the
shift gap.

These are structural constraints, not an exclusion theorem by themselves.

Tracked proof-search verification (2026-07-16):

* `erdos647_gcd_cofactors_dvd_gap`:
  preverification `376e0187-283d-434e-8fd6-a9dd8fb3561d`,
  problem `60af9a3d-4c6a-4637-994d-c0c2b4822ae0`,
  episode `1611cd40-d0d3-4631-9c8d-4b5c82f52e82`,
  root hash `eeedba505324fa39989e7a563ac8899a44fad410c8bacd6ac540cffd0bc4071b`;
* `erdos647_repeated_odd_prime_cofactor_small`:
  preverification `e177b81c-ae5e-4b3f-a519-7424120e8e96`,
  problem `e9b2f6ae-f1ed-420c-a0de-4499a83bbe2b`,
  episode `15d19ef3-0de0-49a0-ab99-51b00d024fd1`,
  root hash `105e08a48b0ffb95212809baa65f2c31bb6dfaf348a5a4472675b86dedf9036a`.

Both tracked outcomes are `kernel_verified` with `root_proved` termination.
-/

/-- Common divisors of two shifted cofactors divide the distance between the
shifts.  No primality or positivity assumption on the cofactors is needed. -/
theorem erdos647_gcd_cofactors_dvd_gap :
    ∀ {n k l q₁ q₂ : ℕ},
      k ≤ l → l ≤ n →
      q₁ ∣ n - k → q₂ ∣ n - l →
      Nat.gcd q₁ q₂ ∣ l - k := by
  intro n k l q₁ q₂ hkl hln hq₁ hq₂
  have hg₁ : Nat.gcd q₁ q₂ ∣ n - k :=
    (Nat.gcd_dvd_left q₁ q₂).trans hq₁
  have hg₂ : Nat.gcd q₁ q₂ ∣ n - l :=
    (Nat.gcd_dvd_right q₁ q₂).trans hq₂
  have hgap : (n - k) - (n - l) = l - k := by omega
  have hdvd := Nat.dvd_sub hg₁ hg₂
  rwa [hgap] at hdvd

/-- Equal positive cofactors attached to two different shifts, with odd
complementary factors, force twice the cofactor to divide the shift gap. -/
theorem erdos647_repeated_odd_cofactor_dvd_gap :
    ∀ {n k l p r q : ℕ},
      0 < q → k < l →
      Odd p → Odd r →
      n - k = p * q → n - l = r * q →
      2 * q ∣ l - k := by
  intro n k l p r q hq hkl hpOdd hrOdd hkfac hlfac
  obtain ⟨a, ha⟩ := hpOdd
  obtain ⟨b, hb⟩ := hrOdd
  have hrpos : 0 < r := by omega
  have hnlpos : 0 < n - l := by
    rw [hlfac]
    exact Nat.mul_pos hrpos hq
  have hln : l < n := Nat.sub_pos_iff_lt.mp hnlpos
  have hshiftlt : n - l < n - k := by omega
  have hprodlt : r * q < p * q := by
    rw [← hlfac, ← hkfac]
    exact hshiftlt
  have hrp : r < p := Nat.lt_of_mul_lt_mul_right hprodlt
  have heven : 2 ∣ p - r := by
    refine ⟨a - b, ?_⟩
    omega
  have hmul : 2 * q ∣ (p - r) * q :=
    Nat.mul_dvd_mul_right heven q
  have hgap : l - k = (p - r) * q := by
    calc
      l - k = (n - k) - (n - l) := by omega
      _ = p * q - r * q := by rw [hkfac, hlfac]
      _ = (p - r) * q := by rw [Nat.sub_mul]
  rwa [hgap]

/-- Prime-facing form used in the Erdős #647 block.  The hypotheses excluding
`2` are necessary: the conclusion is false for complementary primes of
opposite parity. -/
theorem erdos647_repeated_odd_prime_cofactor_small :
    ∀ {n k l p r q : ℕ},
      0 < q → k < l →
      p.Prime → r.Prime →
      p ≠ 2 → r ≠ 2 →
      n - k = p * q → n - l = r * q →
      2 * q ∣ l - k := by
  intro n k l p r q hq hkl hp hr hp2 hr2 hkfac hlfac
  exact erdos647_repeated_odd_cofactor_dvd_gap
    hq hkl (hp.odd_of_ne_two hp2) (hr.odd_of_ne_two hr2) hkfac hlfac
