import Erdos647_ConcreteDenominatorLower
import Erdos647_ConcreteR20Density

/-!
# Erdős #647 — concrete `X / (log z)^7` inequality

This eliminates the existential Selberg denominator from the fully
instantiated `R = (2z)^20` theorem using the concrete seventh-power lower
bound.
-/

namespace Erdos647

theorem concrete_R20_log_density
    (X z : ℕ) (hz : 11 ≤ z) :
    ((boundedCandidates X).card : ℝ) ≤
      60 +
        2 * ((77 : ℝ) / 16) ^ 7 * ((X / 2520 : ℕ) : ℝ) /
          (Real.log (z : ℝ)) ^ 7 +
        (((((2 * z) ^ 20) * ((2 * z) ^ 20) + 1 : ℕ) : ℝ) ^ 8) + z := by
  obtain ⟨t, hprod, hnu, hcard⟩ :=
    exists_concrete_R20_candidate_density X z (by omega)
  have hden := concrete_selberg_denominator_lower t z hz hprod hnu
  let L : ℝ := ∑ l ∈ t.prodPrimes.divisors, t.selbergTerms l
  let D : ℝ := (Real.log (z : ℝ)) ^ 7
  let c : ℝ := ((16 : ℝ) / 77) ^ 7
  let M : ℝ := ((X / 2520 : ℕ) : ℝ)
  have hlog : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hL : 0 < L := by
    have : c * D ≤ L := by simpa [c, D, L] using hden
    exact (mul_pos hc hD).trans_le this
  have hinv : L⁻¹ ≤ (c * D)⁻¹ :=
    inv_anti₀ (mul_pos hc hD) (by simpa [c, D, L] using hden)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hmain :
      2 * M / L ≤ 2 * ((77 : ℝ) / 16) ^ 7 * M / D := by
    calc
      2 * M / L = (2 * M) * L⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (2 * M) * (c * D)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * ((77 : ℝ) / 16) ^ 7 * M / D := by
        dsimp [c]
        field_simp
        <;> ring
  have hcard' :
      ((boundedCandidates X).card : ℝ) ≤
        60 + 2 * M / L +
          (((((2 * z) ^ 20) * ((2 * z) ^ 20) + 1 : ℕ) : ℝ) ^ 8) + z := by
    simpa [M, L] using hcard
  dsimp [M, D] at hmain
  linarith

end Erdos647
