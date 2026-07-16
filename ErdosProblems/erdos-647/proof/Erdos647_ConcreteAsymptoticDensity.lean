import Erdos647_ConcreteR20LogDensity
import Erdos647_DyadicErrorLogScale
import Erdos647_DyadicErrorRealLog
import Erdos647_DyadicParameterBracket
import Erdos647_ParameterErrorPolynomial

/-!
# Erdős #647 — explicit large-range density theorem

The dyadic bracket chooses `z = 2^k`.  The threshold `16^400 ≤ X` forces
`k ≥ 4`, hence `z ≥ 11`.  The main term, polynomial error, `+z`, and the
fixed initial `60` are all absorbed into one explicit multiple of
`X / (log X)^7`.
-/

namespace Erdos647

noncomputable def densityConstant : ℝ :=
  (2 * ((77 : ℝ) / 16) ^ 7 +
    3 * (2 : ℝ) ^ 328 * (Real.log 2) ^ 7) * 800 ^ 7

theorem boundedCandidates_density_large
    (X : ℕ) (hX : 16 ^ 400 ≤ X) :
    ((boundedCandidates X).card : ℝ) ≤
      densityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7 := by
  have hXne : X ≠ 0 := by
    intro h
    subst X
    norm_num at hX
  obtain ⟨k, hkLower, hkUpper⟩ :=
    erdos647_dyadic_parameter_bracket X hXne
  have hk4 : 4 ≤ k := by
    by_contra hnot
    have hk3 : k ≤ 3 := by omega
    have hbase : 2 * 2 ^ k ≤ 16 := by
      interval_cases k <;> norm_num
    have hpowle : (2 * 2 ^ k) ^ 400 ≤ 16 ^ 400 :=
      pow_le_pow_left' hbase 400
    exact (not_lt_of_ge hX) (hkUpper.trans_le hpowle)
  have hkpos : 0 < k := by omega
  let z : ℕ := 2 ^ k
  have hz11 : 11 ≤ z := by
    dsimp [z]
    calc
      11 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right' (by norm_num) hk4
  have hz1 : 1 ≤ z := by omega
  let E : ℕ := (((2 * z) ^ 20) * ((2 * z) ^ 20) + 1) ^ 8
  have hE : E ≤ 2 ^ 328 * z ^ 320 := by
    dsimp [E]
    simpa [pow_two] using erdos647_parameter_error_polynomial z hz1
  have hkLower' : z ^ 400 ≤ X := by simpa [z] using hkLower
  have hEscale : E * k ^ 7 ≤ 2 ^ 328 * X :=
    erdos647_dyadic_error_log_scale k X E hkLower' hE
  have hzBound : z ≤ 2 ^ 328 * z ^ 320 := by
    have hzpow : z ^ 1 ≤ z ^ 320 :=
      pow_le_pow_right' hz1 (by norm_num)
    have hconst : 1 ≤ 2 ^ 328 := one_le_pow₀ (by norm_num)
    calc
      z = z ^ 1 := by simp
      _ ≤ z ^ 320 := hzpow
      _ = 1 * z ^ 320 := by simp
      _ ≤ 2 ^ 328 * z ^ 320 := Nat.mul_le_mul_right _ hconst
  have hzScale : z * k ^ 7 ≤ 2 ^ 328 * X :=
    erdos647_dyadic_error_log_scale k X z hkLower' hzBound
  have h60Bound : 60 ≤ 2 ^ 328 * z ^ 320 := by
    have hzpow : 1 ≤ z ^ 320 := one_le_pow₀ hz1
    have h60 : 60 ≤ 2 ^ 328 := by
      calc
        60 ≤ 2 ^ 8 := by norm_num
        _ ≤ 2 ^ 328 := pow_le_pow_right' (by norm_num) (by norm_num)
    calc
      60 ≤ 2 ^ 328 := h60
      _ = 2 ^ 328 * 1 := by simp
      _ ≤ 2 ^ 328 * z ^ 320 := Nat.mul_le_mul_left _ hzpow
  have h60Scale : 60 * k ^ 7 ≤ 2 ^ 328 * X :=
    erdos647_dyadic_error_log_scale k X 60 hkLower' h60Bound
  have hEreal := erdos647_dyadic_error_real_log k X E hkpos hEscale
  have hzreal := erdos647_dyadic_error_real_log k X z hkpos hzScale
  have h60real := erdos647_dyadic_error_real_log k X 60 hkpos h60Scale
  have hdensity := concrete_R20_log_density X z hz11
  have hmass : ((X / 2520 : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast Nat.div_le_self X 2520
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hD : 0 < (Real.log (z : ℝ)) ^ 7 := by positivity
  have hmain :
      2 * ((77 : ℝ) / 16) ^ 7 * ((X / 2520 : ℕ) : ℝ) /
          (Real.log (z : ℝ)) ^ 7 ≤
        2 * ((77 : ℝ) / 16) ^ 7 * (X : ℝ) /
          (Real.log (z : ℝ)) ^ 7 := by
    gcongr
  have hlogzpow :
      Real.log (((2 ^ k : ℕ) : ℝ)) = Real.log (z : ℝ) := by
    simp [z]
  rw [hlogzpow] at hEreal hzreal h60real
  let Q : ℝ :=
    ((2 : ℝ) ^ 328 * (Real.log 2) ^ 7 * (X : ℝ)) /
      (Real.log (z : ℝ)) ^ 7
  have hEreal' : (E : ℝ) ≤ Q := by
    simpa [Q] using hEreal
  have hzreal' : (z : ℝ) ≤ Q := by
    simpa [Q] using hzreal
  have h60real' : (60 : ℝ) ≤ Q := by
    norm_num at h60real ⊢
    simpa [Q] using h60real
  have hdensity' :
      ((boundedCandidates X).card : ℝ) ≤
        60 +
          2 * ((77 : ℝ) / 16) ^ 7 * ((X / 2520 : ℕ) : ℝ) /
            (Real.log (z : ℝ)) ^ 7 + (E : ℝ) + z := by
    simpa [E] using hdensity
  have hZbound :
      ((boundedCandidates X).card : ℝ) ≤
        (2 * ((77 : ℝ) / 16) ^ 7 +
          3 * (2 : ℝ) ^ 328 * (Real.log 2) ^ 7) *
            (X : ℝ) / (Real.log (z : ℝ)) ^ 7 := by
    calc
      ((boundedCandidates X).card : ℝ) ≤
          60 +
            2 * ((77 : ℝ) / 16) ^ 7 * ((X / 2520 : ℕ) : ℝ) /
              (Real.log (z : ℝ)) ^ 7 + (E : ℝ) + z := hdensity'
      _ ≤ 2 * ((77 : ℝ) / 16) ^ 7 * (X : ℝ) /
            (Real.log (z : ℝ)) ^ 7 + 3 * Q := by
        linarith
      _ = (2 * ((77 : ℝ) / 16) ^ 7 +
          3 * (2 : ℝ) ^ 328 * (Real.log 2) ^ 7) *
            (X : ℝ) / (Real.log (z : ℝ)) ^ 7 := by
        dsimp [Q]
        ring
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hXne
  have hzpos : 0 < (z : ℝ) := by exact_mod_cast (show 0 < z by omega)
  have hcastUpper : (X : ℝ) ≤ (((2 * z) ^ 400 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_of_lt (by simpa [z] using hkUpper))
  have hlogUpper0 :
      Real.log (X : ℝ) ≤ Real.log ((((2 * z) ^ 400 : ℕ) : ℝ)) :=
    Real.log_le_log hXpos hcastUpper
  have hlog2le : Real.log 2 ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ z by omega))
  have hlogUpper : Real.log (X : ℝ) ≤ 800 * Real.log (z : ℝ) := by
    calc
      Real.log (X : ℝ) ≤ Real.log ((((2 * z) ^ 400 : ℕ) : ℝ)) := hlogUpper0
      _ = 400 * (Real.log 2 + Real.log (z : ℝ)) := by
        rw [Nat.cast_pow, Nat.cast_mul, Real.log_pow,
          Real.log_mul (by norm_num) (ne_of_gt hzpos)]
        norm_num
      _ ≤ 800 * Real.log (z : ℝ) := by nlinarith
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hDX : 0 < (Real.log (X : ℝ)) ^ 7 := by positivity
  have hpowLog :
      (Real.log (X : ℝ)) ^ 7 ≤
        (800 : ℝ) ^ 7 * (Real.log (z : ℝ)) ^ 7 := by
    calc
      (Real.log (X : ℝ)) ^ 7 ≤
          (800 * Real.log (z : ℝ)) ^ 7 :=
        pow_le_pow_left₀ (le_of_lt hlogX) hlogUpper 7
      _ = (800 : ℝ) ^ 7 * (Real.log (z : ℝ)) ^ 7 := by ring
  have hrecip :
      ((Real.log (z : ℝ)) ^ 7)⁻¹ ≤
        (800 : ℝ) ^ 7 * ((Real.log (X : ℝ)) ^ 7)⁻¹ := by
    have hquot :
        (Real.log (X : ℝ)) ^ 7 / (800 : ℝ) ^ 7 ≤
          (Real.log (z : ℝ)) ^ 7 := by
      exact (div_le_iff₀ (by positivity)).2 (by simpa [mul_comm] using hpowLog)
    calc
      ((Real.log (z : ℝ)) ^ 7)⁻¹ ≤
          ((Real.log (X : ℝ)) ^ 7 / (800 : ℝ) ^ 7)⁻¹ :=
        inv_anti₀ (div_pos hDX (by positivity)) hquot
      _ = (800 : ℝ) ^ 7 * ((Real.log (X : ℝ)) ^ 7)⁻¹ := by
        field_simp
        <;> ring
  have hcoef :
      0 ≤ 2 * ((77 : ℝ) / 16) ^ 7 +
        3 * (2 : ℝ) ^ 328 * (Real.log 2) ^ 7 := by positivity
  calc
    ((boundedCandidates X).card : ℝ) ≤
        (2 * ((77 : ℝ) / 16) ^ 7 +
          3 * (2 : ℝ) ^ 328 * (Real.log 2) ^ 7) *
            (X : ℝ) / (Real.log (z : ℝ)) ^ 7 := hZbound
    _ ≤ (2 * ((77 : ℝ) / 16) ^ 7 +
          3 * (2 : ℝ) ^ 328 * (Real.log 2) ^ 7) *
            (X : ℝ) * ((800 : ℝ) ^ 7 *
              ((Real.log (X : ℝ)) ^ 7)⁻¹) := by
        rw [div_eq_mul_inv]
        gcongr
    _ = densityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7 := by
      rw [div_eq_mul_inv]
      unfold densityConstant
      ring

noncomputable def globalDensityConstant : ℝ :=
  max densityConstant
    ((Real.log (((16 ^ 400 : ℕ) : ℝ))) ^ 7)

theorem boundedCandidates_density_global (X : ℕ) :
    ((boundedCandidates X).card : ℝ) ≤
      globalDensityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7 := by
  classical
  by_cases hlarge : 16 ^ 400 ≤ X
  · have h := boundedCandidates_density_large X hlarge
    let q : ℝ := (X : ℝ) / (Real.log (X : ℝ)) ^ 7
    have hquot : 0 ≤ q := by
      dsimp [q]
      positivity
    have hconst : densityConstant ≤ globalDensityConstant := by
      unfold globalDensityConstant
      exact le_max_left _ _
    have h' : ((boundedCandidates X).card : ℝ) ≤ densityConstant * q := by
      calc
        ((boundedCandidates X).card : ℝ) ≤
            densityConstant * (X : ℝ) / (Real.log (X : ℝ)) ^ 7 := h
        _ = densityConstant * q := by
          dsimp [q]
          rw [div_eq_mul_inv]
          ring
    calc
      ((boundedCandidates X).card : ℝ) ≤ densityConstant * q := h'
      _ ≤ globalDensityConstant * q :=
        mul_le_mul_of_nonneg_right hconst hquot
      _ = globalDensityConstant * (X : ℝ) /
          (Real.log (X : ℝ)) ^ 7 := by
        dsimp [q]
        rw [div_eq_mul_inv]
        ring
  · have hsmall : X < 16 ^ 400 := Nat.lt_of_not_ge hlarge
    by_cases hX : X ≤ 1
    · have hempty : boundedCandidates X = ∅ := by
        ext n
        simp only [boundedCandidates, Finset.mem_filter, Finset.mem_Icc,
          Finset.notMem_empty, iff_false]
        omega
      rw [hempty]
      interval_cases X <;> norm_num
    · have hX2 : 2 ≤ X := by omega
      have hcardNat : (boundedCandidates X).card ≤ X := by
        calc
          (boundedCandidates X).card ≤ (Finset.Icc 1 X).card :=
            Finset.card_le_card (by
              intro n hn
              exact (Finset.mem_filter.mp hn).1)
          _ = X := by
            simp [Nat.card_Icc]
      have hcard : ((boundedCandidates X).card : ℝ) ≤ (X : ℝ) := by
        exact_mod_cast hcardNat
      have hlogX : 0 < Real.log (X : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < X by omega))
      have hlogT : 0 < Real.log (((16 ^ 400 : ℕ) : ℝ)) :=
        Real.log_pos (by
          exact_mod_cast (show 1 < (16 ^ 400 : ℕ) by
            exact one_lt_pow' (by norm_num) (by norm_num)))
      have hlogle :
          Real.log (X : ℝ) ≤ Real.log (((16 ^ 400 : ℕ) : ℝ)) := by
        exact Real.log_le_log (by positivity) (by exact_mod_cast hsmall.le)
      have hpowle :
          (Real.log (X : ℝ)) ^ 7 ≤
            (Real.log (((16 ^ 400 : ℕ) : ℝ))) ^ 7 :=
        pow_le_pow_left₀ (le_of_lt hlogX) hlogle 7
      have hDX : 0 < (Real.log (X : ℝ)) ^ 7 := by positivity
      have hXbound :
          (X : ℝ) ≤
            (Real.log (((16 ^ 400 : ℕ) : ℝ))) ^ 7 * (X : ℝ) /
              (Real.log (X : ℝ)) ^ 7 := by
        rw [le_div_iff₀ hDX]
        exact (mul_le_mul_of_nonneg_left hpowle (by positivity)).trans_eq
          (by ring)
      have hconst :
          (Real.log (((16 ^ 400 : ℕ) : ℝ))) ^ 7 ≤
            globalDensityConstant := by
        unfold globalDensityConstant
        exact le_max_right _ _
      calc
        ((boundedCandidates X).card : ℝ) ≤ (X : ℝ) := hcard
        _ ≤ (Real.log (((16 ^ 400 : ℕ) : ℝ))) ^ 7 * (X : ℝ) /
              (Real.log (X : ℝ)) ^ 7 := hXbound
        _ ≤ globalDensityConstant * (X : ℝ) /
              (Real.log (X : ℝ)) ^ 7 := by
          gcongr

end Erdos647
