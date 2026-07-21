/-
Erdős Problem #858 — toward UNIFORM interval Mertens, building block 4
(Chojecki 2026).

**Uniform A-ratio floor limit**: upgrades the campaign's existing per-fixed-x
`Tendsto` statement (`erdos858_a_ratio_floor_limit`, `A(⌊N^x⌋)/log⌊N^x⌋−1→0`
given `|A(k)−logk|≤C`) to a genuinely uniform-in-x explicit-rate bound:

  `|A(⌊N^x⌋)/log⌊N^x⌋ − 1| ≤ 2C/(a·logN)`   for ALL `x≥a` simultaneously.

Proof: derives `log⌊N^x⌋ ≥ (a/2)·logN` uniformly (from building block 1, the
uniform floor-log-ratio bound: `log⌊N^x⌋/logN ≥ x−log2/logN ≥ a−a/2=a/2` given
`x≥a` and the same `log2/logN≤a/2` regime condition), giving `a·logN ≤
2·log⌊N^x⌋`; then bounds the numerator via the fixed `|A(⌊N^x⌋)−log⌊N^x⌋|≤C`
hypothesis. The final `|X|/logfloor ≤ 2C/(a·logN)` step avoided guessing at
div-monotonicity lemma names (after the earlier `div_le_div_iff` naming miss
on building block 2) by pre-computing both cross-multiplied product facts
explicitly (`mul_le_mul_of_nonneg_left`/`_right`, high-confidence standard
names) and closing via `div_le_div_iff₀` + `linarith` on the two products —
avoiding a repeat of that naming risk.

With all FOUR building blocks now verified (uniform floor-log-ratio, the
standalone log-perturbation bound, uniform loglog-floor, and this uniform
A-ratio floor limit), every per-fixed-x ingredient of the §5.3 prime
block-mass limit (`erdos858_prime_block_mass_limit`, #129) now has a
uniform-in-x analogue — the remaining step is assembling them (mirroring
#129's own Tendsto-squeeze structure, but with explicit ε-N0 bounds) into the
UNIFORM interval Mertens capstone that Lemma 5.5 and row 5.7 both need.

Kernel-verified via the proofsearch MCP:
  episode 9de8a953-cfce-4f09-99df-15dd219cd8d8,
  problem_version_id d6049439-5dda-4bf5-9b9d-cb3d97953115.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash a7c113117c672017bc0d6614c95f84b9c410e40bede5493eb61af28c0d8bab03.
-/
import Mathlib

namespace Erdos858

/-- Uniform A-ratio floor limit: `|A(⌊N^x⌋)/log⌊N^x⌋ − 1| ≤ 2C/(a·logN)` for
ALL `x≥a` simultaneously (given `|A(k)−logk|≤C` and the same regime
conditions as the other uniform building blocks) — uniform upgrade of
`erdos858_a_ratio_floor_limit`. -/
theorem erdos858_uniform_a_ratio_floor_limit :
    ∀ (a : ℝ), 0 < a →
      (∀ (a' : ℝ), 0 < a' →
        (∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
          |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2) →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a' →
          ∀ x : ℝ, a' ≤ x →
            |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
      (∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
        (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
        |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2) →
      ∀ (A : ℕ → ℝ) (C : ℝ), (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
      ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a → Real.log 2 / Real.log (N:ℝ) ≤ a/2 →
        ∀ x : ℝ, a ≤ x →
          |A ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) - 1| ≤ 2*C/(a*Real.log (N:ℝ)) := by
  intro a ha hfloorratio hfloorrem A C hA N hN2 hNa2 hδsmall x hax
  have hN1 : (1:ℝ) < (N:ℝ) := (by exact_mod_cast hN2)
  have hlogNpos : 0 < Real.log (N:ℝ) := Real.log_pos hN1
  have hR := hfloorratio a ha hfloorrem N hN2 hNa2 x hax
  have hNx2 : 2 ≤ (N:ℝ)^x := le_trans hNa2 (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) hax)
  have hfloor2 : 2 ≤ ⌊(N:ℝ)^x⌋₊ := Nat.le_floor (by exact_mod_cast hNx2)
  have hfr : (2:ℝ) ≤ ((⌊(N:ℝ)^x⌋₊:ℕ):ℝ) := (by exact_mod_cast hfloor2)
  have hlogfloorpos : 0 < Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) := Real.log_pos (by linarith)
  have hRlo := (abs_le.mp hR).1
  have hlogfloor_ge : (a/2) * Real.log (N:ℝ) ≤ Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) := (by
    have h1 : a/2 ≤ Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))/Real.log (N:ℝ) := (by linarith [hRlo, hδsmall, hax])
    calc (a/2) * Real.log (N:ℝ) ≤ (Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))/Real.log (N:ℝ)) * Real.log (N:ℝ) := (mul_le_mul_of_nonneg_right h1 hlogNpos.le)
      _ = Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) := (by field_simp))
  have hCbound : |A ⌊(N:ℝ)^x⌋₊ - Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))| ≤ C := hA ⌊(N:ℝ)^x⌋₊ hfloor2
  have hCnn : 0 ≤ C := le_trans (abs_nonneg _) hCbound
  have heq : A ⌊(N:ℝ)^x⌋₊ / Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) - 1 = (A ⌊(N:ℝ)^x⌋₊ - Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))) / Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) := (by field_simp)
  rw [heq, abs_div, abs_of_pos hlogfloorpos]
  have hapos : (0:ℝ) < a*Real.log (N:ℝ) := mul_pos ha hlogNpos
  have hstep1 : a*Real.log (N:ℝ) ≤ 2*Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) := (by linarith [hlogfloor_ge])
  have hstep2 : C*(a*Real.log (N:ℝ)) ≤ 2*C*Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) := (by nlinarith [hstep1, hCnn])
  have hstep3 : |A ⌊(N:ℝ)^x⌋₊ - Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))| * (a*Real.log (N:ℝ)) ≤ C*(a*Real.log (N:ℝ)) := (mul_le_mul_of_nonneg_right hCbound hapos.le)
  rw [div_le_div_iff₀ hlogfloorpos hapos]
  linarith [hstep2, hstep3]

end Erdos858
