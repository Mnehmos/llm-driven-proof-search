/-
Erdős Problem #858 — toward UNIFORM interval Mertens, building block 3
(Chojecki 2026).

**Uniform loglog-floor limit**: upgrades the campaign's existing per-fixed-x
`Tendsto` statement (`erdos858_loglog_floor_limit`) to a genuinely uniform-in-x
explicit-rate bound:

  `|loglog⌊N^x⌋ − loglogN − logx| ≤ 2·(log2/logN)/a`   for ALL `x≥a` simultaneously.

Combines building block 1 (`erdos858_uniform_floor_log_ratio`, giving
`|R−x|≤log2/logN` for `R:=log⌊N^x⌋/logN`) with building block 2
(`erdos858_log_uniform_bound`, at `δ:=log2/logN`) to bound `|logR−logx|`, then
converts `logR = log(log⌊N^x⌋/logN)` into `loglog⌊N^x⌋−loglogN` via
`Real.log_div` (needing `log⌊N^x⌋>0`, from `⌊N^x⌋≥2` — derived via
`Nat.le_floor` from `N^x≥2`, mirroring `Erdos858_FloorRemainderBound.lean`'s
identical pattern).

This is directly the piece needed to make the §5.3 prime block-mass limit
(previously proven only for each FIXED `(s,t)` pair separately, #129/
`erdos858_prime_block_mass_limit`) uniform as `(s,t)` ranges over a compact
interval bounded away from 0 — the core requirement of Lemma 5.5's uniformity
and row 5.7's prime ramp (both flagged "REACHABLE, needs uniform interval
Mertens").

Kernel-verified via the proofsearch MCP:
  episode 455c52aa-8645-486c-9fa4-f8e477035a39,
  problem_version_id ab03c005-8de6-46ef-b287-abe9ac41fba2.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash db26a0ec2e60c0ef9ec68cb51833961d83d417674e3724fa57f7c1b22919e62c.
-/
import Mathlib

namespace Erdos858

/-- Uniform loglog-floor limit: `|loglog⌊N^x⌋ − loglogN − logx| ≤ 2·(log2/logN)/a`
for ALL `x≥a` simultaneously (given `N^a≥2` and `log2/logN≤a/2`) — chains the
uniform floor-log-ratio bound into the log-perturbation bound, then converts
via `Real.log_div`. Uniform upgrade of `erdos858_loglog_floor_limit`. -/
theorem erdos858_uniform_loglog_floor_limit :
    ∀ (a : ℝ), 0 < a →
      (∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
        (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
        |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2) →
      (∀ (a' : ℝ), 0 < a' →
        (∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
          (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
          |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2) →
        ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a' →
          ∀ x : ℝ, a' ≤ x →
            |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ)) →
      (∀ (a' δ R x : ℝ), 0 < a' → a' ≤ x → 0 ≤ δ → δ ≤ a'/2 → |R - x| ≤ δ →
        |Real.log R - Real.log x| ≤ 2*δ/a') →
      ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a → Real.log 2 / Real.log (N:ℝ) ≤ a/2 →
        ∀ x : ℝ, a ≤ x →
          |Real.log (Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))) - Real.log (Real.log (N:ℝ)) - Real.log x| ≤ 2*(Real.log 2/Real.log (N:ℝ))/a := by
  intro a ha hfloorrem hfloorratio hlogbound N hN2 hNa2 hδsmall x hax
  have hN1 : (1:ℝ) < (N:ℝ) := (by exact_mod_cast hN2)
  have hlogNpos : 0 < Real.log (N:ℝ) := Real.log_pos hN1
  have hR := hfloorratio a ha hfloorrem N hN2 hNa2 x hax
  have hδpos : (0:ℝ) ≤ Real.log 2 / Real.log (N:ℝ) := div_nonneg (Real.log_nonneg (by norm_num)) hlogNpos.le
  have hbound := hlogbound a (Real.log 2/Real.log (N:ℝ)) (Real.log ((⌊(N:ℝ)^x⌋₊:ℝ))/Real.log (N:ℝ)) x ha hax hδpos hδsmall hR
  have hNx2 : 2 ≤ (N:ℝ)^x := le_trans hNa2 (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) hax)
  have hfloor2 : 2 ≤ ⌊(N:ℝ)^x⌋₊ := Nat.le_floor (by exact_mod_cast hNx2)
  have hfr : (2:ℝ) ≤ ((⌊(N:ℝ)^x⌋₊:ℕ):ℝ) := (by exact_mod_cast hfloor2)
  have hlogfloorpos : 0 < Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) := Real.log_pos (by linarith)
  rw [Real.log_div (ne_of_gt hlogfloorpos) (ne_of_gt hlogNpos)] at hbound
  exact hbound

end Erdos858
