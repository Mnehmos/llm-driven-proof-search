/-
Erdős Problem #858 — toward UNIFORM interval Mertens, building block 1
(Chojecki 2026).

**First step toward uniform Lemma 5.5 / row 5.7's prime ramp** (both flagged
in the catalog as "REACHABLE, needs uniform interval Mertens" — a gap distinct
from the already-verified §5.2/§5.3 interval Mertens, which give convergence
for each FIXED `(s,t)` pair separately, not a bound uniform as the pair
varies).

**uniform floor-log-ratio bound**: `log⌊N^x⌋/log N → x` was previously only
available as a per-fixed-x `Tendsto` statement (#91). This atom upgrades it to
an EXPLICIT rate `|log⌊N^x⌋/logN - x| ≤ log2/logN`, and critically — the bound
`log2/logN` depends ONLY on `N`, not on `x` — so the SAME bound holds
simultaneously for every `x≥a` (any fixed `a>0`), which is exactly the
uniformity Lemma 5.5's argument needs.

Proof: specializes the already-verified floor-remainder bound
(`erdos858_floor_remainder_bound`, `Erdos858_FloorRemainderBound.lean`) at
`A:=Real.log, C:=0, u:=N^x` — trivially `|log k - log k|=0≤0` for the
hypothesis — giving `|log⌊N^x⌋ - log(N^x)|≤log2`, then rewrites
`log(N^x)=x·logN` (`Real.log_rpow`) and divides through by `logN` (`abs_div` +
`gcongr`, which auto-closed the residual `|·|≤log2` goal from `hbound` in
context — the SAME pattern banked earlier this campaign, "gcongr alone closes
↑j1/↑K≤↑j2/↑K from j1≤j2").

Kernel-verified via the proofsearch MCP:
  episode 86601788-66ed-41e2-97e2-f3ae8c0326e0,
  problem_version_id 93ba5a20-62d2-4aaa-b88d-5be2b0d963ca.
Outcome: kernel_verified / root_proved (1st submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 986867bab68793c12e69a7d8050c2a62b917416e0848427e6039d8cdd87aaef7.
-/
import Mathlib

namespace Erdos858

/-- Uniform floor-log-ratio bound: for fixed `a>0` and `N` with `N^a≥2`,
`|log⌊N^x⌋/logN - x| ≤ log2/logN` for EVERY `x≥a` simultaneously — the bound
depends only on `N`, giving genuine uniformity in `x` (unlike the pre-existing
per-fixed-x `Tendsto` form). Building block toward uniform interval Mertens. -/
theorem erdos858_uniform_floor_log_ratio :
    ∀ (a : ℝ), 0 < a →
      (∀ (A : ℕ → ℝ) (C : ℝ) (u : ℝ), 2 ≤ u →
        (∀ k : ℕ, 2 ≤ k → |A k - Real.log (k:ℝ)| ≤ C) →
        |A ⌊u⌋₊ - Real.log u| ≤ C + Real.log 2) →
      ∀ N : ℕ, 2 ≤ N → 2 ≤ (N:ℝ)^a →
        ∀ x : ℝ, a ≤ x →
          |Real.log ((⌊(N:ℝ)^x⌋₊ : ℝ)) / Real.log (N:ℝ) - x| ≤ Real.log 2 / Real.log (N:ℝ) := by
  intro a ha hfloorrem N hN2 hNa2 x hax
  have hN1 : (1:ℝ) < (N:ℝ) := (by exact_mod_cast hN2)
  have hlogNpos : 0 < Real.log (N:ℝ) := Real.log_pos hN1
  have hNx2 : 2 ≤ (N:ℝ)^x := le_trans hNa2 (Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1) hax)
  have hbound := hfloorrem (fun k => Real.log (k:ℝ)) 0 ((N:ℝ)^x) hNx2 (fun k _ => by simp)
  rw [Real.log_rpow (by linarith : (0:ℝ) < (N:ℝ))] at hbound
  simp only [zero_add] at hbound
  have heq : Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) / Real.log (N:ℝ) - x = (Real.log ((⌊(N:ℝ)^x⌋₊:ℝ)) - x * Real.log (N:ℝ)) / Real.log (N:ℝ) := (by field_simp)
  rw [heq, abs_div, abs_of_pos hlogNpos]
  gcongr

end Erdos858
