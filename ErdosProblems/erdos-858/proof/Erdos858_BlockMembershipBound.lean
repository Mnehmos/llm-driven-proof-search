/-
Erdős Problem #858 — §5.4 log-harmonic transfer, concrete assembly atom 2/3 (Chojecki 2026).

`block membership implies u_a bound` (exact, non-asymptotic): for N K j : ℕ with
1 < N, 0 < K, j < K, and a in `Finset.Ioc (⌊N^(j/K)⌋₊) (⌊N^((j+1)/K)⌋₊)`, the
log-coordinate `u_a = log a / log N` satisfies `j/K < u_a ≤ (j+1)/K` EXACTLY, for
every N and K — no asymptotics needed:
  - left bound from `a > ⌊N^(j/K)⌋₊ ≥ N^(j/K)` (via the floor property
    `x < ⌊x⌋₊+1`, i.e. `Nat.lt_floor_add_one`);
  - right bound from `a ≤ ⌊N^((j+1)/K)⌋₊ ≤ N^((j+1)/K)` (via `Nat.floor_le`).
Then applying log monotonicity (`Real.log_lt_log` / `Real.log_le_log`) and dividing
by `log N > 0`.

This is the block-membership bound needed for the per-block uniform-continuity
oscillation control in the concrete log-harmonic transfer — it sidesteps ever
needing a fiber-index-equality lemma, since only the one-directional
membership⇒bound is needed for the oscillation estimate.

Kernel-verified via the proofsearch MCP:
  episode 2fd1a6f4-89bb-4de1-9513-a0ea6b773744,
  problem_version_id 23909c74-b4e4-436b-a394-c799d9bc057d.
Outcome: kernel_verified / root_kernel_verified (2nd submission; 1st failed on a
now-diagnosed and campaign-wide-confirmed multi-line `have := by` scoping bug —
see the Lean lesson below).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 2ca89561fc22a13cda3fc34d720345f992676324636ad1c744a03d58f1e4d85e.

**Lean lesson (campaign-wide, confirmed independently in an erdos-647 session the
same day)**: a nested `have h : T := by\n  tac1\n  tac2` block (newline
immediately after `by`, tactics on subsequent indented lines) can silently
mis-scope in this proofsearch pipeline's Lean rendering — the tactics' final
result ends up checked against the OUTER goal instead of closing the have's own
local goal, producing a confusing pair of diagnostics (an "unsolved goals" on
the have's own goal, plus a correctly-typed-but-wrong-target term surfacing far
downstream at the next real tactic boundary, e.g. inside a final `refine`
bullet). The top-level theorem's own `:= by\n  intro ...` is NOT affected — only
nested `have`s. Fix: write nested haves as a single LINE with tactics separated
by `;` (`have h : T := by tac1; tac2`), or pure term-mode (`heq ▸ h`, `.mp`).
Here it was `hlog1`/`hlog2`, each originally `have h : T := by\n  have hh :=
...\n  rwa [...] at hh`, flattened to `have h : T := by have hh := ...; rwa
[...] at hh`. Everything else in the proof (floor bounds, final refine bullets)
was already correct — `Real.log_lt_log (hx:0<x)(h:x<y) : log x<log y` and
`Real.log_le_log (hx:0<x)(hxy:x≤y) : log x≤log y` are the confirmed-correct
signatures (were never actually the problem).
-/
import Mathlib

namespace Erdos858

/-- Concrete assembly atom 2/3 (block membership ⇒ u_a bound, exact/non-asymptotic):
for `1 < N`, `0 < K`, `j < K`, membership in the block `(⌊N^(j/K)⌋₊, ⌊N^((j+1)/K)⌋₊]`
pins the log-coordinate `u_a = log a/log N` to `j/K < u_a ≤ (j+1)/K` exactly, for
every N and K. Proof: floor properties (`Nat.lt_floor_add_one`, `Nat.floor_le`) +
log monotonicity. Toward the per-block oscillation bound and the concrete
log-harmonic transfer. -/
theorem erdos858_block_membership_bound :
    ∀ (N K j : ℕ), 1 < (N:ℝ) → 0 < K → j < K → ∀ (a : ℕ),
      a ∈ Finset.Ioc (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊) (⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊) →
      (j:ℝ) / (K:ℝ) < Real.log (a:ℝ) / Real.log (N:ℝ) ∧ Real.log (a:ℝ) / Real.log (N:ℝ) ≤ ((j:ℝ) + 1) / (K:ℝ) := by
  intro N K j hN hK hj a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Ioc.mp ha
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos hN
  have hNj_pos : (0:ℝ) < (N:ℝ) ^ ((j:ℝ) / (K:ℝ)) := Real.rpow_pos_of_pos hNpos _
  have hNj1_pos : (0:ℝ) < (N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ)) := Real.rpow_pos_of_pos hNpos _
  have ha_pos : (0:ℕ) < a := by omega
  have ha_pos' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha_pos
  have h1nat : (⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℕ) + 1 ≤ a := by omega
  have h1 : ((⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℕ) : ℝ) + 1 ≤ (a:ℝ) := by exact_mod_cast h1nat
  have h2 : (N:ℝ) ^ ((j:ℝ) / (K:ℝ)) < ((⌊(N:ℝ) ^ ((j:ℝ) / (K:ℝ))⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : (N:ℝ) ^ ((j:ℝ) / (K:ℝ)) < (a:ℝ) := by linarith
  have h3 : (a:ℝ) ≤ ((⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℕ) : ℝ) := by exact_mod_cast ha2
  have h4 : ((⌊(N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ))⌋₊ : ℕ) : ℝ) ≤ (N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ)) := Nat.floor_le (le_of_lt hNj1_pos)
  have hle : (a:ℝ) ≤ (N:ℝ) ^ (((j:ℝ) + 1) / (K:ℝ)) := by linarith
  have hlog1 : (j:ℝ) / (K:ℝ) * Real.log (N:ℝ) < Real.log (a:ℝ) := by have hh := Real.log_lt_log hNj_pos hlt; rwa [Real.log_rpow hNpos] at hh
  have hlog2 : Real.log (a:ℝ) ≤ ((j:ℝ) + 1) / (K:ℝ) * Real.log (N:ℝ) := by have hh := Real.log_le_log ha_pos' hle; rwa [Real.log_rpow hNpos] at hh
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hlogN]; linarith
  · rw [div_le_iff₀ hlogN]; linarith

end Erdos858
