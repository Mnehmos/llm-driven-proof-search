/-
Erdős Problem #858 — P_N lower bound via floor-indexed prime sum, THE MISSING
LINK between P_N's exact definition and interval Mertens (Chojecki 2026).

**Resolves the technical gap flagged when row 5.7's literal completion was
first attempted**: `P_N(a)`'s exact Lean definition (`Finset.Icc(a+1)N`
filtered by the INTEGER condition `a*p≤N`) doesn't obviously match the
interval-Mertens machinery's `⌊N^t⌋`-indexed sums. Rather than proving the
harder two-sided asymptotic equivalence `N/a ≈ ⌊N^{1-s}⌋` (which would need a
delicate squeeze argument), this establishes a clean ONE-DIRECTIONAL subset
bound that suffices for LOWER-bounding `P_N(a)`.

**Key elementary fact**: for `a:=⌊N^s⌋`, `a≤N^s` (`Nat.floor_le`) and
`⌊N^{1-s}⌋≤N^{1-s}` (same lemma), so their product is `≤N^s·N^{1-s}=N`
(`Real.rpow_add`) — i.e. `a·⌊N^{1-s}⌋≤N` as NATURALS. This means EVERY prime
`p≤⌊N^{1-s}⌋` automatically satisfies `a·p≤N`, so the floor-indexed prime
range `(a,⌊N^{1-s}⌋]` is a Finset SUBSET of `P_N(a)`'s own defining range
`{p∈(a,N] : a·p≤N}` — giving `S(a,⌊N^{1-s}⌋) ≤ P_N(a)` via
`Finset.sum_le_sum_of_subset_of_nonneg` (the SAME lemma
`prop46_PN_monotone` already uses for its own monotonicity proof).

**Why this matters**: `S(a,⌊N^{1-s}⌋)` (the plain prime-sum over a
floor-rpow-indexed range) is EXACTLY the quantity `erdos858_prime_block_mass_limit`
(#129) and `erdos858_uniform_prime_block_mass_bound` already give asymptotics
for. So `P_N(a) ≥ S(a,⌊N^{1-s}⌋) → log(t/s)` (with `t:=1-s`) lower-bounds
`P_N`'s asymptotic — exactly what row 5.7's ramp needs (`1+δ≤P_N(L)`), and
likely reusable for Lemma 5.5 too.

Kernel-verified via the proofsearch MCP:
  episode 624a9333-a1a2-4608-8031-097b0acbc516,
  problem_version_id 2c18ab22-597e-433e-9975-f77551582937.
Outcome: kernel_verified / root_proved (1st submission, despite several
chained real-number/floor steps).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash 8f1d82b10680a5bec968a38431670f16ed4863e1d081b3a83fe850417c19cf23.
-/
import Mathlib

namespace Erdos858

/-- P_N lower bound via floor: for `a:=⌊N^s⌋`, the floor-indexed prime sum
`S(a,⌊N^{1-s}⌋)` is `≤ P_N(a)` — a ONE-DIRECTIONAL subset bound (avoiding the
harder N/a≈⌊N^{1-s}⌋ asymptotic equivalence) connecting P_N's exact
`a*p≤N`-based definition to the interval-Mertens `⌊N^t⌋`-indexed machinery. -/
theorem erdos858_pn_lower_bound_via_floor :
    ∀ (N a : ℕ) (s : ℝ), 0 ≤ s → s ≤ 1 → 1 ≤ N → a = ⌊(N:ℝ)^s⌋₊ → 1 ≤ a →
      (∑ p ∈ (Finset.Icc (a+1) ⌊(N:ℝ)^(1-s)⌋₊).filter (fun p => Nat.Prime p), (1:ℚ)/(p:ℚ))
        ≤ (∑ p ∈ (Finset.Icc (a+1) N).filter (fun p => Nat.Prime p ∧ a * p ≤ N), (1:ℚ)/(p:ℚ)) := by
  intro N a s hs0 hs1 hN1 haeq ha1
  have hNpos : (0:ℝ) < (N:ℝ) := (by exact_mod_cast hN1)
  have hasN : (a:ℝ) ≤ (N:ℝ)^s := (by rw [haeq]; exact Nat.floor_le (Real.rpow_nonneg hNpos.le s))
  have hfloorle : ((⌊(N:ℝ)^(1-s)⌋₊:ℕ):ℝ) ≤ (N:ℝ)^(1-s) := Nat.floor_le (Real.rpow_nonneg hNpos.le (1-s))
  have heq : (N:ℝ)^s * (N:ℝ)^(1-s) = (N:ℝ) := (by
    rw [← Real.rpow_add hNpos]
    have hexp : s + (1 - s) = (1:ℝ) := (by ring)
    rw [hexp, Real.rpow_one])
  have hmulle : (a:ℝ) * ((⌊(N:ℝ)^(1-s)⌋₊:ℕ):ℝ) ≤ (N:ℝ) := (by
    have hstep : (a:ℝ) * ((⌊(N:ℝ)^(1-s)⌋₊:ℕ):ℝ) ≤ (N:ℝ)^s * (N:ℝ)^(1-s) := mul_le_mul hasN hfloorle (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le s)
    linarith [hstep, heq])
  have hmulleNat : a * ⌊(N:ℝ)^(1-s)⌋₊ ≤ N := (by exact_mod_cast hmulle)
  have hfloorleN : ⌊(N:ℝ)^(1-s)⌋₊ ≤ N := (by
    have h1 : (N:ℝ)^(1-s) ≤ (N:ℝ) := (by
      have hNge1 : (1:ℝ) ≤ (N:ℝ) := (by exact_mod_cast hN1)
      calc (N:ℝ)^(1-s) ≤ (N:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
        _ = (N:ℝ) := Real.rpow_one (N:ℝ))
    have h2 : ⌊(N:ℝ)^(1-s)⌋₊ ≤ ⌊(N:ℝ)⌋₊ := Nat.floor_mono h1
    rwa [Nat.floor_natCast] at h2)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨h1,h2⟩,hprime⟩ := hp
    refine ⟨⟨h1, le_trans h2 hfloorleN⟩, hprime, ?_⟩
    calc a * p ≤ a * ⌊(N:ℝ)^(1-s)⌋₊ := (by gcongr)
      _ ≤ N := hmulleNat
  · intro p _ _
    positivity

end Erdos858
