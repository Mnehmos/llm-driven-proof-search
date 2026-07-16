import Mathlib

/-!
# Erdős #647 — generic leaf-exclusion engine (Engine A, milestone 7)

Snapshots of two statements kernel-verified through the tracked
proof-search pipeline on 2026-07-16 — the symbolic pattern that
generalizes the concrete shift-16 leaf exclusions to arbitrary shifts,
depths, and branches.

**Part 1 — universal exclusion step:**

  problem_version_id  839dc458-4adc-4382-880d-f03e9b741869
  episode_id          87ab49cb-de62-4c7b-a8f4-3724a89f8aa7
  root_statement_hash 93161030548948b561218f426dff6f8eaed396673013df374a5e0100f479be33
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     23ce4d73-157c-4cdf-af85-f942d7e7c7f3 (kernel_pass)

Any divisor `p` with `1 < p < c·t+d` kills primality of the affine value
— the fully generic abstraction of the per-leaf `key` helper.

**Part 2 — unique bad residue:**

  problem_version_id  a2586d9f-e349-425a-8142-536ad3c730ab
  episode_id          0232fe34-07cf-4e9a-98c4-019dd746d6e5
  root_statement_hash 208ff4b4f727624b930c89174fbc09537063a514b4d9f45791c5720851dcea41
  outcome             kernel_verified (root_proved), first tracked attempt
  preverification     164124dc-23be-413c-8e37-3b4048b105e2 (kernel_pass;
                      one prior round 685076e9 left `field_simp` residue
                      `↑d * (-1+1) = 0`, closed by a trailing `ring`)

For every prime `p ∤ c`, the form `c·t+d` is divisible by `p` on EXACTLY
one residue class `t ≡ r (mod p)`, with `r = (−d)·c⁻¹` computed in
`ZMod p`.

**Why together they matter**: every forced-prime terminal leaf whose
coefficient is coprime to a frontier prime acquires exactly one excluded
residue per frontier prime — mechanically. The eight concrete shift-16
exclusion rows (`Erdos647_Shift16LeafFrontierExclusions.lean`) are the
instantiation of this pattern at `(c,d) ∈ {(630,433),(630,59)}`,
`p ∈ {11,13,17,19}`; the same two lemmas will generate the rows for every
leaf the shift-factor framework produces at any depth, which is what the
compatibility-graph API consumes when drawing incompatibility edges.

Import manifest ["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"].
-/

/-- Part 1: any proper divisor strictly between 1 and the value kills
primality of an affine value. -/
theorem erdos647_generic_leaf_exclusion_step :
    ∀ (c d p t : ℕ), 1 < p → p ∣ c * t + d → p < c * t + d →
      ¬ Nat.Prime (c * t + d) := by
  intro c d p t h1 h2 h3 hp
  rcases hp.eq_one_or_self_of_dvd p h2 with h4 | h4 <;> omega

/-- Part 2: a prime not dividing the coefficient divides the affine
values on exactly one residue class of the parameter. -/
theorem erdos647_affine_unique_bad_residue :
    ∀ (c d p : ℕ), Nat.Prime p → ¬ p ∣ c →
      ∃ r, r < p ∧ ∀ t : ℕ, (p ∣ c * t + d ↔ t % p = r) := by
  intro c d p hp hpc
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcne : (c : ZMod p) ≠ 0 := by
    intro h
    exact hpc ((ZMod.natCast_eq_zero_iff c p).mp h)
  set x : ZMod p := - (d : ZMod p) * (c : ZMod p)⁻¹ with hx_def
  have hcast : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_rightInverse x
  refine ⟨x.val, ZMod.val_lt x, ?_⟩
  intro t
  constructor
  · intro hdvd
    have h0 : ((c * t + d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
    push_cast at h0
    have h1 : (c : ZMod p) * t = -(d : ZMod p) := eq_neg_of_add_eq_zero_left h0
    have ht : (t : ZMod p) = x := by
      calc (t : ZMod p) = (c : ZMod p)⁻¹ * ((c : ZMod p) * t) := by
            rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
        _ = (c : ZMod p)⁻¹ * (-(d : ZMod p)) := by rw [h1]
        _ = x := by rw [hx_def]; ring
    have hmm := (ZMod.natCast_eq_natCast_iff' t x.val p).mp (by rw [hcast]; exact ht)
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt x)] at hmm
  · intro hmod
    have ht : (t : ZMod p) = x := by
      rw [← hcast, ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt (ZMod.val_lt x)]
      exact hmod
    have h0 : ((c * t + d : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [ht, hx_def]
      field_simp
      ring
    exact (ZMod.natCast_eq_zero_iff _ p).mp h0
