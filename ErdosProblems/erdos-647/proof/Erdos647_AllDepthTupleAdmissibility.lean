import Mathlib

/-!
# Erdős #647 — arbitrary-depth prefix-LCM tuple admissibility

For fixed depth `K`, the prefix-LCM conditional construction uses the affine
forms

`((lcm(1,…,K) / k) * t) - 1`,  `1 ≤ k ≤ K`.

Every form has constant term `-1`.  Thus the residue class `t = 0` modulo
every prime avoids every root simultaneously.  The tuple is admissible at
every finite depth, with no finite-prime enumeration and no root-count loss.

There is a formalization trap here.  Evaluating the *natural-number*
subtraction `c * 0 - 1` gives `0`, because `Nat.sub` is truncated.  That is
not the modular value of the integer affine form `c*t - 1`.  Accordingly,
the first theorem states the correct root equation `c*t ≡ 1 (mod p)`, and
the second states the affine form directly in `ZMod p`, where subtraction is
not truncated.

This is a local admissibility theorem, not a simultaneous-primality theorem.
It removes local congruence obstructions only.

Proof-search provenance:

* `Nat.ModEq` formulation: verification job
  `4ce290ef-a886-4cb0-9d28-c6c5f81c5ed5`, problem
  `76570114-2102-49c7-b367-2c340e3da12e`, episode
  `58c73ca8-048c-41dc-86e0-10b0d3d3c558`, `kernel_verified`;
* `ZMod` formulation: verification job
  `a484c41b-6eea-40ba-8f5b-a44bb7608dee`, problem
  `02ac0847-6aaf-4445-85da-42af440bdf41`, episode
  `74a08b85-10e7-4095-b41c-3d2e984c124a`, `kernel_verified`.
-/

/-- At every finite depth and every prime modulus, residue zero avoids all
root equations `((prefixLcm K / k) * t) ≡ 1`. -/
theorem erdos647_all_depth_tuple_admissible_modEq :
    ∀ K : ℕ, 1 ≤ K → ∀ p : ℕ, p.Prime →
      ∃ a : Fin p, ∀ k ∈ Finset.Icc 1 K,
        ¬ Nat.ModEq p
          (((Finset.Icc 1 K).lcm id / k) * (a : ℕ)) 1 := by
  intro K hK p hp
  refine ⟨⟨0, hp.pos⟩, ?_⟩
  intro k hk hroot
  change ((((Finset.Icc 1 K).lcm id / k) * 0) % p) = 1 % p at hroot
  simp [Nat.mod_eq_of_lt hp.one_lt] at hroot

/-- The same admissibility statement in the ring `ZMod p`, explicitly
certifying that every affine value at residue zero is `-1`, hence nonzero. -/
theorem erdos647_all_depth_tuple_admissible_zmod :
    ∀ K : ℕ, 1 ≤ K → ∀ p : ℕ, p.Prime →
      ∃ a : ZMod p, ∀ k ∈ Finset.Icc 1 K,
        (((((Finset.Icc 1 K).lcm id / k : ℕ) : ZMod p) * a) - 1) ≠ 0 := by
  intro K hK p hp
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨0, ?_⟩
  intro k hk
  simp
