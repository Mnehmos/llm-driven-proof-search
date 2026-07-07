import Mathlib

/-!
Exported from the tracked ledger (episode `130631aa-4deb-4040-bc6d-f72c6468d833`,
statement hash `32303ccb359f6f8007e88d6f58e40aefd4c2adc26068ce356db81cc1cd4ae28c`).
NOT one of `integer_isGoodPair_iff`'s four assembly pieces (`1/2^k` isn't an
integer for `k ≥ 1`) — a standalone extra result about the `α = 2` fiber.
-/

theorem root_theorem :
    ∀ (k : ℕ), ∀ᶠ j in Filter.atTop, j ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊(1 / (2:ℝ)^k) * (2:ℝ) ^ n⌋) ∧ n = ∑ i ∈ B, i} := by
  intro k
  rw [Filter.eventually_atTop]
  refine ⟨0, fun j hj => ?_⟩
  set E := j.toNat.bitIndices.toFinset with hEdef
  have hE : j.toNat = ∑ i ∈ E, 2 ^ i := (Finset.sum_toFinset_bitIndices_two_pow j.toNat).symm
  refine ⟨E.image (fun i => (2:ℤ)^i), ?_, ?_⟩
  · rintro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨i, _, rfl⟩ := hx
    refine ⟨i + k, ?_⟩
    show ⌊(1 / (2:ℝ)^k) * (2:ℝ)^(i+k)⌋ = 2^i
    have hc : (1 / (2:ℝ)^k) * (2:ℝ)^(i+k) = ((2^i : ℤ) : ℝ) := by
      rw [pow_add]; push_cast; field_simp
    rw [hc, Int.floor_intCast]
  · have hinj : Function.Injective (fun i : ℕ => (2:ℤ)^i) := by
      intro a b hab
      simp only at hab
      have : (2:ℕ)^a = (2:ℕ)^b := by exact_mod_cast hab
      exact Nat.pow_right_injective (le_refl 2) this
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    have hj' : j = (j.toNat : ℤ) := (Int.toNat_of_nonneg hj).symm
    rw [hj']
    exact_mod_cast hE
