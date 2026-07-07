import Mathlib

/-!
Exported from the tracked ledger (episode `0d2fa763-6adc-4a4d-bd4d-e3626bad712a`,
statement hash `ec9344f81572cf51336326d49a224e0abeae96f161623ba088c4c31008064737`).
One of `integer_isGoodPair_iff`'s four assembly pieces: `(1, 2)` is good.
-/

theorem root_theorem :
    ∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊(1:ℝ) * (2:ℝ) ^ n⌋) ∧ n = ∑ i ∈ B, i} := by
  rw [Filter.eventually_atTop]
  refine ⟨0, fun k hk => ?_⟩
  set E := k.toNat.bitIndices.toFinset with hEdef
  have hE : k.toNat = ∑ i ∈ E, 2 ^ i := (Finset.sum_toFinset_bitIndices_two_pow k.toNat).symm
  refine ⟨E.image (fun i => (2:ℤ)^i), ?_, ?_⟩
  · rintro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨i, _, rfl⟩ := hx
    refine ⟨i, ?_⟩
    show ⌊(1:ℝ) * (2:ℝ)^i⌋ = 2^i
    have hc : (1:ℝ) * (2:ℝ)^i = ((2^i : ℤ) : ℝ) := by push_cast; ring
    rw [hc, Int.floor_intCast]
  · have hinj : Function.Injective (fun i : ℕ => (2:ℤ)^i) := by
      intro a b hab
      simp only at hab
      have : (2:ℕ)^a = (2:ℕ)^b := by exact_mod_cast hab
      exact Nat.pow_right_injective (le_refl 2) this
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    have hk' : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg hk).symm
    rw [hk']
    exact_mod_cast hE
