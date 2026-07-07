import Mathlib

/-!
Exported from the tracked ledger (episode `6766c89d-7840-4d11-9fa6-fb7495f12435`,
statement hash `b2eb28f162b568bbe4bc83534248463d1efab3ae807e13866c0eaa8d36f55d21`).
Registered under theorem_name `alpha_le_one_not_isGoodPair_diag` (a single-line
restatement used to diagnose an unrelated import-manifest bug — see
`../evidence.md` — the statement itself is byte-identical to the corpus's
`alpha_le_one_not_isGoodPair`, just written without an embedded newline).
One of `integer_isGoodPair_iff`'s four assembly pieces: `α ≤ 1` fails.
-/

theorem root_theorem :
    ∀ (t : ℝ), 0 < t → ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ¬ (∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) ∧ n = ∑ i ∈ B, i}) := by
  intro t ht α hα0 hα1 h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have hrange : Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) ⊆ ↑(Finset.Icc (0:ℤ) ⌊t⌋) := by
    rintro _ ⟨n, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    have hpow_pos : 0 < α ^ n := pow_pos hα0 n
    have hpow_le : α ^ n ≤ 1 := pow_le_one₀ hα0.le hα1
    have hle : t * α ^ n ≤ t := by nlinarith
    have hpos : 0 < t * α ^ n := by positivity
    exact ⟨Int.floor_nonneg.mpr hpos.le, Int.floor_le_floor hle⟩
  set C : ℤ := ∑ i ∈ Finset.Icc (0:ℤ) ⌊t⌋, i with hCdef
  have hbound : ∀ k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊t * α ^ n⌋) ∧ n = ∑ i ∈ B, i}, k ≤ C := by
    rintro k ⟨B, hBsub, rfl⟩
    have hBsub' : B ⊆ Finset.Icc (0:ℤ) ⌊t⌋ := by
      intro x hx
      have hxr := hBsub hx
      have := hrange hxr
      simpa using this
    exact Finset.sum_le_sum_of_subset_of_nonneg hBsub' (fun i hi _ => by simpa using (Finset.mem_Icc.mp hi).1)
  have hk := hN (max N (C+1)) (le_max_left _ _)
  have := hbound _ hk
  have hge : C + 1 ≤ max N (C+1) := le_max_right _ _
  omega
