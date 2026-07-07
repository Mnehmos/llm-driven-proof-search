import Mathlib

/-!
Exported from the tracked ledger (episode `f447f17e-18d7-48fd-b1ef-1ee8aa7bb9c8`,
statement hash `444d78b6081aa380d9260f96fb8501f05347817736672fdc2f0a9a08f769747f`).
One of `integer_isGoodPair_iff`'s four assembly pieces: integer `t ≥ 2` fails.
-/

theorem root_theorem :
    ∀ (t : ℤ), 2 ≤ t → ∀ (α : ℤ),
    ¬ (∀ᶠ k in Filter.atTop, k ∈ {n : ℤ | ∃ B : Finset ℤ, ↑B ⊆ Set.range (fun n : ℕ ↦ ⌊(t:ℝ) * (α:ℝ) ^ n⌋) ∧ n = ∑ i ∈ B, i}) := by
  intro t ht α h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  set k : ℤ := t * (N.natAbs + 1) + 1 with hkdef
  have hNk : N ≤ k := by
    have h1 : N ≤ (N.natAbs : ℤ) := Int.le_natAbs
    have h2 : (0:ℤ) ≤ N.natAbs := Int.natCast_nonneg N.natAbs
    nlinarith
  have hkt : ¬ (t ∣ k) := by
    rintro ⟨c, hc⟩
    have h1 : t ∣ (1:ℤ) := ⟨c - (N.natAbs + 1), by linarith [hc]⟩
    have := Int.le_of_dvd one_pos h1
    omega
  obtain ⟨B, hBsub, hBeq⟩ := hN k hNk
  apply hkt
  rw [hBeq]
  apply Finset.dvd_sum
  intro i hi
  obtain ⟨n, hn⟩ := hBsub hi
  simp only at hn
  rw [← hn]
  have heq : (t:ℝ) * (α:ℝ)^n = ((t * α^n : ℤ) : ℝ) := by push_cast; ring
  rw [heq, Int.floor_intCast]
  exact ⟨α^n, rfl⟩
