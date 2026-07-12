/-
CDC step 05 — Annihilator uniqueness in dimension 3 over a two-element field
                (discharges step 02/03's uniqueness hypothesis; implicit in
                cdc-lean's finite `decide`)
Problem version : cf9ca3b0-d4a9-4406-bf34-c406515efd6f
Episode         : 9763965c-5107-45db-bc6e-f5b2e391b250
Outcome         : kernel_verified (2026-07-11, first attempt)
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (K Γ : Type) [Field K] [AddCommGroup Γ] [Module K Γ]
    [FiniteDimensional K Γ] (x y : Γ),
  (∀ c : K, c = 0 ∨ c = 1) →
  Module.finrank K Γ = 3 →
  x ≠ 0 → y ≠ 0 → x ≠ y →
  ∀ p q : Module.Dual K Γ,
    p ≠ 0 → q ≠ 0 →
    p x = 0 → p y = 0 → q x = 0 → q y = 0 → p = q := by
intro K Γ _ _ _ _ x y htwo hrank hx hy hxy p q hp hq hpx hpy hqx hqy
have hli : LinearIndependent K ![x, y] := by
  rw [linearIndependent_fin2]
  constructor
  · simpa using hy
  · intro a ha
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at ha
    rcases htwo a with h0 | h1
    · rw [h0, zero_smul] at ha
      exact hx ha.symm
    · rw [h1, one_smul] at ha
      exact hxy ha.symm
have hW2 : Module.finrank K (Submodule.span K (Set.range ![x, y])) = 2 := by
  rw [finrank_span_eq_card hli]
  simp
have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span K (Set.range ![x, y]))
rw [hW2, hrank] at hsum
have hann : Module.finrank K (Submodule.span K (Set.range ![x, y])).dualAnnihilator = 1 := by
  omega
have hker : ∀ r : Module.Dual K Γ, r x = 0 → r y = 0 →
    r ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := by
  intro r hrx hry
  rw [Submodule.mem_dualAnnihilator]
  intro w hw
  have hle : Submodule.span K (Set.range ![x, y]) ≤ LinearMap.ker r := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    fin_cases i
    · simpa using hrx
    · simpa using hry
  exact LinearMap.mem_ker.mp (hle hw)
have hpA : p ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := hker p hpx hpy
have hqA : q ∈ (Submodule.span K (Set.range ![x, y])).dualAnnihilator := hker q hqx hqy
have hp0 : (⟨p, hpA⟩ : (Submodule.span K (Set.range ![x, y])).dualAnnihilator) ≠ 0 := by
  intro h
  exact hp (by simpa using congrArg Subtype.val h)
have hall := (finrank_eq_one_iff_of_nonzero'
  (⟨p, hpA⟩ : (Submodule.span K (Set.range ![x, y])).dualAnnihilator) hp0).mp hann
obtain ⟨c, hc⟩ := hall ⟨q, hqA⟩
rcases htwo c with h0 | h1
· exfalso
  rw [h0, zero_smul] at hc
  exact hq (by simpa using congrArg Subtype.val hc.symm)
· rw [h1, one_smul] at hc
  simpa using congrArg Subtype.val hc
