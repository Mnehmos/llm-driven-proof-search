/-
CDC step 28 — JK-E-1: conservation completes across a 2-edge cut (the char-2
                core of the recursive two-cut contraction pullback)
                (mirrors CDCLean.nowhereZeroGammaFlow_of_contractEdge_of_twoCut,
                 JaegerKilpatrick.lean 686–793, char-2 / ends-form)
Problem version : 8dda72dc-ccfc-45b4-a4c3-9213abd10162
Episode         : 1e07b2b0-cb95-413d-9e8e-bba0921b5211
Outcome         : kernel_verified (2026-07-11, first attempt)
Statement       : if φ conserves (ends-form, char 2) at every vertex except the
                  two ends of e₁, the cut of S is exactly {e₁,e₂} (e₁≠e₂), and
                  φ e₁ = φ e₂, then φ conserves everywhere. This is the
                  flow-transfer step used to pull a flow on the edge-contracted
                  graph back to the original across a 2-cut.
Method          : global defect sum ∑_v d v = 0 unconditionally in char 2
                  (each edge contributes φe+φe=0); cut sum = ∑_{cut} φe =
                  φe₁+φe₂ = 0 (per-edge sum_ite_eq, ite-not, sum_filter over
                  {e₁,e₂}); e₁ crosses ⇒ one end in S, so
                  Finset.sum_eq_single_of_mem forces the defect to 0 at both
                  ends. Simpler than the reference — char 2 removes all signs.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  φ e₁ = φ e₂ →
  (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
    (∑ e, ((if endAt e 0 = w then φ e else 0) +
      (if endAt e 1 = w then φ e else 0))) = 0) →
  ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
    (if endAt e 1 = v then φ e else 0))) = 0 := by
  intro V E _ _ _ _ endAt φ S e₁ e₂ hcut he₁₂ hφeq hoff
  have hchar2 : ∀ x : ZMod 2, x + x = 0 := by decide
  set d : V → (Fin 3 → ZMod 2) := fun v =>
    ∑ e, ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))
    with hd
  -- global sum is zero (char 2)
  have hsumUniv : ∑ v : V, d v = 0 := by
    simp only [hd]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro e _
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq Finset.univ (endAt e 0) (fun _ => φ e)]
    rw [Finset.sum_ite_eq Finset.univ (endAt e 1) (fun _ => φ e)]
    simp only [Finset.mem_univ, if_true]
    -- φ e + φ e = 0 in char 2
    funext i
    exact hchar2 _
  -- e₁ crosses S
  have he₁cut : e₁ ∈ Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) := by
    rw [hcut]; exact Finset.mem_insert_self e₁ {e₂}
  have hcross₁ : ¬((endAt e₁ 0 ∈ S) ↔ (endAt e₁ 1 ∈ S)) := (Finset.mem_filter.mp he₁cut).2
  -- cut sum equals φ e₁ + φ e₂ = 0
  have hsumS : ∑ v ∈ S, d v = 0 := by
    simp only [hd]
    rw [Finset.sum_comm]
    have hterm : ∀ e : E, (∑ v ∈ S, ((if endAt e 0 = v then φ e else 0) +
        (if endAt e 1 = v then φ e else 0))) =
        if ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)) then φ e else 0 := by
      intro e
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq S (endAt e 0) (fun _ => φ e),
          Finset.sum_ite_eq S (endAt e 1) (fun _ => φ e)]
      by_cases h0 : endAt e 0 ∈ S <;> by_cases h1 : endAt e 1 ∈ S
      · rw [if_pos h0, if_pos h1, if_neg (by simp [h0, h1])]
        funext i; exact hchar2 _
      · rw [if_pos h0, if_neg h1, if_pos (by simp [h0, h1]), add_zero]
      · rw [if_neg h0, if_pos h1, if_pos (by simp [h0, h1]), zero_add]
      · rw [if_neg h0, if_neg h1, if_neg (by simp [h0, h1]), add_zero]
    rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.sum_filter, hcut,
      Finset.sum_pair he₁₂, hφeq]
    funext i; exact hchar2 _
  -- e₁ crosses: exactly one end in S
  have hendsZero : d (endAt e₁ 0) = 0 ∧ d (endAt e₁ 1) = 0 := by
    by_cases h0 : endAt e₁ 0 ∈ S
    · have h1 : endAt e₁ 1 ∉ S := fun h1 => hcross₁ ⟨fun _ => h1, fun _ => h0⟩
      have hd0 : d (endAt e₁ 0) = 0 := by
        have hsingle : ∑ v ∈ S, d v = d (endAt e₁ 0) := by
          apply Finset.sum_eq_single_of_mem (endAt e₁ 0) h0
          intro v hv hvne
          exact hoff v hvne (fun h => h1 (h ▸ hv))
        rw [← hsingle]; exact hsumS
      have hd1 : d (endAt e₁ 1) = 0 := by
        have hsingle : ∑ v : V, d v = d (endAt e₁ 1) := by
          apply Finset.sum_eq_single_of_mem (endAt e₁ 1) (Finset.mem_univ _)
          intro v _ hvne
          by_cases hv0 : v = endAt e₁ 0
          · rw [hv0]; exact hd0
          · exact hoff v hv0 hvne
        rw [← hsingle]; exact hsumUniv
      exact ⟨hd0, hd1⟩
    · have h1 : endAt e₁ 1 ∈ S := by
        by_contra h1
        exact hcross₁ ⟨fun h => (h0 h).elim, fun h => (h1 h).elim⟩
      have hd1 : d (endAt e₁ 1) = 0 := by
        have hsingle : ∑ v ∈ S, d v = d (endAt e₁ 1) := by
          apply Finset.sum_eq_single_of_mem (endAt e₁ 1) h1
          intro v hv hvne
          exact hoff v (fun h => h0 (h ▸ hv)) hvne
        rw [← hsingle]; exact hsumS
      have hd0 : d (endAt e₁ 0) = 0 := by
        have hsingle : ∑ v : V, d v = d (endAt e₁ 0) := by
          apply Finset.sum_eq_single_of_mem (endAt e₁ 0) (Finset.mem_univ _)
          intro v _ hvne
          by_cases hv1 : v = endAt e₁ 1
          · rw [hv1]; exact hd1
          · exact hoff v hvne hv1
        rw [← hsingle]; exact hsumUniv
      exact ⟨hd0, hd1⟩
  intro v
  by_cases hv0 : v = endAt e₁ 0
  · rw [hv0]; exact hendsZero.1
  · by_cases hv1 : v = endAt e₁ 1
    · rw [hv1]; exact hendsZero.2
    · exact hoff v hv0 hv1
