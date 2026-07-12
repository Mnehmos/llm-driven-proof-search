/-
CDC step 14 — Bridgeless ⇒ no degree-one vertex
                (mirrors CDCLean.degree_ne_one_of_bridgeless)
Problem version : 7aa583df-c304-4f9f-9396-720964cebc4b
Episode         : fb3502ad-11b3-4848-8c5a-630f6bb5d0c0
Outcome         : kernel_verified (2026-07-11, first attempt)
Chain           : conclusion = hypothesis of step 13, so: bridgeless ⇒
                  rotation system exists. Crossing is encoded decidably as the
                  negated membership biconditional.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false

theorem probe_deg : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ∀ v : V, (Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v)).card ≠ 1 := by
  intro V E _ _ _ _ endAt hloop hbridge v hd
  obtain ⟨h, hh⟩ := Finset.card_eq_one.mp hd
  have hmem : ∀ x : E × Fin 2, endAt x.1 x.2 = v → x = h := by
    intro x hx
    have hx2 : x ∈ Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v) := by
      simp [hx]
    rw [hh] at hx2
    exact Finset.mem_singleton.mp hx2
  have hhv : endAt h.1 h.2 = v := by
    have hself : h ∈ Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v) := by
      rw [hh]
      exact Finset.mem_singleton_self h
    simpa using hself
  have hcut : (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ ({v} : Finset V)) ↔ (endAt e 1 ∈ ({v} : Finset V))))) = {h.1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk
      by_cases hk0 : endAt k 0 = v
      · exact congrArg Prod.fst (hmem (k, 0) hk0)
      · have hk1 : endAt k 1 = v := by
          by_contra hk1
          exact hk (by simp [hk0, hk1])
        exact congrArg Prod.fst (hmem (k, 1) hk1)
    · intro hke
      subst hke
      have hj2 : h.2 = 0 ∨ h.2 = 1 := by omega
      rcases hj2 with hj | hj
      · have h0v : endAt h.1 0 = v := by rw [← hj]; exact hhv
        have h1v : endAt h.1 1 ≠ v := by
          intro hz
          exact hloop h.1 (h0v.trans hz.symm)
        simp [h0v, h1v]
      · have h1v : endAt h.1 1 = v := by rw [← hj]; exact hhv
        have h0v : endAt h.1 0 ≠ v := by
          intro hz
          exact hloop h.1 (hz.trans h1v.symm)
        simp [h0v, h1v]
  have hb := hbridge {v}
  rw [hcut] at hb
  exact hb (Finset.card_singleton h.1)
