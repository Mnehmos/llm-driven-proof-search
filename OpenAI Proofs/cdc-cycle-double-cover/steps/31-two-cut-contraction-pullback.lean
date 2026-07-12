/-
CDC step 31 — JK-E-2c: the full two-cut contraction pullback — a nowhere-zero
                flow on the edge-contracted graph pulls back to a nowhere-zero
                ends-form F₂³ flow on the original
                (mirrors CDCLean.nowhereZeroGammaFlow_of_contractEdge_of_twoCut,
                 JaegerKilpatrick.lean 686–793, abstract merge-map form)
Problem version : 0cf0561e-7176-4071-a692-93971bf687b4
Episode         : f85271cd-ae3d-4a78-9fef-ce643d32a2fc
Outcome         : kernel_verified (2026-07-11, first attempt)
Statement       : q : V → W collapses EXACTLY e₁'s ends; survivors = edges with
                  q(end₀) ≠ q(end₁); given a 2-cut {e₁,e₂} and a nowhere-zero
                  flow ψ on the contracted graph (merged conservation over
                  survivors), the original graph has a nowhere-zero ends-form
                  flow. Takes verified step 28 (8dda72dc) as a hypothesis.
Method          : φ e := if e survives then ψ e else avec (common cut value);
                  φ nowhere-zero, φ e₁ = φ e₂ = avec. Off-support conservation
                  by the survivor/non-survivor split — non-survivors vanish at
                  v ∉ {ends of e₁} (char-2 loop case + {a,b}≠v case), survivors
                  match the merged conservation since end_i e = v ⟺ q(end_i e)
                  = q v there. Step 28 upgrades to full conservation.
                  The abstract q : V → W avoids committed Quotient types; the
                  recursion instantiates W = Quotient (contractEdgeSetoid e₁).
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E W : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [DecidableEq W] (endAt : E → Fin 2 → V) (q : V → W)
    (ψ : E → (Fin 3 → ZMod 2)) (e₁ e₂ : E) (S : Finset V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (φ : E → (Fin 3 → ZMod 2)) (S : Finset V) (e₁ e₂ : E),
    (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
    e₁ ≠ e₂ →
    φ e₁ = φ e₂ →
    (∀ w : V, w ≠ endAt e₁ 0 → w ≠ endAt e₁ 1 →
      (∑ e, ((if endAt e 0 = w then φ e else 0) +
        (if endAt e 1 = w then φ e else 0))) = 0) →
    ∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0) →
  (Finset.univ.filter (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  e₁ ≠ e₂ →
  (∀ u v : V, q u = q v ↔ (u = v ∨
    (u = endAt e₁ 0 ∧ v = endAt e₁ 1) ∨ (u = endAt e₁ 1 ∧ v = endAt e₁ 0))) →
  (∀ e : E, q (endAt e 0) ≠ q (endAt e 1) → ψ e ≠ 0) →
  (∀ w : W, (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
    ((if q (endAt e 0) = w then ψ e else 0) +
      (if q (endAt e 1) = w then ψ e else 0))) = 0) →
  ∃ φ : E → (Fin 3 → ZMod 2),
    (∀ e : E, φ e ≠ 0) ∧
    (∀ v : V, (∑ e, ((if endAt e 0 = v then φ e else 0) +
      (if endAt e 1 = v then φ e else 0))) = 0) := by
  intro V E W _ _ _ _ _ endAt q ψ e₁ e₂ S h28 hcut he₁₂ hq hψnz hmerged
  have hchar2 : ∀ x : ZMod 2, x + x = 0 := by decide
  have hab : q (endAt e₁ 0) = q (endAt e₁ 1) :=
    (hq (endAt e₁ 0) (endAt e₁ 1)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  -- the common cut value
  set avec : (Fin 3 → ZMod 2) :=
    if q (endAt e₂ 0) ≠ q (endAt e₂ 1) then ψ e₂ else (fun _ => 1) with havec
  have havecne : avec ≠ 0 := by
    rw [havec]
    by_cases h : q (endAt e₂ 0) ≠ q (endAt e₂ 1)
    · rw [if_pos h]; exact hψnz e₂ h
    · rw [if_neg h]
      intro hc
      have := congrFun hc 0
      simp at this
  set φ : E → (Fin 3 → ZMod 2) :=
    fun e => if q (endAt e 0) ≠ q (endAt e 1) then ψ e else avec with hφ
  have hφnz : ∀ e : E, φ e ≠ 0 := by
    intro e
    simp only [hφ]
    by_cases h : q (endAt e 0) ≠ q (endAt e 1)
    · rw [if_pos h]; exact hψnz e h
    · rw [if_neg h]; exact havecne
  have hφe₁ : φ e₁ = avec := by
    simp only [hφ]
    rw [if_neg (by rw [not_not]; exact hab)]
  have hφe₂ : φ e₂ = avec := by
    simp only [hφ]
    by_cases h : q (endAt e₂ 0) ≠ q (endAt e₂ 1)
    · rw [if_pos h, havec, if_pos h]
    · rw [if_neg h]
  have hφeq : φ e₁ = φ e₂ := by rw [hφe₁, hφe₂]
  -- off-support conservation
  have hoff : ∀ v : V, v ≠ endAt e₁ 0 → v ≠ endAt e₁ 1 →
      (∑ e, ((if endAt e 0 = v then φ e else 0) +
        (if endAt e 1 = v then φ e else 0))) = 0 := by
    intro v hva hvb
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun e => q (endAt e 0) ≠ q (endAt e 1))]
    have hnon : (∑ e ∈ Finset.univ.filter (fun e => ¬ q (endAt e 0) ≠ q (endAt e 1)),
        ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have hqe : q (endAt e 0) = q (endAt e 1) := not_not.mp (Finset.mem_filter.mp he).2
      rcases (hq (endAt e 0) (endAt e 1)).mp hqe with heq | ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [heq]
        by_cases hx : endAt e 1 = v
        · rw [if_pos hx]; funext i; exact hchar2 _
        · rw [if_neg hx, add_zero]
      · rw [if_neg (by rw [h0]; exact fun hh => hva hh.symm),
            if_neg (by rw [h1]; exact fun hh => hvb hh.symm), add_zero]
      · rw [if_neg (by rw [h0]; exact fun hh => hvb hh.symm),
            if_neg (by rw [h1]; exact fun hh => hva hh.symm), add_zero]
    rw [hnon, add_zero]
    -- survivor part = merged conservation at q v
    have hsurv : (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
        ((if endAt e 0 = v then φ e else 0) + (if endAt e 1 = v then φ e else 0))) =
        (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
        ((if q (endAt e 0) = q v then ψ e else 0) +
          (if q (endAt e 1) = q v then ψ e else 0))) := by
      apply Finset.sum_congr rfl
      intro e he
      have hs : q (endAt e 0) ≠ q (endAt e 1) := (Finset.mem_filter.mp he).2
      have hφe : φ e = ψ e := by simp only [hφ]; rw [if_pos hs]
      have hi0 : (endAt e 0 = v) ↔ (q (endAt e 0) = q v) := by
        constructor
        · intro h; rw [h]
        · intro h
          rcases (hq (endAt e 0) v).mp h with heq | ⟨_, hv⟩ | ⟨_, hv⟩
          · exact heq
          · exact absurd hv hvb
          · exact absurd hv hva
      have hi1 : (endAt e 1 = v) ↔ (q (endAt e 1) = q v) := by
        constructor
        · intro h; rw [h]
        · intro h
          rcases (hq (endAt e 1) v).mp h with heq | ⟨_, hv⟩ | ⟨_, hv⟩
          · exact heq
          · exact absurd hv hvb
          · exact absurd hv hva
      rw [hφe]
      congr 1
      · by_cases h : endAt e 0 = v
        · rw [if_pos h, if_pos (hi0.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hi0.mpr hc))]
      · by_cases h : endAt e 1 = v
        · rw [if_pos h, if_pos (hi1.mp h)]
        · rw [if_neg h, if_neg (fun hc => h (hi1.mpr hc))]
    rw [hsurv]
    exact hmerged (q v)
  exact ⟨φ, hφnz, h28 V E endAt φ S e₁ e₂ hcut he₁₂ hφeq hoff⟩
