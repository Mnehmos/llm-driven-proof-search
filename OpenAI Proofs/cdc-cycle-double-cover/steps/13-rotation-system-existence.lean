/-
CDC step 13 — Rotation-system existence: every finite multigraph without a
                degree-one vertex admits a vertex-preserving, fixed-point-free,
                fiber-transitive permutation of its half-edges
                (mirrors CDCLean.rotationSystemOfDegreeNeOne, unbundled)
Problem version : abd3fd7f-4d0d-4042-98cc-14e68449e9db
Episode         : 04744cf3-b179-45d4-b0cb-f4a15896ba29
Outcome         : kernel_verified (2026-07-11, first server attempt after four
                  local pre-flight iterations)
Chain           : hypothesis discharged by step 14; conclusion supplies the
                  rotation consumed by the projection step 12.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false
set_option linter.deprecated false

#check @finCycle_eq_finRotate_iterate
#check @finCycle_apply

theorem probe_rotation : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ v : V, (Finset.univ.filter (fun h : E × Fin 2 => endAt h.1 h.2 = v)).card ≠ 1) →
  ∃ next : Equiv.Perm (E × Fin 2),
    (∀ h : E × Fin 2, endAt (next h).1 (next h).2 = endAt h.1 h.2) ∧
    (∀ h : E × Fin 2, next h ≠ h) ∧
    (∀ h k : E × Fin 2, endAt h.1 h.2 = endAt k.1 k.2 →
      ∃ n : ℕ, (⇑next)^[n] h = k) := by
  intro V E _ _ _ _ endAt hdeg
  classical
  have hcard : ∀ v : V, Fintype.card {h : E × Fin 2 // endAt h.1 h.2 = v} ≠ 1 := by
    intro v
    rw [Fintype.card_subtype]
    exact hdeg v
  have hrot_ne : ∀ (n : ℕ), n ≠ 1 → ∀ a : Fin n, finRotate n a ≠ a := by
    intro n hn a
    match n, hn, a with
    | 0, _, a => exact a.elim0
    | 1, hn, _ => exact absurd rfl hn
    | (k+2), _, a =>
      intro heq
      rw [finRotate_succ_apply] at heq
      have haa : a + 1 = a + 0 := by rw [add_zero]; exact heq
      have h0 : (1 : Fin (k+2)) = 0 := add_left_cancel haa
      have hv := congrArg Fin.val h0
      rw [Fin.val_one, Fin.val_zero] at hv
      exact one_ne_zero hv
  set σ : (E × Fin 2) ≃ ((v : V) × {h : E × Fin 2 // endAt h.1 h.2 = v}) :=
    { toFun := fun h => ⟨endAt h.1 h.2, h, rfl⟩
      invFun := fun p => p.2.1
      left_inv := fun h => rfl
      right_inv := by
        rintro ⟨v, ⟨h, hh⟩⟩
        subst hh
        rfl } with hσ
  set fc : ∀ v : V, Equiv.Perm {h : E × Fin 2 // endAt h.1 h.2 = v} :=
    fun v => (Fintype.equivFin _).trans ((finRotate _).trans (Fintype.equivFin _).symm)
    with hfc
  refine ⟨σ.trans ((Equiv.sigmaCongrRight fc).trans σ.symm), ?_, ?_, ?_⟩
  · intro h
    simp only [Equiv.trans_apply]
    have hs : σ h = ⟨endAt h.1 h.2, h, rfl⟩ := by rw [hσ]; rfl
    rw [hs, Equiv.sigmaCongrRight_apply]
    have hv : ∀ p : ((v : V) × {x : E × Fin 2 // endAt x.1 x.2 = v}),
        endAt ((σ.symm p).1) ((σ.symm p).2) = p.1 := by
      rintro ⟨v, ⟨x, hx⟩⟩
      have hsymm : σ.symm ⟨v, ⟨x, hx⟩⟩ = x := by rw [hσ]; rfl
      rw [hsymm]
      exact hx
    exact hv _
  · intro h heq
    have hs := congrArg σ heq
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply] at hs
    have hsh : σ h = ⟨endAt h.1 h.2, h, rfl⟩ := by rw [hσ]; rfl
    rw [hsh, Equiv.sigmaCongrRight_apply] at hs
    have hf : fc (endAt h.1 h.2) ⟨h, rfl⟩ = ⟨h, rfl⟩ := by
      have hp := (Sigma.mk.injEq _ _ _ _).mp hs
      exact eq_of_heq hp.2
    have hi := congrArg (Fintype.equivFin {h' : E × Fin 2 // endAt h'.1 h'.2 = endAt h.1 h.2}) hf
    rw [hfc] at hi
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at hi
    exact hrot_ne _ (hcard (endAt h.1 h.2)) _ hi
  · intro h k hvk
    have heh : endAt h.1 h.2 = endAt h.1 h.2 := rfl
    set eh : {x : E × Fin 2 // endAt x.1 x.2 = endAt h.1 h.2} := ⟨h, rfl⟩ with hehdef
    set ek : {x : E × Fin 2 // endAt x.1 x.2 = endAt h.1 h.2} := ⟨k, hvk.symm⟩ with hekdef
    set ef := Fintype.equivFin {x : E × Fin 2 // endAt x.1 x.2 = endAt h.1 h.2} with hefdef
    obtain ⟨n, hn⟩ : ∃ n : ℕ,
        (⇑(finRotate (Fintype.card {x : E × Fin 2 // endAt x.1 x.2 = endAt h.1 h.2})))^[n]
          (ef eh) = ef ek := by
      haveI : NeZero (Fintype.card {x : E × Fin 2 // endAt x.1 x.2 = endAt h.1 h.2}) :=
        ⟨(ef eh).pos.ne'⟩
      refine ⟨(ef ek - ef eh).val, ?_⟩
      rw [← finCycle_eq_finRotate_iterate]
      simp only [finCycle_apply]
      rw [sub_eq_add_neg]
      abel
    have hsemFiber : Function.Semiconj ef (fc (endAt h.1 h.2))
        (finRotate (Fintype.card {x : E × Fin 2 // endAt x.1 x.2 = endAt h.1 h.2})) := by
      intro x
      rw [hfc, hefdef]
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    have hfiber : (⇑(fc (endAt h.1 h.2)))^[n] eh = ek := by
      apply ef.injective
      rw [hsemFiber.iterate_right]
      exact hn
    set sigmaCycle : Equiv.Perm ((v : V) × {x : E × Fin 2 // endAt x.1 x.2 = v}) :=
      Equiv.sigmaCongrRight fc with hsc
    have hsemEmbed : Function.Semiconj
        (fun x : {x : E × Fin 2 // endAt x.1 x.2 = endAt h.1 h.2} =>
          (⟨endAt h.1 h.2, x⟩ : (v : V) × {x : E × Fin 2 // endAt x.1 x.2 = v}))
        (fc (endAt h.1 h.2)) sigmaCycle := by
      intro x
      rw [hsc]
      rfl
    have hsigma : (⇑sigmaCycle)^[n] ⟨endAt h.1 h.2, eh⟩ = ⟨endAt h.1 h.2, ek⟩ := by
      rw [← hsemEmbed.iterate_right]
      exact congrArg _ hfiber
    have hsemGlobal : Function.Semiconj (⇑σ)
        (⇑(σ.trans ((Equiv.sigmaCongrRight fc).trans σ.symm))) (⇑sigmaCycle) := by
      intro x
      rw [hsc]
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    refine ⟨n, σ.injective ?_⟩
    rw [hsemGlobal.iterate_right]
    have hh : σ h = ⟨endAt h.1 h.2, eh⟩ := by rw [hσ, hehdef]; rfl
    have hk : σ k = ⟨endAt h.1 h.2, ek⟩ := by
      rw [hσ, hekdef]
      refine Sigma.ext hvk.symm ?_
      refine (Subtype.heq_iff_coe_eq ?_).2 rfl
      intro x
      show (endAt x.1 x.2 = endAt k.1 k.2) ↔ (endAt x.1 x.2 = endAt h.1 h.2)
      rw [hvk]
    rw [hh, hk]
    exact hsigma
