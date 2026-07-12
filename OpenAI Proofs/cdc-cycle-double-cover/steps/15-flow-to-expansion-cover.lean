/-
CDC step 15 — Flow ⇒ localized expansion cover: the vertex-ring expansion is a
                slot-equivalence cubic graph (slot 0 = spoke, 1 = outgoing ring,
                2 = incoming ring via next.symm; ring looplessness = the
                rotation's fixed-point-freeness), so the verified slot-form
                cover theorem (step 08, problem 3917309c — taken here as a
                hypothesis: first theorem-as-hypothesis chain) applied at this
                incidence turns a nowhere-zero F₂³-flow on the expansion into
                the localized cover triple consumed by step 12.
Problem version : e46a54f1-e42c-4852-94a2-a7004c6f9e3e
Episode         : dcc3a393-8dcd-4673-9757-4e4b91e7365d
Outcome         : kernel_verified (2026-07-11, first attempt, pre-flighted)
Chain           : completes bridgeless ⇒(14) ⇒(13) ⇒ [flow on expansion] ⇒(15)
                  ⇒(12) ⇒(11+09) cycle double cover. Unconditional CDC now
                  needs only expansion bridgelessness + the 8-flow theorem.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib
set_option linter.unusedVariables false

theorem probe_L : ∀ (E : Type) [Fintype E] [DecidableEq E] (next : Equiv.Perm (E × Fin 2)),
  (∀ h : E × Fin 2, next h ≠ h) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (inc : (V' × Fin 3) ≃ (E' × Fin 2)) (f : E' → (Fin 3 → ZMod 2)),
    (∀ e : E', (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
    (∀ e : E', f e ≠ 0) →
    (∀ v : V', (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
    ∃ member : (Fin 3 → ZMod 2) → E' → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V'),
        (∑ i : Fin 3, member s ((inc (v, i)).1)) = 0) ∧
      (∀ e : E',
        (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) →
  ∀ fK : (E ⊕ (E × Fin 2)) → (Fin 3 → ZMod 2),
    (∀ k, fK k ≠ 0) →
    (∀ h : E × Fin 2,
      fK (Sum.inl h.1) + fK (Sum.inr h) + fK (Sum.inr (next.symm h)) = 0) →
    ∃ memberK : (Fin 3 → ZMod 2) → (E ⊕ (E × Fin 2)) → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (h : E × Fin 2),
        memberK s (Sum.inl h.1) + memberK s (Sum.inr h) +
          memberK s (Sum.inr (next.symm h)) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        memberK s (Sum.inl e) = 1).card = 2) := by
  intro E _ _ next hne h08 fK hnz hcons
  set incK : ((E × Fin 2) × Fin 3) ≃ ((E ⊕ (E × Fin 2)) × Fin 2) :=
    { toFun := fun p =>
        match p.2 with
        | 0 => (Sum.inl p.1.1, p.1.2)
        | 1 => (Sum.inr p.1, 0)
        | 2 => (Sum.inr (next.symm p.1), 1)
      invFun := fun q =>
        match q.1, q.2 with
        | Sum.inl e, j => ((e, j), 0)
        | Sum.inr k, 0 => (k, 1)
        | Sum.inr k, 1 => (next k, 2)
      left_inv := by
        rintro ⟨h, i⟩
        fin_cases i
        · rfl
        · rfl
        · show (next (next.symm h), 2) = (h, 2)
          rw [Equiv.apply_symm_apply]
      right_inv := by
        rintro ⟨e | k, j⟩
        · fin_cases j <;> rfl
        · fin_cases j
          · rfl
          · show (Sum.inr (next.symm (next k)), (1 : Fin 2)) = (Sum.inr k, 1)
            rw [Equiv.symm_apply_apply] } with hinc
  have hloopK : ∀ k : E ⊕ (E × Fin 2), (incK.symm (k, 0)).1 ≠ (incK.symm (k, 1)).1 := by
    rintro (e | k) heq
    · rw [hinc] at heq
      have h2 : ((e, 0) : E × Fin 2) = ((e, 1) : E × Fin 2) := heq
      have h3 : (0 : Fin 2) = 1 := congrArg Prod.snd h2
      exact absurd h3 (by decide)
    · rw [hinc] at heq
      have h2 : k = next k := heq
      exact hne k h2.symm
  have hconsK : ∀ w : E × Fin 2, (∑ i : Fin 3, fK ((incK (w, i)).1)) = 0 := by
    intro w
    rw [Fin.sum_univ_three, hinc]
    show fK (Sum.inl w.1) + fK (Sum.inr w) + fK (Sum.inr (next.symm w)) = 0
    exact hcons w
  obtain ⟨member, hEven, hTwo⟩ :=
    h08 (E × Fin 2) (E ⊕ (E × Fin 2)) incK fK hloopK hnz hconsK
  refine ⟨member, ?_, ?_⟩
  · intro s h
    have hE := hEven s h
    rw [Fin.sum_univ_three, hinc] at hE
    exact hE
  · intro e
    exact hTwo (Sum.inl e)
