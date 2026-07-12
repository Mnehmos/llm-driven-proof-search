/-
CDC step 32 — JK-E-3a: 2-cut existence — a finite multigraph that is
                bridgeless, connected, and NOT 3-edge-connected has a 2-edge
                cut
                (mirrors the case split in
                 CDCLean.jaegerKilpatrickEightFlow_connected, JaegerKilpatrick.lean
                 905–933)
Problem version : e073d2c8-b40e-4ad7-8342-76957d951caf
Episode         : 67dd9620-f09d-4642-8552-4450f4afcf07
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : negating ¬3EC gives a nonempty proper S with < 3 crossing
                  edges; connectivity forces the cut nonempty (a walk-preserves-
                  membership induction, isolated in its own have-block to avoid
                  the induction tactic over-generalizing); bridgeless rules out
                  card 1, so card = 2 by omega; Finset.card_eq_two extracts the
                  witnesses. Supplies the 2-cut consumed by the step-31
                  contraction pullback in the bridgeless→3EC recursion.
LESSON: push_neg/push Not rewrite negations everywhere they match, including
inside filter lambda bodies — normalizing ¬(P ↔ Q) into an xor form and
breaking later syntactic matches. Fixed by naming the cut predicate once via
`set` and destructuring the negated hypothesis with targeted not_forall /
Classical.not_imp / not_le rewrites instead of a blanket push_neg call.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
    ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  ¬ (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ (S : Finset V) (e₁ e₂ : E), e₁ ≠ e₂ ∧
    Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂} := by
  intro V E _ _ _ _ endAt hbridge hconn h3ec
  set cut : Finset V → Finset E := fun T =>
    Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ T) ↔ (endAt e 1 ∈ T))) with hcutdef
  have hcutdef' : ∀ T : Finset V, cut T =
      Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ T) ↔ (endAt e 1 ∈ T))) := fun T => rfl
  have hbridge' : ∀ T : Finset V, (cut T).card ≠ 1 := by
    intro T; rw [hcutdef']; exact hbridge T
  simp only [← hcutdef'] at h3ec
  obtain ⟨S, hS⟩ := not_forall.mp h3ec
  rw [Classical.not_imp, Classical.not_imp, not_le] at hS
  obtain ⟨hSne, hSuniv, hlt'⟩ := hS
  have hcutne : (cut S).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hprop : ∀ a b : V, (∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨
        (endAt t 0 = b ∧ endAt t 1 = a)) → a ∈ S → b ∈ S := by
      intro a b hstep ha
      by_contra hb
      obtain ⟨t, ht⟩ := hstep
      have htmem : t ∈ cut S := by
        rw [hcutdef']
        rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · simp [h0, h1, ha, hb]
        · simp [h0, h1, ha, hb]
      rw [hempty] at htmem
      exact absurd htmem (Finset.notMem_empty t)
    have hwalk : ∀ x y : V, Relation.ReflTransGen
        (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) x y →
        x ∈ S → y ∈ S := by
      intro x y hxy
      induction hxy with
      | refl => exact id
      | tail hab hbc ih => intro hx; exact hprop _ _ hbc (ih hx)
    obtain ⟨u, hu⟩ := hSne
    have hcompl : (Finset.univ \ S).Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      exact hSuniv (Finset.eq_univ_of_forall (fun x => hsub (Finset.mem_univ x)))
    obtain ⟨v, hv⟩ := hcompl
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have hvmem : v ∈ S := hwalk u v (hconn u v) hu
    exact hvS hvmem
  have hcard : (cut S).card = 2 := by
    have h1 := hbridge' S
    have hpos := hcutne.card_pos
    have h3 := hlt'
    omega
  rw [hcutdef'] at hcard
  obtain ⟨e₁, e₂, he₁₂, heq⟩ := Finset.card_eq_two.mp hcard
  exact ⟨S, e₁, e₂, he₁₂, heq⟩
