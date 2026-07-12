/-
CDC step 34 — JK-E-4: COMPONENT DECOMPOSITION — the connectedness hypothesis
                drops: EVERY finite bridgeless multigraph has a nowhere-zero
                ends-form F₂³ flow
                (mirrors CDCLean.jaegerKilpatrickEightFlow_of_nonempty and the
                 component machinery, JaegerKilpatrick.lean 1110–1219)
Problem version : 5145a5c2-63e7-4c86-805e-cfae1e2577b1
Episode         : 82de0408-700c-4382-91f0-ec34ac2c4f1d
Outcome         : kernel_verified (2026-07-11, first attempt)
Hypothesis      : step 33's conclusion verbatim (the ∀n vertex-count-bounded
                  connected form) — the chain composes by direct application.
Method          : reach := edge-walk reachability; equivalence (symmetry by
                  walk reversal); classifier c := Quotient.out over the
                  reachability Setoid. Per root r: component subtypes
                  {v // reach r v} / {e // reach r (endAt e 0)}, endAtr by
                  Fin-2 match; connectivity lift (tail induction with
                  existential endpoint proof); bridgelessness by Subtype.val
                  image-card bijection against the original cut of
                  A.image val; apply step 33 at n := card of the component;
                  convert subtype-form conservation to val-form once per
                  component. Glue: per-root flows chosen; global flow
                  f e := ψ (c (endAt e 0)); conservation at v splits into v's
                  component (subtype reindex + proof-irrelevance ψ-congruence
                  + component-constancy of c) and off-component edges (both
                  if-terms vanish).
WITH THIS STEP, THE 8-FLOW THEOREM IS COMPLETE: 34 ← 33 ← (29∘30) ←
{17,18,19,21,22,23,24,25,26,27} + {28,31,32} — every finite bridgeless
multigraph has a nowhere-zero ends-form F₂³ flow.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem :
  (∀ n : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V),
    Fintype.card V ≤ n →
    (∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
    (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ f : E → (Fin 3 → ZMod 2),
      (∀ e : E, f e ≠ 0) ∧
      (∀ (v : V) (i : Fin 3),
        (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
          (if endAt e 1 = v then f e i else 0))) = 0)) →
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V),
    (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ f : E → (Fin 3 → ZMod 2),
      (∀ e : E, f e ≠ 0) ∧
      (∀ (v : V) (i : Fin 3),
        (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
          (if endAt e 1 = v then f e i else 0))) = 0) := by
  intro hFlowConn V E _ _ _ _ endAt hbridge
  classical
  set reach : V → V → Prop := fun u v => Relation.ReflTransGen
    (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v
    with hreachdef
  have hreachiff : ∀ u v : V, reach u v ↔ Relation.ReflTransGen
      (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v :=
    fun _ _ => Iff.rfl
  have hsymm : ∀ x y : V, reach x y → reach y x := by
    intro x y hxy
    rw [hreachiff] at hxy ⊢
    refine Relation.ReflTransGen.head_induction_on hxy ?_ ?_
    · exact Relation.ReflTransGen.refl
    · rintro a c ⟨t, ht⟩ hcq ih
      refine ih.tail ⟨t, ?_⟩
      rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact Or.inl ⟨h0, h1⟩
  have htrans : ∀ x y z : V, reach x y → reach y z → reach x z := by
    intro x y z h1 h2
    rw [hreachiff] at h1 h2 ⊢
    exact h1.trans h2
  have hrefl : ∀ x : V, reach x x := fun x => (hreachiff x x).mpr Relation.ReflTransGen.refl
  -- classifier: canonical representative of each component
  set RS : Setoid V := ⟨reach, ⟨hrefl, fun {a b} h => hsymm a b h,
    fun {a b c} h1 h2 => htrans a b c h1 h2⟩⟩ with hRSdef
  set c : V → V := fun v => (Quotient.mk RS v).out with hcdef
  have hcv : ∀ v : V, reach (c v) v := by
    intro v
    have h := Quotient.out_eq (Quotient.mk RS v)
    exact Quotient.exact h
  have hceq : ∀ u v : V, reach u v → c u = c v := by
    intro u v huv
    simp only [hcdef]
    exact congrArg Quotient.out (Quotient.sound huv)
  -- per-root component flow, val-form conservation
  have hcomp : ∀ r : V, ∃ ψ : {e : E // reach r (endAt e 0)} → (Fin 3 → ZMod 2),
      (∀ es, ψ es ≠ 0) ∧
      (∀ w : V, reach r w → ∀ i : Fin 3,
        (∑ es : {e : E // reach r (endAt e 0)},
          ((if endAt es.1 0 = w then ψ es i else 0) +
            (if endAt es.1 1 = w then ψ es i else 0))) = 0) := by
    intro r
    -- component vertex/edge subtypes
    let Vr := {v : V // reach r v}
    let Er := {e : E // reach r (endAt e 0)}
    letI : Fintype Vr := Subtype.fintype _
    letI : DecidableEq Vr := Subtype.instDecidableEq
    letI : Fintype Er := Subtype.fintype _
    letI : DecidableEq Er := Subtype.instDecidableEq
    have hreach1 : ∀ es : Er, reach r (endAt es.1 1) := by
      intro es
      refine htrans _ _ _ es.2 ?_
      rw [hreachiff]
      exact Relation.ReflTransGen.single ⟨es.1, Or.inl ⟨rfl, rfl⟩⟩
    let endAtr : Er → Fin 2 → Vr := fun es i =>
      match i with
      | 0 => ⟨endAt es.1 0, es.2⟩
      | 1 => ⟨endAt es.1 1, hreach1 es⟩
    -- connectivity of the component
    have hlift : ∀ x y : V, reach x y → ∀ hx : reach r x, ∃ hy : reach r y,
        Relation.ReflTransGen (fun p q : Vr => ∃ ts : Er,
          (endAtr ts 0 = p ∧ endAtr ts 1 = q) ∨ (endAtr ts 0 = q ∧ endAtr ts 1 = p))
        ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro x y hxy
      rw [hreachiff] at hxy
      induction hxy with
      | refl => exact fun hx => ⟨hx, Relation.ReflTransGen.refl⟩
      | @tail b' c' hab hbc ih =>
          intro hx
          obtain ⟨hb, w⟩ := ih hx
          obtain ⟨t, ht⟩ := hbc
          rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · -- t : b' → c' oriented (end0 = b', end1 = c')
            have htEr : reach r (endAt t 0) := by rw [h0]; exact hb
            have hc : reach r c' := by rw [← h1]; exact hreach1 ⟨t, htEr⟩
            refine ⟨hc, w.tail ?_⟩
            exact ⟨⟨t, htEr⟩, Or.inl ⟨Subtype.ext h0, Subtype.ext h1⟩⟩
          · -- t : c' → b' oriented (end0 = c', end1 = b')
            have hb' : reach r (endAt t 1) := by rw [h1]; exact hb
            have hstep : reach (endAt t 1) (endAt t 0) := by
              rw [hreachiff]
              exact Relation.ReflTransGen.single ⟨t, Or.inr ⟨rfl, rfl⟩⟩
            have htEr : reach r (endAt t 0) := htrans _ _ _ hb' hstep
            have hc : reach r c' := by rw [← h0]; exact htEr
            refine ⟨hc, w.tail ?_⟩
            exact ⟨⟨t, htEr⟩, Or.inr ⟨Subtype.ext h0, Subtype.ext h1⟩⟩
    have hconnr : ∀ p q : Vr, Relation.ReflTransGen (fun p q : Vr => ∃ ts : Er,
        (endAtr ts 0 = p ∧ endAtr ts 1 = q) ∨ (endAtr ts 0 = q ∧ endAtr ts 1 = p)) p q := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      have hxy : reach x y := htrans _ _ _ (hsymm _ _ hx) hy
      obtain ⟨hy', w⟩ := hlift x y hxy hx
      have : (⟨y, hy'⟩ : Vr) = ⟨y, hy⟩ := Subtype.ext rfl
      rw [this] at w
      exact w
    -- bridgelessness of the component
    have hbridger : ∀ A : Finset Vr, (Finset.univ.filter (fun es : Er =>
        ¬((endAtr es 0 ∈ A) ↔ (endAtr es 1 ∈ A)))).card ≠ 1 := by
      intro A
      set S : Finset V := A.image Subtype.val with hSdef
      have hmemS : ∀ (x : V) (hx : reach r x), x ∈ S ↔ (⟨x, hx⟩ : Vr) ∈ A := by
        intro x hx
        rw [hSdef]
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨a, ha, hav⟩
          have : a = ⟨x, hx⟩ := Subtype.ext hav
          rw [← this]; exact ha
        · intro h
          exact ⟨⟨x, hx⟩, h, rfl⟩
      have himg : (Finset.univ.filter (fun es : Er =>
          ¬((endAtr es 0 ∈ A) ↔ (endAtr es 1 ∈ A)))).image Subtype.val =
          Finset.univ.filter (fun t : E => ¬((endAt t 0 ∈ S) ↔ (endAt t 1 ∈ S))) := by
        ext t
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨es, hes, rfl⟩
          rw [hmemS (endAt es.1 0) es.2, hmemS (endAt es.1 1) (hreach1 es)]
          exact hes
        · intro ht
          -- one crossing end is in S ⊆ component, so t's end0 is reachable
          have hone : endAt t 0 ∈ S ∨ endAt t 1 ∈ S := by
            by_cases h0 : endAt t 0 ∈ S <;> by_cases h1 : endAt t 1 ∈ S
            · exact Or.inl h0
            · exact Or.inl h0
            · exact Or.inr h1
            · exact absurd ⟨fun h => absurd h h0, fun h => absurd h h1⟩ ht
          have ht0 : reach r (endAt t 0) := by
            rcases hone with h | h
            · rw [hSdef] at h
              obtain ⟨a, _, hav⟩ := Finset.mem_image.mp h
              rw [← hav]; exact a.2
            · rw [hSdef] at h
              obtain ⟨a, _, hav⟩ := Finset.mem_image.mp h
              have h1r : reach r (endAt t 1) := by rw [← hav]; exact a.2
              have hstep : reach (endAt t 1) (endAt t 0) := by
                rw [hreachiff]
                exact Relation.ReflTransGen.single ⟨t, Or.inr ⟨rfl, rfl⟩⟩
              exact htrans _ _ _ h1r hstep
          refine ⟨⟨t, ht0⟩, ?_, rfl⟩
          rw [hmemS (endAt t 0) ht0, hmemS (endAt t 1) (hreach1 ⟨t, ht0⟩)] at ht
          exact ht
      have hcardeq : (Finset.univ.filter (fun es : Er =>
          ¬((endAtr es 0 ∈ A) ↔ (endAtr es 1 ∈ A)))).card =
          (Finset.univ.filter (fun t : E => ¬((endAt t 0 ∈ S) ↔ (endAt t 1 ∈ S)))).card := by
        rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
      rw [hcardeq]
      exact hbridge S
    -- apply the connected flow theorem to the component
    obtain ⟨ψ0, hnz0, hcons0⟩ := hFlowConn (Fintype.card Vr) Vr Er endAtr
      le_rfl hconnr hbridger
    refine ⟨ψ0, hnz0, ?_⟩
    intro w hw i
    have h := hcons0 ⟨w, hw⟩ i
    -- convert subtype-equality if-conditions to val-form
    have hconv : (∑ es : Er,
        ((if endAt es.1 0 = w then ψ0 es i else 0) +
          (if endAt es.1 1 = w then ψ0 es i else 0))) =
        (∑ es : Er,
        ((if endAtr es 0 = ⟨w, hw⟩ then ψ0 es i else 0) +
          (if endAtr es 1 = ⟨w, hw⟩ then ψ0 es i else 0))) := by
      apply Finset.sum_congr rfl
      intro es _
      congr 1
      · by_cases h0 : endAt es.1 0 = w
        · rw [if_pos h0, if_pos (Subtype.ext h0 : endAtr es 0 = ⟨w, hw⟩)]
        · rw [if_neg h0, if_neg (fun hc => h0 (congrArg Subtype.val hc))]
      · by_cases h1 : endAt es.1 1 = w
        · rw [if_pos h1, if_pos (Subtype.ext h1 : endAtr es 1 = ⟨w, hw⟩)]
        · rw [if_neg h1, if_neg (fun hc => h1 (congrArg Subtype.val hc))]
    rw [hconv]
    exact h
  choose ψ hψnz hψcons using hcomp
  refine ⟨fun e => ψ (c (endAt e 0)) ⟨e, hcv (endAt e 0)⟩, fun e => hψnz _ _, ?_⟩
  intro v i
  -- edges incident to v all lie in v's component; off-component terms vanish
  have hpsi_congr : ∀ (r r' : V) (hrr : r = r') (e : E)
      (h1 : reach r (endAt e 0)) (h2 : reach r' (endAt e 0)),
      ψ r ⟨e, h1⟩ = ψ r' ⟨e, h2⟩ := by
    intro r r' hrr e h1 h2
    subst hrr
    rfl
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun e => reach (c v) (endAt e 0))]
  have hnon : (∑ e ∈ Finset.univ.filter (fun e => ¬ reach (c v) (endAt e 0)),
      ((if endAt e 0 = v then ψ (c (endAt e 0)) ⟨e, hcv (endAt e 0)⟩ i else 0) +
        (if endAt e 1 = v then ψ (c (endAt e 0)) ⟨e, hcv (endAt e 0)⟩ i else 0))) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    have hnr : ¬ reach (c v) (endAt e 0) := (Finset.mem_filter.mp he).2
    have h0 : endAt e 0 ≠ v := by
      intro h
      exact hnr (h ▸ hcv v)
    have h1 : endAt e 1 ≠ v := by
      intro h
      have hcv1 : reach (c v) (endAt e 1) := by rw [h]; exact hcv v
      have hstep : reach (endAt e 1) (endAt e 0) := by
        rw [hreachiff]
        exact Relation.ReflTransGen.single ⟨e, Or.inr ⟨rfl, rfl⟩⟩
      exact hnr (htrans _ _ _ hcv1 hstep)
    rw [if_neg h0, if_neg h1, add_zero]
  rw [hnon, add_zero]
  -- on-component terms: reindex to the component subtype and use ψ's conservation
  have hsub : (∑ e ∈ Finset.univ.filter (fun e => reach (c v) (endAt e 0)),
      ((if endAt e 0 = v then ψ (c (endAt e 0)) ⟨e, hcv (endAt e 0)⟩ i else 0) +
        (if endAt e 1 = v then ψ (c (endAt e 0)) ⟨e, hcv (endAt e 0)⟩ i else 0))) =
      (∑ es : {e : E // reach (c v) (endAt e 0)},
        ((if endAt es.1 0 = v then ψ (c v) es i else 0) +
          (if endAt es.1 1 = v then ψ (c v) es i else 0))) := by
    rw [Finset.sum_subtype (p := fun e => reach (c v) (endAt e 0))
      (Finset.univ.filter (fun e => reach (c v) (endAt e 0))) (by intro x; simp)]
    apply Finset.sum_congr rfl
    intro es _
    have hcc : c (endAt es.1 0) = c v := by
      have h1 : reach (endAt es.1 0) v := htrans _ _ _ (hsymm _ _ es.2) (hcv v)
      exact hceq _ _ h1
    have hpsi : ψ (c (endAt es.1 0)) ⟨es.1, hcv (endAt es.1 0)⟩ = ψ (c v) es := by
      have h2 := hpsi_congr (c (endAt es.1 0)) (c v) hcc es.1 (hcv (endAt es.1 0)) es.2
      exact h2
    rw [hpsi]
  rw [hsub]
  exact hψcons (c v) v (hcv v) i
