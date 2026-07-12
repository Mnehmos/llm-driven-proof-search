/-
CDC step 33 — JK-E-3: THE BRIDGELESS-TO-3EC CONTRACTION RECURSION — for
                connected finite multigraphs, bridgelessness alone (no
                3-edge-connectivity assumption) implies a nowhere-zero
                ends-form F₂³ flow
                (mirrors CDCLean.jaegerKilpatrickEightFlow_connected,
                 JaegerKilpatrick.lean 902–933, via a concrete subtype
                 contraction instead of genuine Quotient/Setoid machinery)
Problem version : aae6e901-7438-4e49-be94-d3e75df152ec
Episode         : 820065fe-ea40-476b-a30a-ebc0b2d56a53
Outcome         : kernel_verified (2026-07-11, first attempt)
Hypotheses      : hFlow3EC (3EC ⇒ flow — dischargeable by composing steps
                  29+30, taken as a bare hypothesis to stay under the ~7KB
                  episode-statement ceiling), step 28 (8dda72dc), step 31 —
                  the pullback (0cf0561e), step 32 — 2-cut existence
                  (e073d2c8).
Method          : strong induction on n bounding Fintype.card V. Base case:
                  V empty forces E empty, flow vacuous. Step: if 3EC, apply
                  hFlow3EC; else extract a 2-cut {e₁,e₂} via step 32, derive
                  e₁'s looplessness from cut membership, and contract
                  CONCRETELY: W := {v : V // v ≠ endAt e₁ 1} (a subtype, not a
                  Quotient — Fintype/DecidableEq come for free, no Classical
                  needed), q v := if v = endAt e₁ 1 then ⟨endAt e₁ 0, _⟩ else
                  ⟨v, _⟩. Proves q collapses exactly e₁'s ends, card W < card V,
                  connectivity of the contracted graph (survivor edges become
                  contracted steps; collapsed edges are absorbed), and
                  bridgelessness of the contracted graph (a card bijection via
                  Subtype.val between the contracted cut and the original cut
                  of q's preimage). Applies the IH to get a survivor-indexed
                  flow, lifts it to all of E (junk 0 off-survivors), and pulls
                  back via step 31.
Built with the sorry-skeleton-first discipline across ~8 local iterations;
the full ~220-line recursion compiled with zero sorries and kernel-verified
on the very first server attempt.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem :
  -- hFlow3EC: 3EC ⇒ flow (dischargeable by composing steps 29+30; taken here as a bare hypothesis)
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V),
    (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
      3 ≤ (Finset.univ.filter (fun e : E =>
        ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
    ∃ f : E → (Fin 3 → ZMod 2),
      (∀ e : E, f e ≠ 0) ∧
      (∀ (v : V) (i : Fin 3),
        (∑ e : E, ((if endAt e 0 = v then f e i else 0) +
          (if endAt e 1 = v then f e i else 0))) = 0)) →
  -- h28: step 28, conservation completes across a 2-cut
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
  -- hPull: step 31, the two-cut contraction pullback (abstract merge-map q)
  (∀ (V E W : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (if endAt e 1 = v then φ e else 0))) = 0)) →
  -- h2cut: step 32, 2-cut existence
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V),
    (∀ S : Finset V, (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    (∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
    ¬ (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
      3 ≤ (Finset.univ.filter (fun e : E =>
        ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
    ∃ (S : Finset V) (e₁ e₂ : E), e₁ ≠ e₂ ∧
      Finset.univ.filter (fun e : E => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) = {e₁, e₂}) →
  ∀ n : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
          (if endAt e 1 = v then f e i else 0))) = 0) := by
  intro hFlow3EC h28 hPull h2cut n
  induction n with
  | zero =>
      intro V E _ _ _ _ endAt hcard hconn hbridge
      have hVempty : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
      have hEempty : IsEmpty E := by
        constructor
        intro e
        exact hVempty.elim (endAt e 0)
      exact ⟨fun e => (hEempty.elim e), fun e => (hEempty.elim e),
        fun v i => (hVempty.elim v)⟩
  | succ k ih =>
      intro V E _ _ _ _ endAt hcard hconn hbridge
      by_cases h3 : ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
          3 ≤ (Finset.univ.filter (fun e : E =>
            ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card
      · obtain ⟨f, hfnz, hfcons⟩ := hFlow3EC V E endAt h3
        exact ⟨f, hfnz, fun v i => hfcons v i⟩
      · obtain ⟨S, e₁, e₂, he₁₂, hcuteq⟩ := h2cut V E endAt hbridge hconn h3
        -- e₁ crosses S, so its ends are distinct
        have he₁mem : e₁ ∈ Finset.univ.filter (fun e : E =>
            ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S))) := by
          rw [hcuteq]; exact Finset.mem_insert_self e₁ {e₂}
        have hloop1 : endAt e₁ 0 ≠ endAt e₁ 1 := by
          intro heq
          exact (Finset.mem_filter.mp he₁mem).2 (by rw [heq])
        -- the contracted vertex type: V minus one of e₁'s two ends
        set a0 := endAt e₁ 0
        set a1 := endAt e₁ 1
        let W := {v : V // v ≠ a1}
        letI : Fintype W := Subtype.fintype _
        letI : DecidableEq W := Subtype.instDecidableEq
        set q : V → W := fun v => if h : v = a1 then ⟨a0, hloop1⟩ else ⟨v, h⟩ with hqdef
        have hqiff : ∀ u v : V, q u = q v ↔ (u = v ∨ (u = a0 ∧ v = a1) ∨ (u = a1 ∧ v = a0)) := by
          intro u v
          simp only [hqdef]
          by_cases hu : u = a1 <;> by_cases hv : v = a1
          · rw [dif_pos hu, dif_pos hv]
            constructor
            · intro _; exact Or.inl (hu.trans hv.symm)
            · intro _; rfl
          · rw [dif_pos hu, dif_neg hv]
            constructor
            · intro heq
              have hav : a0 = v := congrArg Subtype.val heq
              exact Or.inr (Or.inr ⟨hu, hav.symm⟩)
            · rintro (h | ⟨_, h2⟩ | ⟨_, h2⟩)
              · rw [hu] at h; exact absurd h.symm hv
              · exact absurd h2 hv
              · exact Subtype.ext h2.symm
          · rw [dif_neg hu, dif_pos hv]
            constructor
            · intro heq
              have hua : u = a0 := congrArg Subtype.val heq
              exact Or.inr (Or.inl ⟨hua, hv⟩)
            · rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
              · exact absurd (h.trans hv) hu
              · exact Subtype.ext h1
              · exact absurd h1 hu
          · rw [dif_neg hu, dif_neg hv]
            constructor
            · intro heq
              exact Or.inl (congrArg Subtype.val heq)
            · rintro (h | ⟨_, h2⟩ | ⟨h1, _⟩)
              · exact Subtype.ext h
              · exact absurd h2 hv
              · exact absurd h1 hu
        have hqsurj : ∀ w : W, ∃ v : V, q v = w := by
          rintro ⟨v, hv⟩
          refine ⟨v, ?_⟩
          simp only [hqdef]
          rw [dif_neg hv]
        have hcardW : Fintype.card W < Fintype.card V := by
          have hWcard : Fintype.card W = Fintype.card V - 1 := by
            have hWcard' : Fintype.card {v : V // v ≠ a1} = (Finset.univ.erase a1).card := by
              rw [Fintype.card_subtype]
              congr 1
              ext v
              simp [Finset.mem_erase]
            rw [hWcard', Finset.card_erase_of_mem (Finset.mem_univ a1), Finset.card_univ]
          have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨a1⟩
          omega
        -- contracted edges: survivors of the merge
        let survives : E → Prop := fun f => q (endAt f 0) ≠ q (endAt f 1)
        letI : DecidablePred survives := fun f => inferInstanceAs (Decidable (q (endAt f 0) ≠ q (endAt f 1)))
        let Esub := {f : E // survives f}
        letI : Fintype Esub := Subtype.fintype _
        letI : DecidableEq Esub := Subtype.instDecidableEq
        let endAt' : Esub → Fin 2 → W := fun f i => q (endAt f.1 i)
        -- connectivity transfer
        have hconnW : ∀ p r : W, Relation.ReflTransGen
            (fun x y => ∃ f : Esub, (endAt' f 0 = x ∧ endAt' f 1 = y) ∨
              (endAt' f 0 = y ∧ endAt' f 1 = x)) p r := by
          have hstepV : ∀ x y : V, Relation.ReflTransGen
              (fun a b => ∃ t : E, (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) x y →
              Relation.ReflTransGen
                (fun x y => ∃ f : Esub, (endAt' f 0 = x ∧ endAt' f 1 = y) ∨
                  (endAt' f 0 = y ∧ endAt' f 1 = x)) (q x) (q y) := by
            intro x y hxy
            induction hxy with
            | refl => exact Relation.ReflTransGen.refl
            | tail hab hbc ih2 =>
                obtain ⟨t, ht⟩ := hbc
                by_cases hs : survives t
                · refine ih2.tail ?_
                  rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
                  · exact ⟨⟨t, hs⟩, Or.inl ⟨by simp [endAt', h0], by simp [endAt', h1]⟩⟩
                  · exact ⟨⟨t, hs⟩, Or.inr ⟨by simp [endAt', h0], by simp [endAt', h1]⟩⟩
                · have hcollapse : q (endAt t 0) = q (endAt t 1) := not_not.mp hs
                  rcases ht with ⟨h0, h1⟩ | ⟨h0, h1⟩
                  · rw [h0, h1] at hcollapse; rw [← hcollapse]; exact ih2
                  · rw [h0, h1] at hcollapse; rw [hcollapse]; exact ih2
          intro p r
          obtain ⟨x, hx⟩ := hqsurj p
          obtain ⟨y, hy⟩ := hqsurj r
          rw [← hx, ← hy]
          exact hstepV x y (hconn x y)
        -- bridgelessness transfer
        have hbridgeW : ∀ A : Finset W, (Finset.univ.filter (fun f : Esub =>
            ¬((endAt' f 0 ∈ A) ↔ (endAt' f 1 ∈ A)))).card ≠ 1 := by
          intro A
          set S' : Finset V := Finset.univ.filter (fun v => q v ∈ A) with hS'def
          have hmem : ∀ v : V, v ∈ S' ↔ q v ∈ A := by
            intro v; rw [hS'def]; simp
          have himg : (Finset.univ.filter (fun f : Esub =>
              ¬((endAt' f 0 ∈ A) ↔ (endAt' f 1 ∈ A)))).image Subtype.val =
              Finset.univ.filter (fun t : E => ¬((endAt t 0 ∈ S') ↔ (endAt t 1 ∈ S'))) := by
            ext t
            simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨f, hf, rfl⟩
              rw [hmem, hmem]
              exact hf
            · intro ht
              have hsurv : survives t := by
                intro heq
                exact ht (by rw [hmem, hmem, heq])
              refine ⟨⟨t, hsurv⟩, ?_, rfl⟩
              rw [hmem, hmem] at ht
              exact ht
          have hcardeq : (Finset.univ.filter (fun f : Esub =>
              ¬((endAt' f 0 ∈ A) ↔ (endAt' f 1 ∈ A)))).card =
              (Finset.univ.filter (fun t : E => ¬((endAt t 0 ∈ S') ↔ (endAt t 1 ∈ S')))).card := by
            rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
          rw [hcardeq]
          exact hbridge S'
        -- apply the induction hypothesis to the contracted graph
        have hcardWk : Fintype.card W ≤ k := by omega
        obtain ⟨ψ, hψnz, hψcons⟩ := ih W Esub endAt' hcardWk hconnW hbridgeW
        -- lift ψ (over survivors) to a total function on E
        let ψfull : E → (Fin 3 → ZMod 2) := fun e =>
          if h : survives e then ψ ⟨e, h⟩ else 0
        have hψfulleq : ∀ f : Esub, ψfull f.1 = ψ f := by
          intro f
          simp only [ψfull]
          rw [dif_pos f.2]
        have hψfullnz : ∀ e : E, survives e → ψfull e ≠ 0 := by
          intro e hs
          simp only [ψfull]
          rw [dif_pos hs]
          exact hψnz ⟨e, hs⟩
        have hψfullmerged : ∀ w : W, (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
            ((if q (endAt e 0) = w then ψfull e else 0) +
              (if q (endAt e 1) = w then ψfull e else 0))) = 0 := by
          intro w
          have hreindex : (∑ e ∈ Finset.univ.filter (fun e => q (endAt e 0) ≠ q (endAt e 1)),
              ((if q (endAt e 0) = w then ψfull e else 0) +
                (if q (endAt e 1) = w then ψfull e else 0))) =
              (∑ f : Esub, ((if endAt' f 0 = w then ψ f else 0) +
                (if endAt' f 1 = w then ψ f else 0))) := by
            rw [Finset.sum_subtype (p := survives) (Finset.univ.filter
              (fun e => q (endAt e 0) ≠ q (endAt e 1))) (by intro x; simp [survives])]
            apply Finset.sum_congr rfl
            intro f _
            rw [hψfulleq f]
          rw [hreindex]
          funext i
          have hcons := hψcons w i
          simp only [Finset.sum_apply, Pi.add_apply] at hcons ⊢
          simp only [apply_ite (fun g : Fin 3 → ZMod 2 => g i), Pi.zero_apply]
          exact hcons
        -- pull back via step 31
        obtain ⟨φ, hφnz, hφcons⟩ := hPull V E W endAt q ψfull e₁ e₂ S
          h28 hcuteq he₁₂ hqiff hψfullnz hψfullmerged
        refine ⟨φ, hφnz, fun v i => ?_⟩
        have hv := hφcons v
        have hvi : (∑ e : E, ((if endAt e 0 = v then φ e else 0) +
            (if endAt e 1 = v then φ e else 0))) i = (0 : Fin 3 → ZMod 2) i := by rw [hv]
        simpa [Finset.sum_apply, Pi.add_apply,
          apply_ite (fun g : Fin 3 → ZMod 2 => g i), Pi.zero_apply] using hvi
