/-
CDC step 26 — NW-3 (Nash-Williams campaign, THE EXCHANGE LEMMA — Diestel's
                Lemma 2.4.3 / 3.5.3, the heart of the tree-packing theorem;
                replaces the role of cdc-lean's Kaiser machinery,
                NashWilliams.lean 337–3459, whose recursively-defined partition
                sequences cannot cross our plain-statement chaining boundary):
                a maximum tuple of three pairwise-disjoint forests and an edge
                e in none of them admit a vertex predicate P containing both
                ends of e with every pair of P-vertices connected within P by
                every forest.
Problem version : 3632c255-b78e-4128-9a1e-9602c3946de4
Episode         : 9f74edd6-8a3e-44bb-a9d5-58be0b4cb486
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : one 490-line declaration. Exchange steps on tuples (insert a
                  free edge, delete a bridge of its ends), Reach = ReflTransGen
                  closure, P = the free-edge adjacency component of e's end
                  over all reachable tuples. Local lemmas: walk_symm,
                  subst_lemma (insert-decomposition), exchange_forest,
                  insert_forest, hinv (invariants along Reach), hfe (maximality
                  ⇒ free ends connected everywhere), hA (minimal connecting
                  subsets consist of bridges, hence exchangeable, making the
                  connecting walk P-internal), htrans (reachable-tuple walks
                  translate back to F), and the adjacency-chain assembly.
                  Pre-flighted under maxHeartbeats 200000 (server budget),
                  ~10 local iterations, sorry-skeleton-first.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (F : Fin 3 → Finset E) (e : E),
  (∀ i j : Fin 3, i ≠ j → Disjoint (F i) (F j)) →
  (∀ i : Fin 3, ∀ h ∈ F i, ¬ Relation.ReflTransGen
    (fun a b => ∃ s ∈ (F i).erase h,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
    (endAt h 0) (endAt h 1)) →
  (∀ F' : Fin 3 → Finset E, (∀ i j : Fin 3, i ≠ j → Disjoint (F' i) (F' j)) →
    (∀ i : Fin 3, ∀ h ∈ F' i, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ (F' i).erase h,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt h 0) (endAt h 1)) →
    (∑ i : Fin 3, (F' i).card) ≤ ∑ i : Fin 3, (F i).card) →
  (∀ i : Fin 3, e ∉ F i) →
  ∃ P : V → Prop,
    P (endAt e 0) ∧ P (endAt e 1) ∧
    ∀ i : Fin 3, ∀ u v : V, P u → P v →
      Relation.ReflTransGen (fun a b => P a ∧ P b ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v := by
  intro V E _ _ _ _ endAt F e hdisj hforest hmax hefree
  have walk_symm : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (T : Finset E) (p q : V),
    Relation.ReflTransGen
      (fun a b => ∃ s ∈ T,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q →
    Relation.ReflTransGen
      (fun a b => ∃ s ∈ T,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) q p := by
    intro V E _ _ _ _ endAt T p q hw
    refine Relation.ReflTransGen.head_induction_on hw ?_ ?_
    · exact Relation.ReflTransGen.refl
    · rintro a c ⟨s, hs, hends⟩ hcq ih
      refine ih.trans (Relation.ReflTransGen.single ⟨s, hs, ?_⟩)
      rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact Or.inl ⟨h0, h1⟩
  have subst_lemma : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (W : Finset E) (f : E) (x y : V),
    Relation.ReflTransGen
      (fun a b => ∃ s ∈ insert f W,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) x y →
    Relation.ReflTransGen
      (fun a b => ∃ s ∈ W,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) x y ∨
    ((Relation.ReflTransGen (fun a b => ∃ s ∈ W,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) x (endAt f 0) ∧
      Relation.ReflTransGen (fun a b => ∃ s ∈ W,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) (endAt f 1) y) ∨
     (Relation.ReflTransGen (fun a b => ∃ s ∈ W,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) x (endAt f 1) ∧
      Relation.ReflTransGen (fun a b => ∃ s ∈ W,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) (endAt f 0) y)) := by
    intro V E _ _ _ _ endAt W f x y hwalk
    refine Relation.ReflTransGen.head_induction_on hwalk ?_ ?_
    · exact Or.inl Relation.ReflTransGen.refl
    · rintro a b ⟨s, hsW, hends⟩ hbv ih
      rcases Finset.mem_insert.mp hsW with rfl | hsW'
      · rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · subst h0; subst h1
          rcases ih with ihW | ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩
          · exact Or.inr (Or.inl ⟨Relation.ReflTransGen.refl, ihW⟩)
          · exact Or.inr (Or.inl ⟨Relation.ReflTransGen.refl, ih2⟩)
          · exact Or.inl ih2
        · subst h0; subst h1
          rcases ih with ihW | ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩
          · exact Or.inr (Or.inr ⟨Relation.ReflTransGen.refl, ihW⟩)
          · exact Or.inl ih2
          · exact Or.inr (Or.inr ⟨Relation.ReflTransGen.refl, ih2⟩)
      · have hstep : Relation.ReflTransGen (fun a b => ∃ s ∈ W,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) a b :=
          Relation.ReflTransGen.single ⟨s, hsW', hends⟩
        rcases ih with ihW | ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩
        · exact Or.inl (hstep.trans ihW)
        · exact Or.inr (Or.inl ⟨hstep.trans ih1, ih2⟩)
        · exact Or.inr (Or.inr ⟨hstep.trans ih1, ih2⟩)
  have exchange_forest : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (W : Finset E) (f g : E),
    (∀ h ∈ W, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ W.erase h,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt h 0) (endAt h 1)) →
    f ∉ W → g ∈ W →
    ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ W.erase g,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt f 0) (endAt f 1) →
    ∀ h ∈ insert f (W.erase g), ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ (insert f (W.erase g)).erase h,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt h 0) (endAt h 1) := by
    intro V E _ _ _ _ endAt W f g hforest hfW hgW hbridge h hh hwalk
    have hfWg : f ∉ W.erase g := fun hmem => hfW (Finset.mem_of_mem_erase hmem)
    rcases Finset.mem_insert.mp hh with rfl | hh'
    · rw [Finset.erase_insert hfWg] at hwalk
      exact hbridge hwalk
    · have hhg : h ≠ g := (Finset.mem_erase.mp hh').1
      have hhW : h ∈ W := (Finset.mem_erase.mp hh').2
      have hhf : f ≠ h := fun hEq => hfW (hEq ▸ hhW)
      rw [Finset.erase_insert_of_ne hhf] at hwalk
      have hsub : ∀ (p q : V), Relation.ReflTransGen
          (fun a b => ∃ s ∈ (W.erase g).erase h,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q →
          Relation.ReflTransGen
          (fun a b => ∃ s ∈ W.erase g,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q := by
        intro p q hw
        refine Relation.ReflTransGen.mono ?_ hw
        rintro a b ⟨s, hs, hends⟩
        exact ⟨s, Finset.mem_of_mem_erase hs, hends⟩
      have hsub2 : ∀ (p q : V), Relation.ReflTransGen
          (fun a b => ∃ s ∈ (W.erase g).erase h,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q →
          Relation.ReflTransGen
          (fun a b => ∃ s ∈ W.erase h,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q := by
        intro p q hw
        refine Relation.ReflTransGen.mono ?_ hw
        rintro a b ⟨s, hs, hends⟩
        refine ⟨s, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hs).1, ?_⟩, hends⟩
        exact Finset.mem_of_mem_erase (Finset.mem_erase.mp hs).2
      have hhstep : Relation.ReflTransGen
          (fun a b => ∃ s ∈ W.erase g,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
          (endAt h 0) (endAt h 1) :=
        Relation.ReflTransGen.single ⟨h, Finset.mem_erase.mpr ⟨hhg, hhW⟩, Or.inl ⟨rfl, rfl⟩⟩
      rcases subst_lemma V E endAt ((W.erase g).erase h) f (endAt h 0) (endAt h 1) hwalk with
        hW | ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩
      · exact hforest h hhW (hsub2 _ _ hW)
      · -- h0 ⇝ f0 and f1 ⇝ h1 avoiding f, g, h: reroute f's ends through h
        refine hbridge (((walk_symm V E endAt (W.erase g) _ _ (hsub _ _ ih1)).trans
          hhstep).trans (walk_symm V E endAt (W.erase g) _ _ (hsub _ _ ih2)))
      · refine hbridge ((hsub _ _ ih2).trans
          ((walk_symm V E endAt (W.erase g) _ _ hhstep).trans (hsub _ _ ih1)))
  have insert_forest : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V) (W : Finset E) (f : E),
    (∀ h ∈ W, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ W.erase h,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt h 0) (endAt h 1)) →
    f ∉ W →
    ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ W,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt f 0) (endAt f 1) →
    ∀ h ∈ insert f W, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ (insert f W).erase h,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt h 0) (endAt h 1) := by
    intro V E _ _ _ _ endAt W f hforest hfW hnc h hh hwalk
    rcases Finset.mem_insert.mp hh with rfl | hhW
    · rw [Finset.erase_insert hfW] at hwalk
      exact hnc hwalk
    · have hhf : f ≠ h := fun hEq => hfW (hEq ▸ hhW)
      rw [Finset.erase_insert_of_ne hhf] at hwalk
      have hemb : ∀ (p q : V), Relation.ReflTransGen
          (fun a b => ∃ s ∈ W.erase h,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q →
          Relation.ReflTransGen
          (fun a b => ∃ s ∈ W,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q := by
        intro p q hw
        refine Relation.ReflTransGen.mono ?_ hw
        rintro a b ⟨s, hs, hends⟩
        exact ⟨s, Finset.mem_of_mem_erase hs, hends⟩
      have hstepF : Relation.ReflTransGen
          (fun a b => ∃ s ∈ W,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
          (endAt h 0) (endAt h 1) :=
        Relation.ReflTransGen.single ⟨h, hhW, Or.inl ⟨rfl, rfl⟩⟩
      rcases subst_lemma V E endAt (W.erase h) f _ _ hwalk with hW | ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩
      · exact hforest h hhW hW
      · exact hnc (((walk_symm V E endAt W _ _ (hemb _ _ ih1)).trans hstepF).trans
          (walk_symm V E endAt W _ _ (hemb _ _ ih2)))
      · exact hnc ((hemb _ _ ih2).trans
          ((walk_symm V E endAt W _ _ hstepF).trans (hemb _ _ ih1)))
  set ExStep : (Fin 3 → Finset E) → (Fin 3 → Finset E) → Prop :=
    fun G G' => ∃ f : E, ∃ i : Fin 3, ∃ g : E, (∀ j : Fin 3, f ∉ G j) ∧ g ∈ G i ∧
      ¬ Relation.ReflTransGen (fun a b => ∃ s ∈ (G i).erase g,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
        (endAt f 0) (endAt f 1) ∧
      G' = fun j => if j = i then insert f ((G i).erase g) else G j
    with hExStep
  set Reach : (Fin 3 → Finset E) → Prop :=
    fun G => Relation.ReflTransGen ExStep F G with hReach
  set UU : V → Prop := fun v => Relation.ReflTransGen
    (fun a b => ∃ G, Reach G ∧ ∃ f : E, (∀ j : Fin 3, f ∉ G j) ∧
      ((endAt f 0 = a ∧ endAt f 1 = b) ∨ (endAt f 0 = b ∧ endAt f 1 = a)))
    (endAt e 0) v with hUU
  have hUUiff : ∀ w : V, UU w ↔ Relation.ReflTransGen
      (fun a b => ∃ G, Reach G ∧ ∃ f : E, (∀ j : Fin 3, f ∉ G j) ∧
        ((endAt f 0 = a ∧ endAt f 1 = b) ∨ (endAt f 0 = b ∧ endAt f 1 = a)))
      (endAt e 0) w := fun w => Iff.rfl
  -- Part 1: structural invariants along Reach
  have hinv : ∀ G, Reach G →
      (∀ i j : Fin 3, i ≠ j → Disjoint (G i) (G j)) ∧
      (∀ i : Fin 3, ∀ h ∈ G i, ¬ Relation.ReflTransGen
        (fun a b => ∃ s ∈ (G i).erase h,
          (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
        (endAt h 0) (endAt h 1)) ∧
      (∀ i : Fin 3, (G i).card = (F i).card) := by
    intro G hG
    rw [hReach] at hG
    induction hG with
    | refl => exact ⟨hdisj, hforest, fun i => rfl⟩
    | @tail G' G'' hFG' hstep ih =>
        obtain ⟨hdisj', hfor', hcard'⟩ := ih
        rw [hExStep] at hstep
        obtain ⟨f, i, g, hffree, hgmem, hbridge, hGdef⟩ := hstep
        have hG''i : G'' i = insert f ((G' i).erase g) := by rw [hGdef]; simp
        have hG''ne : ∀ j : Fin 3, j ≠ i → G'' j = G' j := by
          intro j hj
          rw [hGdef]
          simp [hj]
        have hfnotin : f ∉ (G' i).erase g := fun hm => hffree i (Finset.mem_of_mem_erase hm)
        refine ⟨?_, ?_, ?_⟩
        · intro a b hab
          rcases eq_or_ne a i with rfl | ha
          · rw [hG''i, hG''ne b (fun hb => hab hb.symm)]
            refine Finset.disjoint_left.mpr ?_
            intro x hxa hxb
            rcases Finset.mem_insert.mp hxa with rfl | hxa'
            · exact hffree b hxb
            · exact Finset.disjoint_left.mp (hdisj' a b hab)
                (Finset.mem_of_mem_erase hxa') hxb
          · rcases eq_or_ne b i with rfl | hb
            · rw [hG''i, hG''ne a ha]
              refine Finset.disjoint_left.mpr ?_
              intro x hxa hxb
              rcases Finset.mem_insert.mp hxb with rfl | hxb'
              · exact hffree a hxa
              · exact Finset.disjoint_left.mp (hdisj' a b hab) hxa
                  (Finset.mem_of_mem_erase hxb')
            · rw [hG''ne a ha, hG''ne b hb]
              exact hdisj' a b hab
        · intro a
          rcases eq_or_ne a i with rfl | ha
          · rw [hG''i]
            exact exchange_forest V E endAt (G' a) f g (hfor' a) (hffree a) hgmem hbridge
          · rw [hG''ne a ha]
            exact hfor' a
        · intro a
          rcases eq_or_ne a i with rfl | ha
          · rw [hG''i, Finset.card_insert_of_notMem hfnotin,
              Finset.card_erase_of_mem hgmem]
            have hpos : 0 < (G' a).card := Finset.card_pos.mpr ⟨g, hgmem⟩
            have := hcard' a
            omega
          · rw [hG''ne a ha]
            exact hcard' a
  -- Part 2: ends of free edges are connected in every coordinate (maximality)
  have hfe : ∀ G, Reach G → ∀ f : E, (∀ j : Fin 3, f ∉ G j) → ∀ i : Fin 3,
      Relation.ReflTransGen (fun a b => ∃ s ∈ G i,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
      (endAt f 0) (endAt f 1) := by
    intro G hG f hffree i
    by_contra hnc
    obtain ⟨hdisjG, hforG, hcardG⟩ := hinv G hG
    set G2 : Fin 3 → Finset E := fun j => if j = i then insert f (G i) else G j with hG2
    have hG2i : G2 i = insert f (G i) := by rw [hG2]; simp
    have hG2ne : ∀ j : Fin 3, j ≠ i → G2 j = G j := by
      intro j hj
      rw [hG2]
      simp [hj]
    have hdisj2 : ∀ a b : Fin 3, a ≠ b → Disjoint (G2 a) (G2 b) := by
      intro a b hab
      rcases eq_or_ne a i with rfl | ha
      · rw [hG2i, hG2ne b (fun hb => hab hb.symm)]
        refine Finset.disjoint_left.mpr ?_
        intro x hxa hxb
        rcases Finset.mem_insert.mp hxa with rfl | hxa'
        · exact hffree b hxb
        · exact Finset.disjoint_left.mp (hdisjG a b hab) hxa' hxb
      · rcases eq_or_ne b i with rfl | hb
        · rw [hG2i, hG2ne a ha]
          refine Finset.disjoint_left.mpr ?_
          intro x hxa hxb
          rcases Finset.mem_insert.mp hxb with rfl | hxb'
          · exact hffree a hxa
          · exact Finset.disjoint_left.mp (hdisjG a b hab) hxa hxb'
        · rw [hG2ne a ha, hG2ne b hb]
          exact hdisjG a b hab
    have hfor2 : ∀ a : Fin 3, ∀ h ∈ G2 a, ¬ Relation.ReflTransGen
        (fun x y => ∃ s ∈ (G2 a).erase h,
          (endAt s 0 = x ∧ endAt s 1 = y) ∨ (endAt s 0 = y ∧ endAt s 1 = x))
        (endAt h 0) (endAt h 1) := by
      intro a
      rcases eq_or_ne a i with rfl | ha
      · rw [hG2i]
        exact insert_forest V E endAt (G a) f (hforG a) (hffree a) hnc
      · rw [hG2ne a ha]
        exact hforG a
    have hle := hmax G2 hdisj2 hfor2
    have key : ∀ (H : Fin 3 → Finset E), (∑ j : Fin 3, (H j).card) =
        (H i).card + ∑ j ∈ Finset.univ.erase i, (H j).card := by
      intro H
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : (∑ j ∈ Finset.univ.erase i, (G2 j).card) =
        ∑ j ∈ Finset.univ.erase i, (G j).card :=
      Finset.sum_congr rfl (fun j hj => by rw [hG2ne j (Finset.ne_of_mem_erase hj)])
    have hcard2 : (G2 i).card = (G i).card + 1 := by
      rw [hG2i, Finset.card_insert_of_notMem (hffree i)]
    have hGF : (∑ j : Fin 3, (G j).card) = ∑ j : Fin 3, (F j).card :=
      Finset.sum_congr rfl (fun j _ => hcardG j)
    have h1 := key G2
    have h2 := key G
    omega
  -- Part 3: CLAIM-A — free-edge ends are connected within UU
  have hA : ∀ G, Reach G → ∀ f : E, (∀ j : Fin 3, f ∉ G j) → UU (endAt f 0) →
      ∀ i : Fin 3, Relation.ReflTransGen
        (fun a b => UU a ∧ UU b ∧ ∃ t ∈ G i,
          (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a))
        (endAt f 0) (endAt f 1) := by
    intro G hG f hffree hf0U i
    obtain ⟨hdisjG, hforG, hcardG⟩ := hinv G hG
    have hconn := hfe G hG f hffree i
    suffices HA : ∀ T : Finset E, T ⊆ G i → Relation.ReflTransGen
        (fun a b => ∃ s ∈ T,
          (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
        (endAt f 0) (endAt f 1) →
        Relation.ReflTransGen
        (fun a b => UU a ∧ UU b ∧ ∃ t ∈ G i,
          (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a))
        (endAt f 0) (endAt f 1) by
      exact HA (G i) Finset.Subset.rfl hconn
    intro T
    refine Finset.strongInductionOn T ?_
    intro T ihT hTsub hTconn
    by_cases hmin : ∃ g ∈ T, Relation.ReflTransGen
        (fun a b => ∃ s ∈ T.erase g,
          (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
        (endAt f 0) (endAt f 1)
    · obtain ⟨g, hgT, hg⟩ := hmin
      exact ihT (T.erase g) (Finset.erase_ssubset hgT)
        ((Finset.erase_subset _ _).trans hTsub) hg
    · have hminall : ∀ g ∈ T, ¬ Relation.ReflTransGen
          (fun a b => ∃ s ∈ T.erase g,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
          (endAt f 0) (endAt f 1) := fun g hg hc => hmin ⟨g, hg, hc⟩
      have hembTG : ∀ (g : E) (p q : V), Relation.ReflTransGen
          (fun a b => ∃ s ∈ T.erase g,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q →
          Relation.ReflTransGen
          (fun a b => ∃ s ∈ (G i).erase g,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) p q := by
        intro g p q hw
        refine Relation.ReflTransGen.mono ?_ hw
        rintro a b ⟨s, hs, hends⟩
        exact ⟨s, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hs).1,
          hTsub (Finset.mem_erase.mp hs).2⟩, hends⟩
      have hbridgeall : ∀ g ∈ T, ¬ Relation.ReflTransGen
          (fun a b => ∃ s ∈ (G i).erase g,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
          (endAt f 0) (endAt f 1) := by
        intro g hgT hcg
        have hTconn' := hTconn
        rw [← Finset.insert_erase hgT] at hTconn'
        rcases subst_lemma V E endAt (T.erase g) g _ _ hTconn' with hW | ⟨w1, w2⟩ | ⟨w1, w2⟩
        · exact hminall g hgT hW
        · exact hforG i g (hTsub hgT)
            (((walk_symm V E endAt _ _ _ (hembTG g _ _ w1)).trans hcg).trans
              (walk_symm V E endAt _ _ _ (hembTG g _ _ w2)))
        · exact hforG i g (hTsub hgT)
            ((hembTG g _ _ w2).trans
              ((walk_symm V E endAt _ _ _ hcg).trans (hembTG g _ _ w1)))
      have hchainU : ∀ w : V, Relation.ReflTransGen
          (fun a b => ∃ s ∈ T,
            (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
          (endAt f 0) w →
          UU w ∧ Relation.ReflTransGen
          (fun a b => UU a ∧ UU b ∧ ∃ t ∈ G i,
            (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a))
          (endAt f 0) w := by
        intro w hw
        induction hw with
        | refl => exact ⟨hf0U, Relation.ReflTransGen.refl⟩
        | @tail b c hb hbc ih =>
            obtain ⟨hbU, hbwalk⟩ := ih
            obtain ⟨s, hsT, hends⟩ := hbc
            have hsG : s ∈ G i := hTsub hsT
            have hsf : s ≠ f := fun hEq => hffree i (hEq ▸ hsG)
            set G2 : Fin 3 → Finset E :=
              fun j => if j = i then insert f ((G i).erase s) else G j with hG2def
            have hG2i : G2 i = insert f ((G i).erase s) := by rw [hG2def]; simp
            have hG2ne : ∀ j : Fin 3, j ≠ i → G2 j = G j := by
              intro j hj
              rw [hG2def]
              simp [hj]
            have hstepEx : ExStep G G2 := by
              rw [hExStep]
              exact ⟨f, i, s, hffree, hsG, hbridgeall s hsT, hG2def⟩
            have hG2reach : Reach G2 := by
              rw [hReach] at hG ⊢
              exact hG.tail hstepEx
            have hsfree2 : ∀ j : Fin 3, s ∉ G2 j := by
              intro j
              rcases eq_or_ne j i with rfl | hj
              · rw [hG2i]
                intro hmem
                rcases Finset.mem_insert.mp hmem with hEq | hmem'
                · exact hsf hEq
                · exact (Finset.mem_erase.mp hmem').1 rfl
              · rw [hG2ne j hj]
                exact fun hmem => Finset.disjoint_left.mp
                  (hdisjG i j (fun h => hj h.symm)) hsG hmem
            have hcU : UU c := (hUUiff c).mpr (((hUUiff b).mp hbU).tail
              ⟨G2, hG2reach, s, hsfree2, hends⟩)
            exact ⟨hcU, hbwalk.tail ⟨hbU, hcU, s, hsG, hends⟩⟩
      exact (hchainU (endAt f 1) hTconn).2
  -- small helper: within-UU walks reverse (any edge set)
  have hWUsymm : ∀ (T : Finset E) (p q : V), Relation.ReflTransGen
      (fun a b => UU a ∧ UU b ∧ ∃ t ∈ T,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) p q →
      Relation.ReflTransGen
      (fun a b => UU a ∧ UU b ∧ ∃ t ∈ T,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) q p := by
    intro T p q hw
    refine Relation.ReflTransGen.head_induction_on hw ?_ ?_
    · exact Relation.ReflTransGen.refl
    · rintro a c ⟨ha, hc, t, ht, hends⟩ hcq ih
      refine ih.trans (Relation.ReflTransGen.single ⟨hc, ha, t, ht, ?_⟩)
      rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact Or.inl ⟨h0, h1⟩
  -- small helper: translate a within-UU walk in reachable G to one in F
  have htrans : ∀ G, Reach G → ∀ i : Fin 3, ∀ x y : V, Relation.ReflTransGen
      (fun a b => UU a ∧ UU b ∧ ∃ t ∈ G i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) x y →
      Relation.ReflTransGen
      (fun a b => UU a ∧ UU b ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) x y := by
    intro G hG
    rw [hReach] at hG
    induction hG with
    | refl => exact fun i x y hw => hw
    | @tail G' G'' hFG' hstep ih =>
        intro i x y hw
        rw [hExStep] at hstep
        obtain ⟨f, i0, g, hffree, hgmem, hbridge, hGdef⟩ := hstep
        have hG' : Reach G' := by rw [hReach]; exact hFG'
        rcases eq_or_ne i i0 with rfl | hi
        · have hG''i : G'' i = insert f ((G' i).erase g) := by rw [hGdef]; simp
          refine ih i x y ?_
          rw [hG''i] at hw
          refine Relation.ReflTransGen.head_induction_on hw ?_ ?_
          · exact Relation.ReflTransGen.refl
          · rintro a c ⟨ha, hc, t, ht, hends⟩ hcq ihw
            refine Relation.ReflTransGen.trans ?_ ihw
            rcases Finset.mem_insert.mp ht with rfl | ht'
            · rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
              · have hstepA := hA G' hG' t hffree (by rw [h0]; exact ha) i
                rw [h0, h1] at hstepA
                exact hstepA
              · have hstepA := hA G' hG' t hffree (by rw [h0]; exact hc) i
                rw [h0, h1] at hstepA
                exact hWUsymm _ _ _ hstepA
            · exact Relation.ReflTransGen.single
                ⟨ha, hc, t, Finset.mem_of_mem_erase ht', hends⟩
        · have hG''ne : G'' i = G' i := by rw [hGdef]; simp [hi]
          rw [hG''ne] at hw
          exact ih i x y hw
  -- assembly
  have hUUe1 : UU (endAt e 1) := by
    rw [hUU]
    exact Relation.ReflTransGen.single
      ⟨F, Relation.ReflTransGen.refl, e, hefree, Or.inl ⟨rfl, rfl⟩⟩
  have hUUsymmStep : ∀ p q : V, Relation.ReflTransGen
      (fun a b => ∃ G, Reach G ∧ ∃ f : E, (∀ j : Fin 3, f ∉ G j) ∧
        ((endAt f 0 = a ∧ endAt f 1 = b) ∨ (endAt f 0 = b ∧ endAt f 1 = a))) p q →
      Relation.ReflTransGen
      (fun a b => ∃ G, Reach G ∧ ∃ f : E, (∀ j : Fin 3, f ∉ G j) ∧
        ((endAt f 0 = a ∧ endAt f 1 = b) ∨ (endAt f 0 = b ∧ endAt f 1 = a))) q p := by
    intro p q hw
    refine Relation.ReflTransGen.head_induction_on hw ?_ ?_
    · exact Relation.ReflTransGen.refl
    · rintro a c ⟨G, hG, f, hf, hends⟩ hcq ih
      refine ih.trans (Relation.ReflTransGen.single ⟨G, hG, f, hf, ?_⟩)
      rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact Or.inl ⟨h0, h1⟩
  -- translate a ≈-chain into a within-UU F i walk (start point in UU)
  have hxlat : ∀ i : Fin 3, ∀ p q : V, UU p → Relation.ReflTransGen
      (fun a b => ∃ G, Reach G ∧ ∃ f : E, (∀ j : Fin 3, f ∉ G j) ∧
        ((endAt f 0 = a ∧ endAt f 1 = b) ∨ (endAt f 0 = b ∧ endAt f 1 = a))) p q →
      Relation.ReflTransGen
      (fun a b => UU a ∧ UU b ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) p q := by
    intro i p q hpU hw
    induction hw with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hpb hbc ih =>
        have hbU : UU b := (hUUiff b).mpr (((hUUiff p).mp hpU).trans hpb)
        have hcU : UU c := (hUUiff c).mpr
          (((hUUiff b).mp hbU).tail hbc)
        refine ih.trans ?_
        obtain ⟨G, hG, f, hf, hends⟩ := hbc
        rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
        · have hstep := htrans G hG i _ _ (hA G hG f hf (by rw [h0]; exact hbU) i)
          rw [h0, h1] at hstep
          exact hstep
        · have hstep := htrans G hG i _ _ (hA G hG f hf (by rw [h0]; exact hcU) i)
          rw [h0, h1] at hstep
          exact hWUsymm _ _ _ hstep
  refine ⟨UU, (hUUiff _).mpr Relation.ReflTransGen.refl, hUUe1, ?_⟩
  intro i u v huP hvP
  have hchain : Relation.ReflTransGen
      (fun a b => ∃ G, Reach G ∧ ∃ f : E, (∀ j : Fin 3, f ∉ G j) ∧
        ((endAt f 0 = a ∧ endAt f 1 = b) ∨ (endAt f 0 = b ∧ endAt f 1 = a))) u v :=
    (hUUsymmStep _ _ ((hUUiff u).mp huP)).trans ((hUUiff v).mp hvP)
  exact hxlat i u v huP hchain
