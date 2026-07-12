/-
CDC step 27 — NW-TOP: the Nash-Williams–Tutte tree-packing theorem, k = 3
                (sufficiency): the classifier-form packing condition implies
                three pairwise-disjoint spanning-connected edge sets
                (mirrors CDCLean.hasTreePacking_of_condition /
                 nashWilliamsTutte, NashWilliams.lean 3592–3653, via the
                 Diestel maximum-tuple route; statements of steps 24, 25 and
                 26 as theorem-hypotheses)
Problem version : c5b86842-c29d-48fa-b477-a8a1b3466e3e
Episode         : 24730338-152b-4bf7-bc19-6d742e9d02c6
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : maximum disjoint-forest tuple by Finset.exists_max_image
                  (classical decidability, no decide); per fully-free edge the
                  exchange-lemma predicate (choose!); classifier c =
                  Quotient.out over the EqvGen setoid of "share a free-edge
                  predicate"; fibers internally connected in every forest by
                  EqvGen induction with tagged-walk retag/reversal; crossing
                  edges partition into the three forests (biUnion,
                  card_biUnion, disjoint_filter_filter); the packing condition
                  pins each forest's crossing count at classes−1 (omega), so
                  step 25's equality clause plus step 24 give per-forest
                  spanning connectivity. U := the forest tuple itself.
The conclusion instantiated at edge type E × Fin 2 is exactly step 23's
hypothesis, whose input is step 21's conclusion — closing the 8-flow theorem
for 3-edge-connected multigraphs through steps 21→27→23→22.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ c : V → V, 3 * ((Finset.univ.image c).card - 1) ≤
    (Finset.univ.filter (fun s : E => c (endAt s 0) ≠ c (endAt s 1))).card) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (S : Finset E') (c : V' → V'),
    (∀ u v : V', c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
        (endAt' t 0 = a ∧ endAt' t 1 = b) ∨ (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
    (∀ u v : V', Relation.ReflTransGen
      (fun a b => c a = c b ∨ ∃ t ∈ S,
        (c (endAt' t 0) = c a ∧ c (endAt' t 1) = c b) ∨
        (c (endAt' t 0) = c b ∧ c (endAt' t 1) = c a)) u v) →
    ∀ u v : V', Relation.ReflTransGen
      (fun a b => ∃ t ∈ S,
        (endAt' t 0 = a ∧ endAt' t 1 = b) ∨ (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (S : Finset E') (c : V' → V'),
    (∀ f ∈ S, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ S.erase f,
        (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a))
      (endAt' f 0) (endAt' f 1)) →
    (∀ u v : V', c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
        (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a)) u v) →
    (S.filter (fun s => c (endAt' s 0) ≠ c (endAt' s 1))).card ≤
        (Finset.univ.image c).card - 1 ∧
      ((S.filter (fun s => c (endAt' s 0) ≠ c (endAt' s 1))).card =
          (Finset.univ.image c).card - 1 →
        ∀ u v : V', Relation.ReflTransGen
          (fun a b => c a = c b ∨ ∃ s ∈ S,
            (c (endAt' s 0) = c a ∧ c (endAt' s 1) = c b) ∨
            (c (endAt' s 0) = c b ∧ c (endAt' s 1) = c a)) u v)) →
  (∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (endAt' : E' → Fin 2 → V') (F : Fin 3 → Finset E') (e : E'),
    (∀ i j : Fin 3, i ≠ j → Disjoint (F i) (F j)) →
    (∀ i : Fin 3, ∀ h ∈ F i, ¬ Relation.ReflTransGen
      (fun a b => ∃ s ∈ (F i).erase h,
        (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a))
      (endAt' h 0) (endAt' h 1)) →
    (∀ F' : Fin 3 → Finset E', (∀ i j : Fin 3, i ≠ j → Disjoint (F' i) (F' j)) →
      (∀ i : Fin 3, ∀ h ∈ F' i, ¬ Relation.ReflTransGen
        (fun a b => ∃ s ∈ (F' i).erase h,
          (endAt' s 0 = a ∧ endAt' s 1 = b) ∨ (endAt' s 0 = b ∧ endAt' s 1 = a))
        (endAt' h 0) (endAt' h 1)) →
      (∑ i : Fin 3, (F' i).card) ≤ ∑ i : Fin 3, (F i).card) →
    (∀ i : Fin 3, e ∉ F i) →
    ∃ P : V' → Prop,
      P (endAt' e 0) ∧ P (endAt' e 1) ∧
      ∀ i : Fin 3, ∀ u v : V', P u → P v →
        Relation.ReflTransGen (fun a b => P a ∧ P b ∧ ∃ t ∈ F i,
          (endAt' t 0 = a ∧ endAt' t 1 = b) ∨ (endAt' t 0 = b ∧ endAt' t 1 = a)) u v) →
  ∃ U : Fin 3 → Finset E,
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) := by
  intro V E _ _ _ _ endAt hPC h24 h25 h26
  classical
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun F : Fin 3 → Finset E =>
      (∀ i j : Fin 3, i ≠ j → Disjoint (F i) (F j)) ∧
      (∀ i : Fin 3, ∀ h ∈ F i, ¬ Relation.ReflTransGen
        (fun a b => ∃ s ∈ (F i).erase h,
          (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
        (endAt h 0) (endAt h 1))))
    (fun F : Fin 3 → Finset E => ∑ i : Fin 3, (F i).card)
    ⟨fun _ => ∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun i j hij => Finset.disjoint_empty_left _,
      fun i h hh => absurd hh (Finset.notMem_empty h)⟩⟩
  obtain ⟨-, hdisjF, hforF⟩ := Finset.mem_filter.mp hFmem
  have hmax' : ∀ F' : Fin 3 → Finset E, (∀ i j : Fin 3, i ≠ j → Disjoint (F' i) (F' j)) →
      (∀ i : Fin 3, ∀ h ∈ F' i, ¬ Relation.ReflTransGen
        (fun a b => ∃ s ∈ (F' i).erase h,
          (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
        (endAt h 0) (endAt h 1)) →
      (∑ i : Fin 3, (F' i).card) ≤ ∑ i : Fin 3, (F i).card :=
    fun F' h1 h2 => hFmax F' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
  have hPall : ∀ e : E, (∀ i : Fin 3, e ∉ F i) → ∃ P : V → Prop,
      P (endAt e 0) ∧ P (endAt e 1) ∧
      ∀ i : Fin 3, ∀ u v : V, P u → P v →
        Relation.ReflTransGen (fun a b => P a ∧ P b ∧ ∃ t ∈ F i,
          (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v :=
    fun e he => h26 V E endAt F e hdisjF hforF hmax' he
  choose! Pe hPe0 hPe1 hPec using hPall
  set r : V → V → Prop := fun u v => ∃ s : E, (∀ i : Fin 3, s ∉ F i) ∧ Pe s u ∧ Pe s v
    with hrdef
  set c : V → V := fun v => (Quotient.mk (Relation.EqvGen.setoid r) v).out with hcdef
  have hcv : ∀ v : V, c v = (Quotient.mk (Relation.EqvGen.setoid r) v).out := fun _ => rfl
  have hceq : ∀ u v : V, c u = c v ↔ Relation.EqvGen r u v := by
    intro u v
    constructor
    · intro h
      rw [hcv, hcv] at h
      have h2 := congrArg (Quotient.mk (Relation.EqvGen.setoid r)) h
      rw [Quotient.out_eq, Quotient.out_eq] at h2
      exact Quotient.exact h2
    · intro h
      rw [hcv, hcv]
      exact congrArg Quotient.out (Quotient.sound h)
  have hretag : ∀ (i : Fin 3) (K K' p q : V), c K = c K' → Relation.ReflTransGen
      (fun a b => c a = c K ∧ c b = c K ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) p q →
      Relation.ReflTransGen
      (fun a b => c a = c K' ∧ c b = c K' ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) p q := by
    intro i K K' p q hKK hw
    refine Relation.ReflTransGen.mono ?_ hw
    rintro a b ⟨ha, hb, ht⟩
    exact ⟨ha.trans hKK, hb.trans hKK, ht⟩
  have hrevt : ∀ (i : Fin 3) (K p q : V), Relation.ReflTransGen
      (fun a b => c a = c K ∧ c b = c K ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) p q →
      Relation.ReflTransGen
      (fun a b => c a = c K ∧ c b = c K ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) q p := by
    intro i K p q hw
    refine Relation.ReflTransGen.head_induction_on hw ?_ ?_
    · exact Relation.ReflTransGen.refl
    · rintro a b ⟨ha, hb, t, ht, hends⟩ hbq ih
      refine ih.trans (Relation.ReflTransGen.single ⟨hb, ha, t, ht, ?_⟩)
      rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exact Or.inl ⟨h0, h1⟩
  have hEqvWalk : ∀ (i : Fin 3) (u v : V), Relation.EqvGen r u v →
      Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ F i,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v := by
    intro i u v h
    induction h with
    | rel x y hxy =>
        obtain ⟨s, hsfree, hPx, hPy⟩ := hxy
        have hw := hPec s hsfree i x y hPx hPy
        refine Relation.ReflTransGen.mono ?_ hw
        rintro a b ⟨hPa, hPb, ht⟩
        refine ⟨?_, ?_, ht⟩
        · exact (hceq a x).mpr (Relation.EqvGen.rel a x ⟨s, hsfree, hPa, hPx⟩)
        · exact (hceq b x).mpr (Relation.EqvGen.rel b x ⟨s, hsfree, hPb, hPx⟩)
    | refl x => exact Relation.ReflTransGen.refl
    | symm x y hxy ih =>
        have hcxy : c x = c y := (hceq x y).mpr hxy
        exact hretag i x y _ _ hcxy (hrevt i x _ _ ih)
    | trans x y z hxy hyz ih1 ih2 =>
        have hcxy : c x = c y := (hceq x y).mpr hxy
        exact ih1.trans (hretag i y x _ _ hcxy.symm ih2)
  have hint : ∀ i : Fin 3, ∀ u v : V, c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ F i,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v :=
    fun i u v huv => hEqvWalk i u v ((hceq u v).mp huv)
  have hfreein : ∀ s : E, (∀ i : Fin 3, s ∉ F i) → c (endAt s 0) = c (endAt s 1) :=
    fun s hs => (hceq _ _).mpr (Relation.EqvGen.rel _ _ ⟨s, hs, hPe0 s hs, hPe1 s hs⟩)
  have hcover : Finset.univ.filter (fun s : E => c (endAt s 0) ≠ c (endAt s 1)) =
      Finset.univ.biUnion (fun i : Fin 3 =>
        (F i).filter (fun s => c (endAt s 0) ≠ c (endAt s 1))) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hs
      by_cases hfree : ∀ i : Fin 3, s ∉ F i
      · exact absurd (hfreein s hfree) hs
      · obtain ⟨i, hi⟩ := not_forall.mp hfree
        exact ⟨i, not_not.mp hi, hs⟩
    · rintro ⟨i, hsi, hcross⟩
      exact hcross
  have hcardsum : (Finset.univ.filter (fun s : E => c (endAt s 0) ≠ c (endAt s 1))).card =
      ∑ i : Fin 3, ((F i).filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card := by
    rw [hcover]
    exact Finset.card_biUnion (fun i _ j _ hij =>
      Finset.disjoint_filter_filter (hdisjF i j hij))
  obtain ⟨hb0, he0⟩ := h25 V E endAt (F 0) c (hforF 0) (hint 0)
  obtain ⟨hb1, he1⟩ := h25 V E endAt (F 1) c (hforF 1) (hint 1)
  obtain ⟨hb2, he2⟩ := h25 V E endAt (F 2) c (hforF 2) (hint 2)
  have hPCc := hPC c
  rw [hcardsum, Fin.sum_univ_three] at hPCc
  have heq0 : ((F 0).filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
      (Finset.univ.image c).card - 1 := by omega
  have heq1 : ((F 1).filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
      (Finset.univ.image c).card - 1 := by omega
  have heq2 : ((F 2).filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
      (Finset.univ.image c).card - 1 := by omega
  have hconn0 := h24 V E endAt (F 0) c (hint 0) (he0 heq0)
  have hconn1 := h24 V E endAt (F 1) c (hint 1) (he1 heq1)
  have hconn2 := h24 V E endAt (F 2) c (hint 2) (he2 heq2)
  refine ⟨F, hdisjF, ?_⟩
  intro i
  fin_cases i
  · exact hconn0
  · exact hconn1
  · exact hconn2
