# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Jaeger 8-flow, composition step JK-E-2a (bundles steps 21 + 27 + 24 + 25 + 26 into a clean single-conclusion link): if a finite multigraph is 3-edge-connected (nonempty-proper cuts have card ≥ 3), then its doubled multigraph (edges E × Fin 2) carries three pairwise-disjoint spanning-connected edge sets. Takes the verified root statements of step 21 (doubled packing condition, cd0a7b4a), step 24 (internal+quotient connectivity glue, 39c57ce0), step 25 (forest crossing count, 5341018f), step 26 (exchange lemma, 3632c255), and step 27 (Nash-Williams tree packing, c5b86842) as theorem-hypotheses. Proof is a single application: h21 turns 3EC into the classifier-form packing condition of the doubled graph, and h27 (fed h24, h25, h26 as its own hypotheses) turns that packing condition into the disjoint-connected tuple, instantiated at edge type E × Fin 2 with endAt' p = endAt p.1. This is the doubled-graph packing half of the 8-flow-for-3EC chain; its conclusion is exactly the hypothesis shape of step 23 (doubled-packing projection). Pre-flighted clean first try on the pinned lean-checker; statement 6.5KB.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ f ∈ S, ¬ Relation.ReflTransGen
    (fun a b => ∃ s ∈ S.erase f,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
    (endAt f 0) (endAt f 1)) →
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
  (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card ≤
      (Finset.univ.image c).card - 1 ∧
    ((S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
        (Finset.univ.image c).card - 1 →
      ∀ u v : V, Relation.ReflTransGen
        (fun a b => c a = c b ∨ ∃ s ∈ S,
          (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v)) →
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ U : Fin 3 → Finset (E × Fin 2),
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
        (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ f ∈ S, ¬ Relation.ReflTransGen
    (fun a b => ∃ s ∈ S.erase f,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
    (endAt f 0) (endAt f 1)) →
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
  (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card ≤
      (Finset.univ.image c).card - 1 ∧
    ((S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
        (Finset.univ.image c).card - 1 →
      ∀ u v : V, Relation.ReflTransGen
        (fun a b => c a = c b ∨ ∃ s ∈ S,
          (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v)) →
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ U : Fin 3 → Finset (E × Fin 2),
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
        (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `6bc3de88-43b8-4688-8ab4-d51377e6009b` | terminated (root_proved) | 1 | — | 2026-07-11T22:25:53 | 2026-07-11T22:26:48 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ f ∈ S, ¬ Relation.ReflTransGen
    (fun a b => ∃ s ∈ S.erase f,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
    (endAt f 0) (endAt f 1)) →
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
  (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card ≤
      (Finset.univ.image c).card - 1 ∧
    ((S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
        (Finset.univ.image c).card - 1 →
      ∀ u v : V, Relation.ReflTransGen
        (fun a b => c a = c b ∨ ∃ s ∈ S,
          (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v)) →
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ U : Fin 3 → Finset (E × Fin 2),
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
        (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V),
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∀ c : V → V,
    3 * ((Finset.univ.image c).card - 1) ≤
      (Finset.univ.filter (fun p : E × Fin 2 =>
        c (endAt p.1 0) ≠ c (endAt p.1 1))).card) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ u v : V, Relation.ReflTransGen
    (fun a b => c a = c b ∨ ∃ t ∈ S,
      (c (endAt t 0) = c a ∧ c (endAt t 1) = c b) ∨
      (c (endAt t 0) = c b ∧ c (endAt t 1) = c a)) u v) →
  ∀ u v : V, Relation.ReflTransGen
    (fun a b => ∃ t ∈ S,
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V) (S : Finset E) (c : V → V),
  (∀ f ∈ S, ¬ Relation.ReflTransGen
    (fun a b => ∃ s ∈ S.erase f,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a))
    (endAt f 0) (endAt f 1)) →
  (∀ u v : V, c u = c v → Relation.ReflTransGen
    (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
      (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
  (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card ≤
      (Finset.univ.image c).card - 1 ∧
    ((S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card =
        (Finset.univ.image c).card - 1 →
      ∀ u v : V, Relation.ReflTransGen
        (fun a b => c a = c b ∨ ∃ s ∈ S,
          (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v) →
  (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v)) →
  (∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    3 ≤ (Finset.univ.filter (fun e : E =>
      ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card) →
  ∃ U : Fin 3 → Finset (E × Fin 2),
    (∀ i j : Fin 3, i ≠ j → Disjoint (U i) (U j)) ∧
    (∀ i : Fin 3, ∀ u v : V, Relation.ReflTransGen
      (fun a b => ∃ t ∈ U i, (endAt t.1 0 = a ∧ endAt t.1 1 = b) ∨
        (endAt t.1 0 = b ∧ endAt t.1 1 = a)) u v) := by
intro V E _ _ _ _ endAt h21 h24 h25 h26 h27 h3ec
exact h27 V (E × Fin 2) (fun p i => endAt p.1 i) (h21 V E endAt h3ec) h24 h25 h26

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt h21 h24 h25 h26 h27 h3ec ; exact h27 V (E × Fin 2) (fun p i => endAt p.1 i) (h21 V E endAt h3ec) h24 h25 h26` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `c7d39888d846…` → `2df251183c95…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
