# ⚠️ KERNEL-VERIFIED FORMAL STATEMENT — FIDELITY NOT YET VERIFIED — CDC paper / Nash-Williams tree-packing campaign step NW-1 (the forest crossing-count lemma; corresponds to the counting layer of NashWilliams.lean 2573-2691 generalized from spanning trees to forests): let S be a forest (every edge f of S has its ends not connected by S minus f) whose classifier fibers are internally S-connected. Then (i) the number of S-edges crossing between distinct classes of c is at most (number of classes) - 1, and (ii) if that count equals classes - 1, the quotient by c is S-connected (class-closed quotient walks, matching the hypothesis interface of verified step 24 / problem 39c57ce0). Proof by strong induction on the crossing edge set (Finset.strongInductionOn): if no crossing edges, the bound is trivial and equality forces at most one class, so quotient walks are single same-class steps; otherwise pick a crossing edge t and merge its end-classes with the classifier c' v = if c v = c(end1 t) then c(end0 t) else c v. Local have-lemmas: uniqueBridge (a forest has at most one edge between any two classes -- a second one would close a cycle through the two internally-connected fibers, violating forestness of the erased edge), mergeInternal (merged fibers stay internally connected via t), mergeImage (class count drops by exactly one, image-erase), mergeCross (the crossing set loses exactly t, using uniqueBridge for edges that would join the merged pair of classes), quotientLift (quotient connectivity for c' lifts to c: same-c'-class steps become at most one t-crossing step, crossing steps translate edgewise). Arithmetic by omega. Pre-flighted clean on the pinned lean-checker in single-declaration form under set_option maxHeartbeats 200000 (the exact server budget), 3 local iterations.

> This proof establishes:
>
> `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)`
>
> It does **not yet** certify the source claim above.

**Root goal (formal):** `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)`

| Proof soundness | Statement fidelity | Canonical promotion | Training eligibility |
|---|---|---|---|
| VERIFIED | ATTESTED (unsafe_dev_attestation — not reviewed) | BLOCKED | QUARANTINED |

| episode | state | steps | budget left (μ$) | started | finished |
|---|---|---|---|---|---|
| `ad2124ce-817b-42fe-bf43-b99920fad585` | terminated (root_proved) | 1 | — | 2026-07-11T21:21:17 | 2026-07-11T21:23:53 |

## Proof tree

- ✅ **root_theorem** : `∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v)`

## The proof, assembled

```lean
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
          (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v) := by
intro V E _ _ _ _ endAt S c0 hforest hint0
have uniqueBridge : ∀ (c : V → V),
    (∀ u v : V, c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
    ∀ t ∈ S, ∀ t' ∈ S, c (endAt t 0) ≠ c (endAt t 1) →
      ((c (endAt t' 0) = c (endAt t 0) ∧ c (endAt t' 1) = c (endAt t 1)) ∨
       (c (endAt t' 0) = c (endAt t 1) ∧ c (endAt t' 1) = c (endAt t 0))) →
      t' = t := by
  intro c hint t htS t' ht'S htc hshape
  by_contra hne
  have ht'c : c (endAt t' 0) ≠ c (endAt t' 1) := by
    rcases hshape with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1]; exact htc
    · rw [h0, h1]; exact fun h => htc h.symm
  have hlift : ∀ w x : V, c w = c x → Relation.ReflTransGen
      (fun a b => ∃ s ∈ S.erase t',
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) w x := by
    intro w x hwx
    refine Relation.ReflTransGen.mono ?_ (hint w x hwx)
    rintro a b ⟨ha, hb, s, hsS, hends⟩
    refine ⟨s, Finset.mem_erase.mpr ⟨?_, hsS⟩, hends⟩
    rintro rfl
    rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ht'c (by rw [h0, h1, ha, hb])
    · exact ht'c (by rw [h0, h1, hb, ha])
  have htmem : t ∈ S.erase t' := Finset.mem_erase.mpr ⟨fun h => hne h.symm, htS⟩
  rcases hshape with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact hforest t' ht'S (((hlift (endAt t' 0) (endAt t 0) h0).trans
      (Relation.ReflTransGen.single ⟨t, htmem, Or.inl ⟨rfl, rfl⟩⟩)).trans
      (hlift (endAt t 1) (endAt t' 1) h1.symm))
  · exact hforest t' ht'S (((hlift (endAt t' 0) (endAt t 1) h0).trans
      (Relation.ReflTransGen.single ⟨t, htmem, Or.inr ⟨rfl, rfl⟩⟩)).trans
      (hlift (endAt t 0) (endAt t' 1) h1.symm))
have mergeInternal : ∀ (c c' : V → V) (t : E), t ∈ S →
    (∀ u v : V, c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
    (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) →
    ∀ u v : V, c' u = c' v → Relation.ReflTransGen
      (fun a b => c' a = c' u ∧ c' b = c' u ∧ ∃ s ∈ S,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v := by
  intro c c' t htS hint hc' u v huv
  have hfib : ∀ a b : V, c a = c b → c' a = c' b := by
    intro a b hab
    rw [hc' a, hc' b, hab]
  have hemb : ∀ w x : V, c w = c x → c' w = c' u → Relation.ReflTransGen
      (fun a b => c' a = c' u ∧ c' b = c' u ∧ ∃ s ∈ S,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) w x := by
    intro w x hwx hwu
    refine Relation.ReflTransGen.mono ?_ (hint w x hwx)
    rintro a b ⟨ha, hb, hs⟩
    exact ⟨(hfib a w ha).trans hwu, (hfib b w hb).trans hwu, hs⟩
  have hc'A : c' (endAt t 0) = c (endAt t 0) := by
    rw [hc' (endAt t 0)]
    by_cases h : c (endAt t 0) = c (endAt t 1)
    · rw [if_pos h]
    · rw [if_neg h]
  have hc'B : c' (endAt t 1) = c (endAt t 0) := by
    rw [hc' (endAt t 1), if_pos rfl]
  by_cases hcc : c u = c v
  · exact hemb u v hcc rfl
  · rw [hc' u, hc' v] at huv
    by_cases hu : c u = c (endAt t 1) <;> by_cases hv : c v = c (endAt t 1)
    · exact absurd (hu.trans hv.symm) hcc
    · rw [if_pos hu, if_neg hv] at huv
      have hc'u : c' u = c (endAt t 0) := by rw [hc' u, if_pos hu]
      refine ((hemb u (endAt t 1) hu rfl).trans
        (Relation.ReflTransGen.single
          ⟨hc'B.trans hc'u.symm, hc'A.trans hc'u.symm, t, htS, Or.inr ⟨rfl, rfl⟩⟩)).trans
        (hemb (endAt t 0) v huv (hc'A.trans hc'u.symm))
    · rw [if_neg hu, if_pos hv] at huv
      have hc'u : c' u = c (endAt t 0) := by rw [hc' u, if_neg hu]; exact huv
      refine ((hemb u (endAt t 0) huv rfl).trans
        (Relation.ReflTransGen.single
          ⟨hc'A.trans hc'u.symm, hc'B.trans hc'u.symm, t, htS, Or.inl ⟨rfl, rfl⟩⟩)).trans
        (hemb (endAt t 1) v hv.symm (hc'B.trans hc'u.symm))
    · rw [if_neg hu, if_neg hv] at huv
      exact absurd huv hcc
have mergeImage : ∀ (c c' : V → V) (t : E),
    c (endAt t 0) ≠ c (endAt t 1) →
    (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) →
    (Finset.univ.image c').card = (Finset.univ.image c).card - 1 := by
  intro c c' t htc hc'
  have himg : Finset.univ.image c' = (Finset.univ.image c).erase (c (endAt t 1)) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw⟩
      rw [hc' w] at hw
      by_cases h : c w = c (endAt t 1)
      · rw [if_pos h] at hw
        refine ⟨?_, ⟨endAt t 0, hw⟩⟩
        rw [← hw]; exact htc
      · rw [if_neg h] at hw
        refine ⟨?_, ⟨w, hw⟩⟩
        rw [← hw]; exact h
    · rintro ⟨hxB, w, hw⟩
      refine ⟨w, ?_⟩
      rw [hc' w, if_neg ?_]
      · exact hw
      · rw [hw]; exact hxB
  rw [himg, Finset.card_erase_of_mem (Finset.mem_image_of_mem c (Finset.mem_univ _))]
have mergeCross : ∀ (c c' : V → V) (t : E),
    (∀ u v : V, c u = c v → Relation.ReflTransGen
      (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S,
        (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) →
    t ∈ S → c (endAt t 0) ≠ c (endAt t 1) →
    (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) →
    S.filter (fun s => c' (endAt s 0) ≠ c' (endAt s 1)) =
      (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).erase t := by
  intro c c' t hint htS htc hc'
  have hc'A : c' (endAt t 0) = c (endAt t 0) := by
    rw [hc' (endAt t 0)]
    by_cases h : c (endAt t 0) = c (endAt t 1)
    · rw [if_pos h]
    · rw [if_neg h]
  have hc'B : c' (endAt t 1) = c (endAt t 0) := by
    rw [hc' (endAt t 1), if_pos rfl]
  ext s
  simp only [Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨hsS, hs⟩
    refine ⟨?_, hsS, ?_⟩
    · rintro rfl
      exact hs (hc'A.trans hc'B.symm)
    · intro h
      exact hs (by rw [hc' (endAt s 0), hc' (endAt s 1), h])
  · rintro ⟨hst, hsS, hs⟩
    refine ⟨hsS, ?_⟩
    intro h
    rw [hc' (endAt s 0), hc' (endAt s 1)] at h
    by_cases h0 : c (endAt s 0) = c (endAt t 1) <;>
      by_cases h1 : c (endAt s 1) = c (endAt t 1)
    · exact hs (h0.trans h1.symm)
    · rw [if_pos h0, if_neg h1] at h
      exact hst (uniqueBridge c hint t htS s hsS htc (Or.inr ⟨h0, h.symm⟩))
    · rw [if_neg h0, if_pos h1] at h
      exact hst (uniqueBridge c hint t htS s hsS htc (Or.inl ⟨h, h1⟩))
    · rw [if_neg h0, if_neg h1] at h
      exact hs h
have quotientLift : ∀ (c c' : V → V) (t : E), t ∈ S →
    (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) →
    (∀ u v : V, Relation.ReflTransGen
      (fun a b => c' a = c' b ∨ ∃ s ∈ S,
        (c' (endAt s 0) = c' a ∧ c' (endAt s 1) = c' b) ∨
        (c' (endAt s 0) = c' b ∧ c' (endAt s 1) = c' a)) u v) →
    ∀ u v : V, Relation.ReflTransGen
      (fun a b => c a = c b ∨ ∃ s ∈ S,
        (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨
        (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v := by
  intro c c' t htS hc' hq u v
  have hone : ∀ a b : V, c' a = c' b → Relation.ReflTransGen
      (fun a b => c a = c b ∨ ∃ s ∈ S,
        (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨
        (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) a b := by
    intro a b hab
    by_cases hcc : c a = c b
    · exact Relation.ReflTransGen.single (Or.inl hcc)
    · rw [hc' a, hc' b] at hab
      by_cases ha : c a = c (endAt t 1) <;> by_cases hb : c b = c (endAt t 1)
      · exact absurd (ha.trans hb.symm) hcc
      · rw [if_pos ha, if_neg hb] at hab
        exact Relation.ReflTransGen.single (Or.inr ⟨t, htS, Or.inr ⟨hab, ha.symm⟩⟩)
      · rw [if_neg ha, if_pos hb] at hab
        exact Relation.ReflTransGen.single (Or.inr ⟨t, htS, Or.inl ⟨hab.symm, hb.symm⟩⟩)
      · rw [if_neg ha, if_neg hb] at hab
        exact absurd hab hcc
  refine Relation.ReflTransGen.head_induction_on (hq u v) ?_ ?_
  · exact Relation.ReflTransGen.refl
  · rintro a b hab hbv ih
    rcases hab with hab | ⟨s, hsS, hends⟩
    · exact (hone a b hab).trans ih
    · have hmid : Relation.ReflTransGen
          (fun a b => c a = c b ∨ ∃ s' ∈ S,
            (c (endAt s' 0) = c a ∧ c (endAt s' 1) = c b) ∨
            (c (endAt s' 0) = c b ∧ c (endAt s' 1) = c a)) (endAt s 0) (endAt s 1) :=
        Relation.ReflTransGen.single (Or.inr ⟨s, hsS, Or.inl ⟨rfl, rfl⟩⟩)
      have hmid' : Relation.ReflTransGen
          (fun a b => c a = c b ∨ ∃ s' ∈ S,
            (c (endAt s' 0) = c a ∧ c (endAt s' 1) = c b) ∨
            (c (endAt s' 0) = c b ∧ c (endAt s' 1) = c a)) (endAt s 1) (endAt s 0) :=
        Relation.ReflTransGen.single (Or.inr ⟨s, hsS, Or.inr ⟨rfl, rfl⟩⟩)
      rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact (hone a (endAt s 0) h0.symm).trans
          (hmid.trans ((hone (endAt s 1) b h1).trans ih))
      · exact (hone a (endAt s 1) h1.symm).trans
          (hmid'.trans ((hone (endAt s 0) b h0).trans ih))
suffices H : ∀ (X : Finset E) (c : V → V),
    S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1)) = X →
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
            (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v) by
  exact H _ c0 rfl hint0
intro X
refine Finset.strongInductionOn X ?_
intro X ih c hX hintc
by_cases hXe : X = ∅
· subst hXe
  constructor
  · rw [hX]
    exact Nat.zero_le _
  · intro heq u v
    rw [hX, Finset.card_empty] at heq
    have hm1 : (Finset.univ.image c).card ≤ 1 := by omega
    have hcc : c u = c v :=
      Finset.card_le_one.mp hm1 _ (Finset.mem_image_of_mem c (Finset.mem_univ u))
        _ (Finset.mem_image_of_mem c (Finset.mem_univ v))
    exact Relation.ReflTransGen.single (Or.inl hcc)
· obtain ⟨t, htX⟩ := Finset.nonempty_iff_ne_empty.mpr hXe
  have htXf : t ∈ S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1)) := by
    rw [hX]; exact htX
  have htS : t ∈ S := (Finset.mem_filter.mp htXf).1
  have htc : c (endAt t 0) ≠ c (endAt t 1) := (Finset.mem_filter.mp htXf).2
  set c' : V → V := fun v => if c v = c (endAt t 1) then c (endAt t 0) else c v with hc'def
  have hc' : ∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v :=
    fun v => rfl
  have hint' := mergeInternal c c' t htS hintc hc'
  have himg := mergeImage c c' t htc hc'
  have hcrossX : S.filter (fun s => c' (endAt s 0) ≠ c' (endAt s 1)) = X.erase t := by
    rw [mergeCross c c' t hintc htS htc hc', hX]
  have hlt : X.erase t ⊂ X := Finset.erase_ssubset htX
  obtain ⟨hb', he'⟩ := ih (X.erase t) hlt c' hcrossX hint'
  have hm2 : 2 ≤ (Finset.univ.image c).card :=
    Finset.one_lt_card.mpr
      ⟨c (endAt t 0), Finset.mem_image_of_mem c (Finset.mem_univ _),
       c (endAt t 1), Finset.mem_image_of_mem c (Finset.mem_univ _), htc⟩
  have hcardX : X.card = (X.erase t).card + 1 :=
    (Finset.card_erase_add_one htX).symm
  rw [hcrossX, himg] at hb'
  constructor
  · rw [hX]
    omega
  · intro heq
    rw [hX] at heq
    have he2 : (S.filter (fun s => c' (endAt s 0) ≠ c' (endAt s 1))).card =
        (Finset.univ.image c').card - 1 := by
      rw [hcrossX, himg]
      omega
    exact quotientLift c c' t htS hc' (he' he2)

```

## How it went — every attempt, in order

| # | obligation | action | detail | verdict |
|---|---|---|---|---|
| 2 | `root_theorem` | solve | `intro V E _ _ _ _ endAt S c0 hforest hint0 ; have uniqueBridge : ∀ (c : V → V), ;     (∀ u v : V, c u = c v → Relation.ReflTransGen ;       (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S, ;         (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) → ;     ∀ t ∈ S, ∀ t' ∈ S, c (endAt t 0) ≠ c (endAt t 1) → ;       ((c (endAt t' 0) = c (endAt t 0) ∧ c (endAt t' 1) = c (endAt t 1)) ∨ ;        (c (endAt t' 0) = c (endAt t 1) ∧ c (endAt t' 1) = c (endAt t 0))) → ;       t' = t := by ;   intro c hint t htS t' ht'S htc hshape ;   by_contra hne ;   have ht'c : c (endAt t' 0) ≠ c (endAt t' 1) := by ;     rcases hshape with ⟨h0, h1⟩ \| ⟨h0, h1⟩ ;     · rw [h0, h1]; exact htc ;     · rw [h0, h1]; exact fun h => htc h.symm ;   have hlift : ∀ w x : V, c w = c x → Relation.ReflTransGen ;       (fun a b => ∃ s ∈ S.erase t', ;         (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) w x := by ;     intro w x hwx ;     refine Relation.ReflTransGen.mono ?_ (hint w x hwx) ;     rintro a b ⟨ha, hb, s, hsS, hends⟩ ;     refine ⟨s, Finset.mem_erase.mpr ⟨?_, hsS⟩, hends⟩ ;     rintro rfl ;     rcases hends with ⟨h0, h1⟩ \| ⟨h0, h1⟩ ;     · exact ht'c (by rw [h0, h1, ha, hb]) ;     · exact ht'c (by rw [h0, h1, hb, ha]) ;   have htmem : t ∈ S.erase t' := Finset.mem_erase.mpr ⟨fun h => hne h.symm, htS⟩ ;   rcases hshape with ⟨h0, h1⟩ \| ⟨h0, h1⟩ ;   · exact hforest t' ht'S (((hlift (endAt t' 0) (endAt t 0) h0).trans ;       (Relation.ReflTransGen.single ⟨t, htmem, Or.inl ⟨rfl, rfl⟩⟩)).trans ;       (hlift (endAt t 1) (endAt t' 1) h1.symm)) ;   · exact hforest t' ht'S (((hlift (endAt t' 0) (endAt t 1) h0).trans ;       (Relation.ReflTransGen.single ⟨t, htmem, Or.inr ⟨rfl, rfl⟩⟩)).trans ;       (hlift (endAt t 0) (endAt t' 1) h1.symm)) ; have mergeInternal : ∀ (c c' : V → V) (t : E), t ∈ S → ;     (∀ u v : V, c u = c v → Relation.ReflTransGen ;       (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S, ;         (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) → ;     (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) → ;     ∀ u v : V, c' u = c' v → Relation.ReflTransGen ;       (fun a b => c' a = c' u ∧ c' b = c' u ∧ ∃ s ∈ S, ;         (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v := by ;   intro c c' t htS hint hc' u v huv ;   have hfib : ∀ a b : V, c a = c b → c' a = c' b := by ;     intro a b hab ;     rw [hc' a, hc' b, hab] ;   have hemb : ∀ w x : V, c w = c x → c' w = c' u → Relation.ReflTransGen ;       (fun a b => c' a = c' u ∧ c' b = c' u ∧ ∃ s ∈ S, ;         (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) w x := by ;     intro w x hwx hwu ;     refine Relation.ReflTransGen.mono ?_ (hint w x hwx) ;     rintro a b ⟨ha, hb, hs⟩ ;     exact ⟨(hfib a w ha).trans hwu, (hfib b w hb).trans hwu, hs⟩ ;   have hc'A : c' (endAt t 0) = c (endAt t 0) := by ;     rw [hc' (endAt t 0)] ;     by_cases h : c (endAt t 0) = c (endAt t 1) ;     · rw [if_pos h] ;     · rw [if_neg h] ;   have hc'B : c' (endAt t 1) = c (endAt t 0) := by ;     rw [hc' (endAt t 1), if_pos rfl] ;   by_cases hcc : c u = c v ;   · exact hemb u v hcc rfl ;   · rw [hc' u, hc' v] at huv ;     by_cases hu : c u = c (endAt t 1) <;> by_cases hv : c v = c (endAt t 1) ;     · exact absurd (hu.trans hv.symm) hcc ;     · rw [if_pos hu, if_neg hv] at huv ;       have hc'u : c' u = c (endAt t 0) := by rw [hc' u, if_pos hu] ;       refine ((hemb u (endAt t 1) hu rfl).trans ;         (Relation.ReflTransGen.single ;           ⟨hc'B.trans hc'u.symm, hc'A.trans hc'u.symm, t, htS, Or.inr ⟨rfl, rfl⟩⟩)).trans ;         (hemb (endAt t 0) v huv (hc'A.trans hc'u.symm)) ;     · rw [if_neg hu, if_pos hv] at huv ;       have hc'u : c' u = c (endAt t 0) := by rw [hc' u, if_neg hu]; exact huv ;       refine ((hemb u (endAt t 0) huv rfl).trans ;         (Relation.ReflTransGen.single ;           ⟨hc'A.trans hc'u.symm, hc'B.trans hc'u.symm, t, htS, Or.inl ⟨rfl, rfl⟩⟩)).trans ;         (hemb (endAt t 1) v hv.symm (hc'B.trans hc'u.symm)) ;     · rw [if_neg hu, if_neg hv] at huv ;       exact absurd huv hcc ; have mergeImage : ∀ (c c' : V → V) (t : E), ;     c (endAt t 0) ≠ c (endAt t 1) → ;     (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) → ;     (Finset.univ.image c').card = (Finset.univ.image c).card - 1 := by ;   intro c c' t htc hc' ;   have himg : Finset.univ.image c' = (Finset.univ.image c).erase (c (endAt t 1)) := by ;     ext x ;     simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and] ;     constructor ;     · rintro ⟨w, hw⟩ ;       rw [hc' w] at hw ;       by_cases h : c w = c (endAt t 1) ;       · rw [if_pos h] at hw ;         refine ⟨?_, ⟨endAt t 0, hw⟩⟩ ;         rw [← hw]; exact htc ;       · rw [if_neg h] at hw ;         refine ⟨?_, ⟨w, hw⟩⟩ ;         rw [← hw]; exact h ;     · rintro ⟨hxB, w, hw⟩ ;       refine ⟨w, ?_⟩ ;       rw [hc' w, if_neg ?_] ;       · exact hw ;       · rw [hw]; exact hxB ;   rw [himg, Finset.card_erase_of_mem (Finset.mem_image_of_mem c (Finset.mem_univ _))] ; have mergeCross : ∀ (c c' : V → V) (t : E), ;     (∀ u v : V, c u = c v → Relation.ReflTransGen ;       (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S, ;         (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) → ;     t ∈ S → c (endAt t 0) ≠ c (endAt t 1) → ;     (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) → ;     S.filter (fun s => c' (endAt s 0) ≠ c' (endAt s 1)) = ;       (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).erase t := by ;   intro c c' t hint htS htc hc' ;   have hc'A : c' (endAt t 0) = c (endAt t 0) := by ;     rw [hc' (endAt t 0)] ;     by_cases h : c (endAt t 0) = c (endAt t 1) ;     · rw [if_pos h] ;     · rw [if_neg h] ;   have hc'B : c' (endAt t 1) = c (endAt t 0) := by ;     rw [hc' (endAt t 1), if_pos rfl] ;   ext s ;   simp only [Finset.mem_erase, Finset.mem_filter] ;   constructor ;   · rintro ⟨hsS, hs⟩ ;     refine ⟨?_, hsS, ?_⟩ ;     · rintro rfl ;       exact hs (hc'A.trans hc'B.symm) ;     · intro h ;       exact hs (by rw [hc' (endAt s 0), hc' (endAt s 1), h]) ;   · rintro ⟨hst, hsS, hs⟩ ;     refine ⟨hsS, ?_⟩ ;     intro h ;     rw [hc' (endAt s 0), hc' (endAt s 1)] at h ;     by_cases h0 : c (endAt s 0) = c (endAt t 1) <;> ;       by_cases h1 : c (endAt s 1) = c (endAt t 1) ;     · exact hs (h0.trans h1.symm) ;     · rw [if_pos h0, if_neg h1] at h ;       exact hst (uniqueBridge c hint t htS s hsS htc (Or.inr ⟨h0, h.symm⟩)) ;     · rw [if_neg h0, if_pos h1] at h ;       exact hst (uniqueBridge c hint t htS s hsS htc (Or.inl ⟨h, h1⟩)) ;     · rw [if_neg h0, if_neg h1] at h ;       exact hs h ; have quotientLift : ∀ (c c' : V → V) (t : E), t ∈ S → ;     (∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v) → ;     (∀ u v : V, Relation.ReflTransGen ;       (fun a b => c' a = c' b ∨ ∃ s ∈ S, ;         (c' (endAt s 0) = c' a ∧ c' (endAt s 1) = c' b) ∨ ;         (c' (endAt s 0) = c' b ∧ c' (endAt s 1) = c' a)) u v) → ;     ∀ u v : V, Relation.ReflTransGen ;       (fun a b => c a = c b ∨ ∃ s ∈ S, ;         (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨ ;         (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v := by ;   intro c c' t htS hc' hq u v ;   have hone : ∀ a b : V, c' a = c' b → Relation.ReflTransGen ;       (fun a b => c a = c b ∨ ∃ s ∈ S, ;         (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨ ;         (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) a b := by ;     intro a b hab ;     by_cases hcc : c a = c b ;     · exact Relation.ReflTransGen.single (Or.inl hcc) ;     · rw [hc' a, hc' b] at hab ;       by_cases ha : c a = c (endAt t 1) <;> by_cases hb : c b = c (endAt t 1) ;       · exact absurd (ha.trans hb.symm) hcc ;       · rw [if_pos ha, if_neg hb] at hab ;         exact Relation.ReflTransGen.single (Or.inr ⟨t, htS, Or.inr ⟨hab, ha.symm⟩⟩) ;       · rw [if_neg ha, if_pos hb] at hab ;         exact Relation.ReflTransGen.single (Or.inr ⟨t, htS, Or.inl ⟨hab.symm, hb.symm⟩⟩) ;       · rw [if_neg ha, if_neg hb] at hab ;         exact absurd hab hcc ;   refine Relation.ReflTransGen.head_induction_on (hq u v) ?_ ?_ ;   · exact Relation.ReflTransGen.refl ;   · rintro a b hab hbv ih ;     rcases hab with hab \| ⟨s, hsS, hends⟩ ;     · exact (hone a b hab).trans ih ;     · have hmid : Relation.ReflTransGen ;           (fun a b => c a = c b ∨ ∃ s' ∈ S, ;             (c (endAt s' 0) = c a ∧ c (endAt s' 1) = c b) ∨ ;             (c (endAt s' 0) = c b ∧ c (endAt s' 1) = c a)) (endAt s 0) (endAt s 1) := ;         Relation.ReflTransGen.single (Or.inr ⟨s, hsS, Or.inl ⟨rfl, rfl⟩⟩) ;       have hmid' : Relation.ReflTransGen ;           (fun a b => c a = c b ∨ ∃ s' ∈ S, ;             (c (endAt s' 0) = c a ∧ c (endAt s' 1) = c b) ∨ ;             (c (endAt s' 0) = c b ∧ c (endAt s' 1) = c a)) (endAt s 1) (endAt s 0) := ;         Relation.ReflTransGen.single (Or.inr ⟨s, hsS, Or.inr ⟨rfl, rfl⟩⟩) ;       rcases hends with ⟨h0, h1⟩ \| ⟨h0, h1⟩ ;       · exact (hone a (endAt s 0) h0.symm).trans ;           (hmid.trans ((hone (endAt s 1) b h1).trans ih)) ;       · exact (hone a (endAt s 1) h1.symm).trans ;           (hmid'.trans ((hone (endAt s 0) b h0).trans ih)) ; suffices H : ∀ (X : Finset E) (c : V → V), ;     S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1)) = X → ;     (∀ u v : V, c u = c v → Relation.ReflTransGen ;       (fun a b => c a = c u ∧ c b = c u ∧ ∃ s ∈ S, ;         (endAt s 0 = a ∧ endAt s 1 = b) ∨ (endAt s 0 = b ∧ endAt s 1 = a)) u v) → ;     (S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card ≤ ;         (Finset.univ.image c).card - 1 ∧ ;       ((S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1))).card = ;           (Finset.univ.image c).card - 1 → ;         ∀ u v : V, Relation.ReflTransGen ;           (fun a b => c a = c b ∨ ∃ s ∈ S, ;             (c (endAt s 0) = c a ∧ c (endAt s 1) = c b) ∨ ;             (c (endAt s 0) = c b ∧ c (endAt s 1) = c a)) u v) by ;   exact H _ c0 rfl hint0 ; intro X ; refine Finset.strongInductionOn X ?_ ; intro X ih c hX hintc ; by_cases hXe : X = ∅ ; · subst hXe ;   constructor ;   · rw [hX] ;     exact Nat.zero_le _ ;   · intro heq u v ;     rw [hX, Finset.card_empty] at heq ;     have hm1 : (Finset.univ.image c).card ≤ 1 := by omega ;     have hcc : c u = c v := ;       Finset.card_le_one.mp hm1 _ (Finset.mem_image_of_mem c (Finset.mem_univ u)) ;         _ (Finset.mem_image_of_mem c (Finset.mem_univ v)) ;     exact Relation.ReflTransGen.single (Or.inl hcc) ; · obtain ⟨t, htX⟩ := Finset.nonempty_iff_ne_empty.mpr hXe ;   have htXf : t ∈ S.filter (fun s => c (endAt s 0) ≠ c (endAt s 1)) := by ;     rw [hX]; exact htX ;   have htS : t ∈ S := (Finset.mem_filter.mp htXf).1 ;   have htc : c (endAt t 0) ≠ c (endAt t 1) := (Finset.mem_filter.mp htXf).2 ;   set c' : V → V := fun v => if c v = c (endAt t 1) then c (endAt t 0) else c v with hc'def ;   have hc' : ∀ v : V, c' v = if c v = c (endAt t 1) then c (endAt t 0) else c v := ;     fun v => rfl ;   have hint' := mergeInternal c c' t htS hintc hc' ;   have himg := mergeImage c c' t htc hc' ;   have hcrossX : S.filter (fun s => c' (endAt s 0) ≠ c' (endAt s 1)) = X.erase t := by ;     rw [mergeCross c c' t hintc htS htc hc', hX] ;   have hlt : X.erase t ⊂ X := Finset.erase_ssubset htX ;   obtain ⟨hb', he'⟩ := ih (X.erase t) hlt c' hcrossX hint' ;   have hm2 : 2 ≤ (Finset.univ.image c).card := ;     Finset.one_lt_card.mpr ;       ⟨c (endAt t 0), Finset.mem_image_of_mem c (Finset.mem_univ _), ;        c (endAt t 1), Finset.mem_image_of_mem c (Finset.mem_univ _), htc⟩ ;   have hcardX : X.card = (X.erase t).card + 1 := ;     (Finset.card_erase_add_one htX).symm ;   rw [hcrossX, himg] at hb' ;   constructor ;   · rw [hX] ;     omega ;   · intro heq ;     rw [hX] at heq ;     have he2 : (S.filter (fun s => c' (endAt s 0) ≠ c' (endAt s 1))).card = ;         (Finset.univ.image c').card - 1 := by ;       rw [hcrossX, himg] ;       omega ;     exact quotientLift c c' t htS hc' (he' he2)` | ✅ kernel_pass |

## Verification context

- **Environment hash:** `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- **Import manifest hash:** `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`
- **Import manifest:** `["Mathlib"]`
- **proof_body_redacted:** false

## Integrity

3 hash-chained trajectory events, `e7b5b7a9c623…` → `03d1b54c9640…` (GENESIS-anchored). Re-verify anytime with `episode_replay`.
