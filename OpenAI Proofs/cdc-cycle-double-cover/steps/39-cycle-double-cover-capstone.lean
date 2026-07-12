import Mathlib

set_option linter.unusedVariables false

def CapLoopless {V E : Type} (endAt : E → Fin 2 → V) : Prop :=
  ∀ e : E, endAt e 0 ≠ endAt e 1

def CapBridgeless {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (endAt : E → Fin 2 → V) : Prop :=
  ∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1

def CapEven {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (endAt : E → Fin 2 → V)
    (F : Finset E) : Prop :=
  ∀ v : V,
    (∑ e ∈ F, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
      (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0

def CapCycle {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (endAt : E → Fin 2 → V)
    (C : Finset E) : Prop :=
  C.Nonempty ∧ CapEven endAt C ∧
    ∀ D : Finset E, D.Nonempty → D ⊆ C → CapEven endAt D → D = C

def CapDecomposition {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (endAt : E → Fin 2 → V) : Prop :=
  ∀ F : Finset E, CapEven endAt F →
    ∃ L : List (Finset E),
      (∀ C ∈ L, CapCycle endAt C) ∧
      (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0)

def CapIndexedEvenDoubleCover {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (endAt : E → Fin 2 → V) : Prop :=
  ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
    (∀ (s : Fin 3 → ZMod 2) (v : V),
      CapEven endAt (Finset.univ.filter fun e => member s e = 1)) ∧
    (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
      member s e = 1).card = 2)

def CapCycleDoubleCover {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (endAt : E → Fin 2 → V) : Prop :=
  ∃ L : List (Finset E),
    (∀ C ∈ L, CapCycle endAt C) ∧
    (∀ e : E, (L.filter fun C => e ∈ C).length = 2)

-- Final capstone. The two higher-order hypotheses are exactly the conclusions
-- of step 38 (indexed even cover) and step 09 (cycle decomposition). The
-- step-11 list assembly is rederived below rather than assumed.
theorem probe_CAP39 :
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (endAt : E → Fin 2 → V),
  (∀ e : E, endAt e 0 ≠ endAt e 1) →
  (∀ S : Finset V, (Finset.univ.filter
    (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
  ((∀ e : E, endAt e 0 ≠ endAt e 1) →
    (∀ S : Finset V, (Finset.univ.filter
      (fun e => ¬((endAt e 0 ∈ S) ↔ (endAt e 1 ∈ S)))).card ≠ 1) →
    ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E, (Finset.univ.filter fun s : Fin 3 → ZMod 2 =>
        member s e = 1).card = 2)) →
  ((∀ e : E, endAt e 0 ≠ endAt e 1) →
    ∀ F : Finset E,
      (∀ v : V,
        (∑ e ∈ F, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
      ∃ L : List (Finset E),
        (∀ C ∈ L, C.Nonempty ∧
          (∀ v : V,
            (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
              (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
          (∀ D : Finset E, D.Nonempty → D ⊆ C →
            (∀ v : V,
              (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
                (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
            D = C)) ∧
        (∀ e : E, (L.filter fun C => e ∈ C).length =
          if e ∈ F then 1 else 0)) →
  ∃ L : List (Finset E),
    (∀ C ∈ L, C.Nonempty ∧
      (∀ v : V,
        (∑ e ∈ C, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
          (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ D : Finset E, D.Nonempty → D ⊆ C →
        (∀ v : V,
          (∑ e ∈ D, ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) →
        D = C)) ∧
    (∀ e : E, (L.filter fun C => e ∈ C).length = 2) := by
  intro V E _ _ _ _ endAt hloop hbridge hCover hDecompose
  have hcover := hCover hloop hbridge
  have hdecomp := hDecompose hloop
  obtain ⟨member, hEven, hTwo⟩ := hcover
  choose pieces hp using fun s : Fin 3 → ZMod 2 =>
    hdecomp (Finset.univ.filter fun e => member s e = 1) (hEven s)
  refine ⟨(Finset.univ : Finset (Fin 3 → ZMod 2)).toList.flatMap pieces, ?_, ?_⟩
  · intro C hC
    rw [List.mem_flatMap] at hC
    obtain ⟨s, hs, hCs⟩ := hC
    exact (hp s).1 C hCs
  · intro e
    have hflat : ∀ xs : List (Fin 3 → ZMod 2),
        ((xs.flatMap pieces).filter fun C => e ∈ C).length =
          (xs.map fun s => ((pieces s).filter fun C => e ∈ C).length).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ih => simp [List.flatMap_cons, List.filter_append, ih]
    rw [hflat]
    have hmap : ((Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map
        fun s => ((pieces s).filter fun C => e ∈ C).length) =
        (Finset.univ : Finset (Fin 3 → ZMod 2)).toList.map
          fun s => if member s e = 1 then 1 else 0 := by
      refine List.map_congr_left fun s _ => ?_
      rw [(hp s).2 e]
      by_cases h : member s e = 1
      · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩), if_pos h]
      · rw [if_neg (fun hmem : e ∈
          Finset.univ.filter (fun e' => member s e' = 1) =>
            h (Finset.mem_filter.mp hmem).2), if_neg h]
    rw [hmap, Finset.sum_map_toList, ← Finset.card_filter]
    exact hTwo e
