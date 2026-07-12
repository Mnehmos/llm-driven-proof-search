/-
CDC step 11 — Assembly: exact even double cover ⇒ cycle double cover
                (mirrors CDCLean.IndexedEvenDoubleCover.toCycleDoubleCover;
                hypothesis-chained on steps 09 and 10 because the verifier
                enforces a 60-second wall cap per invocation)
Problem version : 4adc1d0b-1d85-4d3d-879d-0ec080d5f28a
Episode         : c28d8df1-780e-4bd9-8018-34d4952c0f9d
Outcome         : kernel_verified (2026-07-11, attempt 3; attempts 1-2 were
                  60s timeouts caused by a reversed higher-order unification
                  in an unannotated if_neg argument and by Finset.sum_toList
                  being the element-sum form — fixed via local pre-flight)
Composition     : step 09 (d269b928) discharges the first hypothesis for any
                  loopless multigraph; step 10 (2667a666) discharges the
                  second for cubic graphs with a nowhere-zero F₂³-flow; the
                  three together give the cubic cycle double cover theorem.
This file is the local pre-flight copy that compiles clean on the exact pin.
-/
import Mathlib

#check @Finset.sum_toList
#check @Finset.card_filter

set_option maxHeartbeats 800000

theorem probe_assembly (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (endAt : E → Fin 2 → V)
    (hloop : ∀ e : E, endAt e 0 ≠ endAt e 1)
    (hdecomp : ∀ F : Finset E,
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
        (∀ e : E, (L.filter fun C => e ∈ C).length = if e ∈ F then 1 else 0))
    (hcover : ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ e ∈ Finset.univ.filter (fun e => member s e = 1),
          ((if endAt e 0 = v then (1 : ZMod 2) else 0) +
            (if endAt e 1 = v then (1 : ZMod 2) else 0))) = 0) ∧
      (∀ e : E,
        (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)) :
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
      · rw [if_neg (fun hmem : e ∈ Finset.univ.filter (fun e' => member s e' = 1) =>
          h (Finset.mem_filter.mp hmem).2), if_neg h]
    rw [hmap, Finset.sum_map_toList, ← Finset.card_filter]
    exact hTwo e
