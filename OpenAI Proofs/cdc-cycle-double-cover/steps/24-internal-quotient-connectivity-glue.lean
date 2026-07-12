/-
CDC step 24 — NW-2 (Nash-Williams campaign, connectivity glue): internally
                connected classifier fibers + class-closed quotient
                connectivity ⇒ the edge set connects all of V
                (mirrors CDCLean.connects_of_internal_of_quotient_connects,
                 NashWilliams.lean 884–958, in the classifier encoding)
Problem version : 39c57ce0-76c9-4f85-b4f1-e3495e5ecaf2
Episode         : 5272c958-f18d-412b-84a2-86150c9ee396
Outcome         : kernel_verified (2026-07-11, first attempt)
Method          : head induction on the quotient walk; fiber-internal paths
                  embed by ReflTransGen.mono; a crossing step through edge t
                  splits as internal path → edge step → internal path.
Encodings pinned here for the whole NW campaign: fiber-internal connectivity
conjoins `c a = c u ∧ c b = c u` onto the step relation; quotient connectivity
allows `c a = c b` steps or crossing-edge steps between end-classes.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment
-/
import Mathlib

theorem root_theorem : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
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
      (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) u v := by
  intro V E _ _ _ _ endAt S c hint hquot u v
  have hemb : ∀ w x : V, c w = c x → Relation.ReflTransGen
      (fun a b => ∃ t ∈ S,
        (endAt t 0 = a ∧ endAt t 1 = b) ∨ (endAt t 0 = b ∧ endAt t 1 = a)) w x := by
    intro w x hwx
    refine Relation.ReflTransGen.mono ?_ (hint w x hwx)
    rintro a b ⟨-, -, ht⟩
    exact ht
  refine Relation.ReflTransGen.head_induction_on (hquot u v) ?_ ?_
  · exact Relation.ReflTransGen.refl
  · rintro a b hab hbv ih
    rcases hab with hcab | ⟨t, htS, hends⟩
    · exact (hemb a b hcab).trans ih
    · rcases hends with ⟨h0a, h1b⟩ | ⟨h0b, h1a⟩
      · exact ((hemb a (endAt t 0) h0a.symm).tail ⟨t, htS, Or.inl ⟨rfl, rfl⟩⟩).trans
          ((hemb (endAt t 1) b h1b).trans ih)
      · exact ((hemb a (endAt t 1) h1a.symm).tail ⟨t, htS, Or.inr ⟨rfl, rfl⟩⟩).trans
          ((hemb (endAt t 0) b h0b).trans ih)
