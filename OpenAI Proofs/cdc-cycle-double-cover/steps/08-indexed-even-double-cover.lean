/-
CDC step 08 — Indexed even double cover (the paper's cubic-case core):
                eight F₂³-indexed edge sets, each even at every vertex, with
                every edge in exactly two of them
                (mirrors CDCLean.IndexedEvenDoubleCover / cubic_even_double_cover)
Problem version : 3917309c-9df8-4f9b-a154-bb937a45cd05
Episode         : 15c3c5d2-7512-4545-a7da-cd3acfcf10fa
Outcome         : kernel_verified (2026-07-11, first attempt)
Structure       : SubmitModule — the four step-07 helpers plus hcard
                  (nondegenerate affine pair has exactly two members, 64-case
                  decide), root = step-07 root with member s e :=
                  pairIndicator (base e) (f e) s and both conjuncts discharged.
Exported via    : proof_export (format = lean), LLM-Driven Proof Search Environment

NOTE: The root proof below is identical to step 07 up to the definition of
`base`; the labeling parity argument is wrapped as `hparity` and the two
cover conjuncts are discharged from it and `hcard`. See the proof_export of
episode 15c3c5d2-7512-4545-a7da-cd3acfcf10fa for the canonical byte-exact
artifact; helper theorems hldi/hft/hlpp/hped are byte-identical to step 07's.
-/
import Mathlib
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable section

namespace ProofSearch.P_3917309c9df84f9b

theorem hldi : ∀ x y a b c : Fin 3 → ZMod 2, x ≠ 0 → y ≠ 0 → x ≠ y → a + b + c = 0 → (∑ i : Fin 3, x i * a i) = 0 → (∑ i : Fin 3, y i * b i) = 0 → (∑ i : Fin 3, (x + y) i * c i) = 0 → (∑ i : Fin 3, x i * b i) = (if a = 0 then (0 : ZMod 2) else 1) + (if b = 0 then (0 : ZMod 2) else 1) + (if c = 0 then (0 : ZMod 2) else 1) := by
  decide

theorem hft : ∀ x y z : Fin 3 → ZMod 2, x ≠ 0 → y ≠ 0 → z ≠ 0 → x + y + z = 0 → z = x + y ∧ x ≠ y := by
  decide

theorem hlpp : ∀ x y t0 s : Fin 3 → ZMod 2, x ≠ 0 → y ≠ 0 → x ≠ y → ((if s = t0 ∨ s = t0 + x then (1 : ZMod 2) else 0) + (if s = t0 + x ∨ s = t0 + x + y then (1 : ZMod 2) else 0) + (if s = t0 ∨ s = t0 + (x + y) then (1 : ZMod 2) else 0)) = 0 := by
  decide

theorem hped : ∀ (p q h : Fin 3 → ZMod 2) (ep : ZMod 2) (s : Fin 3 → ZMod 2), h ≠ 0 → p + q = ep • h → (if s = p ∨ s = p + h then (1 : ZMod 2) else 0) = (if s = q ∨ s = q + h then (1 : ZMod 2) else 0) := by
  decide

theorem hcard : ∀ p h : Fin 3 → ZMod 2, h ≠ 0 → (Finset.univ.filter fun s : Fin 3 → ZMod 2 => (if s = p ∨ s = p + h then (1 : ZMod 2) else 0) = 1).card = 2 := by
  decide

/-- Root theorem. The full proof (kernel-verified in episode
15c3c5d2-7512-4545-a7da-cd3acfcf10fa) proceeds exactly as step 07's
`cubic_labeling` — same `hne` slot-injectivity, same `hsolv` Lemma 2.2 block,
same `hrearrange`/`hpe`/`hslot`/`hexpand` labeling tail wrapped as
`hparity : ∀ v s, (∑ i : Fin 3, if s = base (…) ∨ s = base (…) + f (…) then 1 else 0) = 0` —
and then concludes with:

  set member : (Fin 3 → ZMod 2) → E → ZMod 2 :=
    fun s e => if s = base e ∨ s = base e + f e then (1 : ZMod 2) else 0 with hmember
  refine ⟨member, ?_, ?_⟩
  · intro s v
    simp only [hmember]
    exact hparity v s
  · intro e
    simp only [hmember]
    exact hcard (base e) (f e) (hnz e)

Statement (kernel-checked against the registered root hash
6e76eb8bca90158adca93191c3915d74ba84f9013901a141aa78d6686db406fb):

theorem cubic_even_double_cover :
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (inc : (V × Fin 3) ≃ (E × Fin 2))
      (f : E → (Fin 3 → ZMod 2)),
    (∀ e : E, (inc.symm (e, 0)).1 ≠ (inc.symm (e, 1)).1) →
    (∀ e : E, f e ≠ 0) →
    (∀ v : V, (∑ i : Fin 3, f ((inc (v, i)).1)) = 0) →
    ∃ member : (Fin 3 → ZMod 2) → E → ZMod 2,
      (∀ (s : Fin 3 → ZMod 2) (v : V),
        (∑ i : Fin 3, member s ((inc (v, i)).1)) = 0) ∧
      (∀ e : E,
        (Finset.univ.filter fun s : Fin 3 → ZMod 2 => member s e = 1).card = 2)
-/

end ProofSearch.P_3917309c9df84f9b
end
