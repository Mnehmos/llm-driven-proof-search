/-
SolveAll #11 — "Smoothed Complexity of the Simplex Method" — companion-lemma campaign.
Tier-2 infrastructure (LP / pivot-rule model), rung 1: the feasible region of a linear program
is convex.

NOT the open conjecture, and NOT probability; pure convex geometry. This begins building the
Tier-2 LP-model infrastructure that R1 (the root SolveAll #11 statement) needs to even be
*expressible* in Lean — per root-spec.md, R1 is not yet Lean-expressible because `PivotRule`,
`T_R`, `Sm_R`, and the LP model do not exist in Mathlib or any public Lean corpus. The intended
build order is: feasible region → vertices / basic feasible solutions → pivot rule → pivot count
`T_R` → smoothing measure → `Sm_R`. This is the first rung.

For `A : Matrix (Fin m) (Fin n) ℝ` and `b : Fin m → ℝ`, the feasible set `{x | A·x ≤ b}` is
`Convex ℝ`: it is the preimage of the convex lower set `Set.Iic b` under the linear map
`Matrix.mulVecLin A` (`x ↦ A·x`), and `Convex.linear_preimage` gives convexity.

Tracked, kernel-verified root (fidelity `attested`, dev-mode; caps at kernel_verified):
  lp_feasible_convex
    problem_version  d3bfd6cf-1f4b-4e9a-baaa-7aeb72209924
    episode          68d69860-eaf5-4c15-9b90-2082589be9d7
    statement_hash   9947c6a3b95e22acfa0097753bbda09aa73a529c57541668d9bbd4476e726ff5
    module_source_hash 749bd6bbc649b624e686316a816f285769cee05b9b0c351d2a0da2243997235f
    declaration_manifest_hash 7a5948abbe70243fea791e766ceebb94b044d9e14d7e4320c62c307a97b55373
    obligation_id    53152a71-d01a-404f-b421-ebb3056e8c01
  lean_environment_hash 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d
  toolchain leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa

`#print axioms` = [propext, Classical.choice, Quot.sound]. Reproduce: `lake env lean` this file.
-/
import Mathlib

namespace SolveAll011.Tier2

/-- **Tier-2 LP model, rung 1.** The feasible region `{x | A·x ≤ b}` of a linear program is
convex — the preimage of the convex lower set `Set.Iic b` under the linear map `x ↦ A·x`. -/
theorem lp_feasible_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ {x : Fin n → ℝ | A.mulVec x ≤ b} := by
  have hset : {x : Fin n → ℝ | A.mulVec x ≤ b} = (Matrix.mulVecLin A) ⁻¹' (Set.Iic b) := by
    ext x
    simp [Set.mem_Iic]
  rw [hset]
  exact (convex_Iic b).linear_preimage (Matrix.mulVecLin A)

/-- **Tier-2 LP model, rung 2.** The feasible region `{x | A·x ≤ b}` is closed — the preimage of
the closed lower set `Set.Iic b` under the continuous map `x ↦ A·x`. With rung 1 this shows the
feasible region is a closed convex set (a polyhedron), the foundational setting for the simplex
method. (Tracked: problem `4698fe99-19ea-49a2-b6fc-f5e0c0b83456`, episode
`7c656092-e9d7-4fe6-9f4b-b190c97b1168`, statement_hash `94780ae3…`.) -/
theorem lp_feasible_closed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IsClosed {x : Fin n → ℝ | A.mulVec x ≤ b} := by
  have hset : {x : Fin n → ℝ | A.mulVec x ≤ b} = (fun x => A.mulVec x) ⁻¹' (Set.Iic b) := by
    ext x
    simp [Set.mem_Iic]
  rw [hset]
  exact IsClosed.preimage (by fun_prop) isClosed_Iic

/-- **Tier-2 LP model, rung 3 (fundamental existence theorem for LP).** A linear objective
`cᵀx = ∑ i, c i · x i` attains its maximum over a nonempty compact feasible region — the LP has an
optimal solution when feasible and bounded (a bounded closed convex feasible polyhedron is compact,
rungs 1–2). This is the optimum the simplex method computes by walking the polyhedron's vertices.
(Tracked: problem `df0ebe23-bcc2-4797-ab8a-043a9fbab062`, episode
`10e96198-b994-4e5f-bf5f-43dbf6629db6`, statement_hash `ee74950e…`.) -/
theorem lp_optimum_exists {n : ℕ} (S : Set (Fin n → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (c : Fin n → ℝ) :
    ∃ x ∈ S, ∀ y ∈ S, (∑ i, c i * y i) ≤ ∑ i, c i * x i := by
  have hcont : Continuous (fun x : Fin n → ℝ => ∑ i, c i * x i) := by fun_prop
  obtain ⟨x, hxS, hx⟩ := hS.exists_isMaxOn hne hcont.continuousOn
  exact ⟨x, hxS, fun y hy => hx hy⟩

/-- **Tier-2 LP model, rung 4.** A nonempty compact LP feasible region `{x | A·x ≤ b}` has a vertex
(extreme point) — Krein–Milman applied to the feasible polytope. The extreme points ARE the
vertices / basic feasible solutions the simplex method visits; this establishes they exist. (Tracked:
problem `8feb6613-bb10-456d-b6d3-f615c7b5a282`, episode `893ece44-3db3-4ed4-ab5f-34c6fdad86b7`,
statement_hash `89bdd7c3…`.) -/
theorem lp_feasible_extremePoints_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcompact : IsCompact {x : Fin n → ℝ | A.mulVec x ≤ b})
    (hne : {x : Fin n → ℝ | A.mulVec x ≤ b}.Nonempty) :
    ({x : Fin n → ℝ | A.mulVec x ≤ b}.extremePoints ℝ).Nonempty :=
  hcompact.extremePoints_nonempty hne

/-- **Tier-2 LP model, rung 5 (pivot-count bound / simplex termination).** A strictly-improving
pivot path — vertices `f : Fin (k+1) → α` along which the objective value `g` strictly increases —
visits distinct vertices, so its length is `≤` the number of vertices: `k + 1 ≤ Fintype.card α`.
This bounds the pivot count `T_R`: with a strictly-improving pivot rule the simplex method performs
at most `(#vertices)` pivots and terminates. (Tracked: problem `ff3312fc-d90f-433a-8e45-66f5a9aa3240`,
episode `90c47820-e693-4748-890f-d25f4cfd290f`, statement_hash `beedf0a9…`.) -/
theorem simplex_path_length_le_card {α : Type} [Fintype α] {k : ℕ} (f : Fin (k + 1) → α)
    (g : α → ℝ) (hmono : StrictMono (fun i => g (f i))) :
    k + 1 ≤ Fintype.card α := by
  have hinj : Function.Injective f := fun i j hij => hmono.injective (by rw [hij])
  have hcard := Fintype.card_le_of_injective f hinj
  rwa [Fintype.card_fin] at hcard

end SolveAll011.Tier2

#print axioms SolveAll011.Tier2.lp_feasible_convex
#print axioms SolveAll011.Tier2.lp_feasible_closed
#print axioms SolveAll011.Tier2.lp_optimum_exists
#print axioms SolveAll011.Tier2.lp_feasible_extremePoints_nonempty
#print axioms SolveAll011.Tier2.simplex_path_length_le_card
