/-
Erdős Problem #858 — Proposition 5.6 (headline conclusion): existence and
uniqueness of the critical exponent α₂.
(Chojecki 2026, "An exact frontier theorem and the asymptotic constant for
Erdős problem #858", Proposition 5.6.)

The limiting prime+semiprime density Φ(u) = log((1-u)/u) + I(u) is continuous and
strictly decreasing on [1/4, 1/3], with Φ(1/4) > 1 and Φ(1/3) < 1. Proposition
5.6 concludes: there is a UNIQUE α₂ ∈ (1/4, 1/3) with Φ(α₂) = 1. This α₂ pins the
asymptotic constant c₂ for #858.

This snapshot is the conditional assembly of that conclusion, taking as inputs the
two structural facts the companion snapshots establish and the two boundary
values the paper computes:
  (i)   ContinuousOn Φ [1/4, 1/3]          (Erdos858_Prop56_Continuity, #37);
  (ii)  StrictAntiOn Φ [1/4, 1/3]          (Erdos858_Prop56_FullMonotone #59,
        restricted from [1/4, 1/2]);
  (iii) 1 < Φ(1/4)                         (paper boundary value);
  (iv)  Φ(1/3) < 1                         (paper boundary value).
Given those, the theorem discharges the genuinely combinatorial-analytic content
of Prop 5.6's conclusion: existence via the intermediate value theorem and
uniqueness via strict-antitone injectivity.

Kernel-verified via the proofsearch MCP:
  episode 68679336-adf1-4a0f-8a8b-749067faeaae,
  problem_version_id 99ca8867-ef20-47fd-a12b-9f6bae05db44.
Outcome: kernel_verified / root_kernel_verified (first submission).
Toolchain: leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56.
root_statement_hash d9b41df1d23122480bfb1aa391f8037226ed27179807a5028e656adb0d469df0.

Lean note (the two mechanisms the pin provides):
EXISTENCE — `intermediate_value_Ioo'` (Mathlib/Topology/Order/IntermediateValue.lean:626):
  {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ioo (f b) (f a) ⊆ f '' Ioo a b.
This is the DECREASING orientation (note the swapped `f b`, `f a`): with a = 1/4,
b = 1/3 it states `Ioo (Φ(1/3)) (Φ(1/4)) ⊆ Φ '' Ioo (1/4) (1/3)`. Since `1` lies
strictly between the boundary values, `(1 : ℝ) ∈ Ioo (Φ(1/3)) (Φ(1/4))` is
literally `⟨h13, h14⟩ = ⟨Φ(1/3) < 1, 1 < Φ(1/4)⟩`, so applying the subset and
`obtain`-ing the image membership yields an `a ∈ Ioo (1/4) (1/3)` with `Φ a = 1`,
directly on the OPEN interval — no need to apply IVT to `-Φ` or reverse the order.
UNIQUENESS — `StrictAntiOn.injOn` (Mathlib/Order/Monotone/Basic.lean:411):
  (hf : StrictAntiOn f s) : s.InjOn f.
Any second root `y ∈ Ioo (1/4) (1/3)` with `Φ y = 1` satisfies `Φ y = Φ a`
(both `= 1`), and `Set.Ioo_subset_Icc_self` lifts both memberships into the
`Icc (1/4) (1/3)` on which `hanti` is stated, so `hanti.injOn … … (by rw […])`
forces `y = a`. Everything is packaged with `ExistsUnique`'s anonymous
constructor `⟨a, ⟨ha_mem, ha_eq⟩, ?_⟩` followed by `rintro y ⟨hy_mem, hy_eq⟩`.
-/
import Mathlib

namespace Erdos858

/-- Proposition 5.6 (headline conclusion): for a function `Φ : ℝ → ℝ` that is
continuous and strictly antitone on `[1/4, 1/3]` with `Φ(1/4) > 1` and
`Φ(1/3) < 1`, there is a **unique** `α₂ ∈ (1/4, 1/3)` with `Φ(α₂) = 1`. Existence
is the intermediate value theorem in the decreasing orientation
(`intermediate_value_Ioo'`); uniqueness is the injectivity of a strictly antitone
function (`StrictAntiOn.injOn`). Conditional on the monotonicity (#59) and
continuity (#37) companion snapshots plus the paper's boundary values, this is the
`α₂` that pins the asymptotic constant `c₂`. -/
theorem erdos858_prop56_alpha2_unique :
    ∀ (Phi : ℝ → ℝ),
      ContinuousOn Phi (Set.Icc (1/4 : ℝ) (1/3)) →
      StrictAntiOn Phi (Set.Icc (1/4 : ℝ) (1/3)) →
      1 < Phi (1/4) →
      Phi (1/3) < 1 →
      ∃! a, a ∈ Set.Ioo (1/4 : ℝ) (1/3) ∧ Phi a = 1 := by
  intro Phi hcont hanti h14 h13
  have hab : (1/4 : ℝ) ≤ 1/3 := by norm_num
  have hmem : (1 : ℝ) ∈ Set.Ioo (Phi (1/3)) (Phi (1/4)) := ⟨h13, h14⟩
  obtain ⟨a, ha_mem, ha_eq⟩ := intermediate_value_Ioo' hab hcont hmem
  refine ⟨a, ⟨ha_mem, ha_eq⟩, ?_⟩
  rintro y ⟨hy_mem, hy_eq⟩
  exact hanti.injOn (Set.Ioo_subset_Icc_self hy_mem) (Set.Ioo_subset_Icc_self ha_mem) (by rw [hy_eq, ha_eq])

end Erdos858
