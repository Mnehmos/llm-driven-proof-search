# SolveAll #11 — Smoothed Complexity of the Simplex Method

**Campaign whitepaper — updated 2026-07-19**

> **Status correction (2026 literature audit): the displayed existence target is
> malformed, not an intact open conjecture.** Bach–Huiberts' current upper bound is
> `O(σ^{-1/2}d^{11/4}log(m)^{7/4})`, and their all-pivot-rule diameter lower bound
> rules out merely polylogarithmic `1/σ` dependence under standard simplex
> semantics. Under the page's literal unrestricted initialization wording, a
> zero-pivot initializer can solve the LP before pivot counting begins. The exact
> order question remains open for a repaired model. This folder now contains a
> Lean-checked diameter-to-expectation bridge and an explicit audit of the fork.

## The problem

[solveall.org/problem/smoothed-complexity-simplex](https://solveall.org/problems).
For LPs `max cᵀx s.t. Ax ≤ b` with `A ∈ ℝ^{m×n}`, under the Gaussian smoothed
model (`A = Ā+G, b = b̄+h, c = c̄+g`, adversarial `‖(Ā,b̄,c̄)‖ ≤ 1`, i.i.d.
`N(0,σ²)` noise, `σ ∈ (0,1]`), define `T_R(A,b,c)` = pivots performed by the full
simplex algorithm under pivot rule `R`, and

```
Sm_R(m,n,σ) := sup_{‖(Ā,b̄,c̄)‖≤1} 𝔼[T_R(Ā+G, b̄+h, c̄+g)].
```

**R1 (the page's displayed question):** does some pivot rule `R` achieve
`Sm_R(m,n,σ) ≤ O(n·polylog(m,n,1/σ))`, uniformly for all `m ≥ n` and `σ ∈ (0,1]`?
More generally, what is the exact asymptotic order of `inf_R Sm_R(m,n,σ)`? The
first sentence is false under conventional Phase I semantics and vacuous under
unrestricted initialization; the second remains open after the model is repaired.

## Honest position

The earlier campaign correctly avoided a breakthrough claim but missed a newer
primary source that changes the root. The honest task is now to separate three
things: the page's literal loophole, the conventional model in which the displayed
bound is disproved, and the still-open exact-order question. The full derivation is
in [lower-bound-audit.md](lower-bound-audit.md).

## What this folder proves (all kernel-verified)

Three fronts have been built. Full per-theorem records — statements, statement
hashes, problem/episode ids, obligation ids, module-source hashes, axiom reports —
are in [evidence.md](evidence.md); the machine-readable frontier digest is
[state.md](state.md). Every tracked root uses at most the three standard axioms
`[propext, Classical.choice, Quot.sound]` (several use fewer; the abstract
pivot-count bound is axiom-free), each proof snapshot recompiles standalone under `lake env lean` (exit
0), toolchain `leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa`. Fidelity is
`attested` throughout — an honest dev-mode label that caps at `kernel_verified` and
is never `certified`.

### Front 1 — Gaussian anti-concentration base (Tier 1)

The small-ball toolkit every paper in this literature opens with.

- **M1 `gaussian_anticoncentration`.** For `X ~ N(m, σ²)`, `σ > 0`, `ε ≥ 0`,
  `Pr[|X − t| ≤ ε] ≤ 2ε/(σ√(2π))` — phrased directly in this problem's own
  `A = Ā + G` perturbation model (one entry of the perturbation). Pass@1. Proof
  idea: the Gaussian density is maximized at the mean, where it equals `(σ√(2π))⁻¹`;
  the interval measure is the density integral over `[t−ε,t+ε]`, bounded by
  (max density)·(length `2ε`). Pure calculus once the density–integral translation
  (`gaussianReal_apply_eq_integral`) is in hand. Genuinely new formalization —
  Mathlib ships `gaussianPDFReal`/`gaussianReal` but no anti-concentration lemma.

- **M1a — finite family (union bound).** `gaussian_anticoncentration_union` (M1a.1):
  for any finite family of Gaussian-law random variables on a common space,
  `P(∃ i, |X_i − t_i| ≤ ε_i) ≤ ∑_i 2ε_i/(σ_i√(2π))`, **with no independence
  assumption** — countable subadditivity suffices, which is the honest lift, since
  the `m·n` perturbed coefficients are not independent of the events one cares
  about. `gaussian_anticoncentration_union_homogeneous` (M1a.2): the clean
  `k·2ε/(σ√(2π))`. `perturbed_coeff_some_near_threshold` (M1a.3, lean_checked): the
  same in perturbed-coefficient vocabulary, explicitly bounding "some coefficient
  near a threshold" and NOT basis near-singularity.

- **M2.0 → M2.1 → M2.2 — geometric anti-concentration.**
  `gaussian_hyperplane_anticoncentration` (M2.0): for `N(center, σ²I)` with
  **arbitrary** center, unit normal `u`, threshold `t`,
  `P(|⟨u,x⟩ − t| ≤ ε) ≤ 2ε/(σ√(2π))` — the ε-slab around a fixed hyperplane, via
  Mathlib's `IsGaussian.map_eq_gaussianReal` (pushforward of `⟨u,·⟩` is a 1-D
  `gaussianReal`) with projection variance `uᵀ(σ²I)u = σ²` computed exactly.
  `gaussian_two_coord_anticoncentration` (M2.1) lifts to a codim-2 product;
  `gaussian_subspace_anticoncentration` (M2.2) is the **master result**: for an
  arbitrary-orientation codimension-`k` subspace, the sharp `(2ε/(σ√(2π)))^k`. The
  content actually proved (not assumed): distinct projections `⟨u_j,·⟩` of an
  isotropic Gaussian are *independent* — pairwise covariance `σ²⟪u_i,u_j⟫ = 0` by
  orthonormality — so the joint slab probability factorizes into `k` M1 marginals.
  M2.2 subsumes M2.1 (coordinate directions) and M2.0 (`k=1`).

### Front 2 — smallest-singular-value lower-tail (A-COND)

The actual probabilistic core of Spielman–Teng and every successor: the smallest
singular value of a Gaussian-perturbed matrix is not too small,
`P(σ_min(Ā + G) ≤ ε) ≤ C·n·ε/σ` (Sankar–Spielman–Teng / Rudelson–Vershynin form).
The pinned Mathlib has none of this: no `smallestSingularValue`, no singular-value
or determinant anti-concentration. This campaign built the pieces.

- **Deterministic Rudelson–Vershynin backbone (complete).**
  `abs_coord_mul_infDist_span_le_norm_sum` (M2-GEOM) is the per-vector reduction
  `|x_i|·dist(a_i, span{a_j : j≠i}) ≤ ‖∑ x_j a_j‖` in any real normed space — pure
  linear algebra, no probability. `rv_min_dist_bound` (M2-GEOMσ) assembles it into
  `(min_i dist)·‖x‖ ≤ √n·‖∑ x_j a_j‖`. `sigmaMin_cols_ge` (M2-DEF; and the
  equivalent Rayleigh-quotient form `sigmaMin_lower_bound`) fixes the definition
  `σ_min(cols) := ⨅_{‖x‖=1} ‖∑ x_j a_j‖` and the lower bound
  `σ_min ≥ n^{-1/2}·min_i dist(a_i, span others)`.
  `sigmaMin_le_imp_exists_col_dist_le` (M2-UNION) gives the set inclusion
  `{σ_min ≤ ε} ⊆ ⋃_i {dist_i ≤ √n·ε}`, the deterministic half of the union bound.

- **Fixed-subspace anti-concentration + conditioning (complete).**
  `gaussian_dist_subspace_le` (M2-CONDc): `P(dist(x,W) ≤ ε) ≤ 2ε/(σ√2π)` for any
  fixed subspace `W` admitting a unit normal — and since `n−1` vectors can never
  span `ℝⁿ`, that normal always exists, so the per-column bound is unconditional.
  `matrix_gaussian_columns_iIndepFun` (M2-COND3a): the product-Gaussian matrix has
  independent columns. `prod_measure_le_of_slice_le` (M2-COND3c): the Fubini
  promotion — if every conditional slice has measure `≤ c`, so does the product
  (first campaign use of an `open MeasureTheory` manifest directive, for `∫⁻`).

- **Absolute-continuity tower and a.s.-nonsingularity (complete) — the crux
  discharged.** The one genuinely-hard analytic obstruction was `det(Ā+G) ≠ 0`
  almost surely. It is now kernel-verified, built bottom-up:
  `poly_root_set_measure_zero` (M2-AC0, univariate base case);
  `pi_absolutelyContinuous` (M2-AC1) — a **genuine Mathlib gap-filler**: the
  finite-product / `Measure.pi` absolute-continuity lemma Mathlib lacks (it ships
  only the binary `AbsolutelyContinuous.prod`), proved by induction via
  `measurePreserving_piFinSuccAbove`; `gaussian_pi_absolutelyContinuous` (M2-AC2,
  product-Gaussian `≪ volume`); `stdGaussian_absolutelyContinuous` (M2-AC3, with
  corollary `stdGaussian_subspace_measure_zero`); and the capstone
  `scaled_gaussian_ac` (M2-AC4) with `scaled_gaussian_subspace_measure_zero`. M2-AC4
  proves the perturbed column `c + σ·G` — *exactly* the smoothed model's column
  `A_col = Ā_col + σ·G` — has law `≪ volume` and assigns measure 0 to any fixed
  proper subspace. Consequently each Gaussian-perturbed column misses the fixed span
  of the other `n−1` columns almost surely, so `det ≠ 0` a.s. The proof deliberately
  avoids the continuous-functional-calculus machinery of `multivariateGaussian`,
  routing through `stdGaussian ≪ volume` + scaling transport
  (`Measure.map_addHaar_smul`) + translation invariance.

  A parallel, independently-verified measurability route (the adjugate row as a
  general-`n` normal direction — `adjugate_row_dotProduct_col_eq_zero`,
  `continuous_adjugate_row`, `adjugate_row_ne_zero_of_det_ne_zero`,
  `gaussian_hyperplane_measure_zero`) fills the same role Mathlib's `Matrix.crossProduct`
  (defined only for `Fin 3`) cannot; the a.c. tower supersedes it for the main line
  by delivering a.s.-nonsingularity directly.

**What remains for the σ_min lower-tail:** assembly only. A single module wiring
M2-UNION → M2-COND3a → M2-CONDc (with `W` = span of the other columns, its normal
guaranteed by M2-AC4) → M2-COND3c → the M1a union bound yields
`P(σ_min(Ā+G) ≤ ε) ≤ C·n·ε/σ`. Every ingredient is kernel-verified; no new
mathematics is required — it would be the first Lean formalization of the σ_min core
in the smoothed model.

### Front 3 — LP / pivot-rule model (Tier 2, complete arc)

R1 is not even Lean-*expressible* without a formal LP/pivot model, and none exists
in Mathlib or any public Lean corpus this campaign found. A complete arc was built:

- `lp_feasible_convex` (T2.1) + `lp_feasible_closed` (T2.2): the feasible region
  `{x | A·x ≤ b}` is a closed convex polyhedron (preimage of `Set.Iic b` under
  `Matrix.mulVecLin A`).
- `lp_optimum_exists` (T2.3): a linear objective attains its max over a nonempty
  compact feasible set (extreme value theorem) — LP optimality existence.
- `lp_feasible_extremePoints_nonempty` (T2.4): the feasible polytope has vertices
  (Krein–Milman) — the basic feasible solutions the simplex method visits.
- `simplex_path_length_le_card` (T2.5): a strictly-improving pivot path visits
  distinct vertices, so its length is `≤ #vertices`.
- `pivotCount_le_fuel` (T2.6): the abstract pivot count `T_R` (a deterministic rule
  `step : α → Option α` run with a fuel budget) satisfies `T_R ≤ fuel`; axiom-free.
  With T2.5 and `fuel = #vertices`, `T_R` is finite and well-defined.
- `smoothedComplexity_le_of_forall_le` (T2.7, **capstone**): model
  `Sm_R := ⨆ center, 𝔼[T_R]` — the sup over the adversarial center family, exactly
  the SolveAll #11 definition — and conclude `Sm_R ≤ B` from a uniform per-center
  bound `𝔼[T_R] ≤ B`. With `B = #vertices` this is the **trivial worst-case**
  `Sm_R ≤ #vertices` — precisely the quantity R1 asks to improve to
  `O(n·polylog(m,n,1/σ))`. This rung delineates exactly what is trivial versus open.

**What remains to make R1 fully Lean-expressible** (each a real milestone, none the
open conjecture): a concrete deterministic pivot rule as an adjacent-vertex
transition on the perturbed polytope; the smoothing product measure on
`(Ā,b̄,c̄) + noise`; and `𝔼[T_R]` as an integral against it.

### Front 4 — antipodal lower-bound bridge (Tier 3)

Bach–Huiberts Theorem 57 gives, with high probability, a long 1-skeleton path
between the minimizing and maximizing vertices of every nonzero objective. For a
common objective-independent Phase I start `s`, the paths from `s` to those two
vertices have total length at least the max–min distance. Centered Gaussian
objective noise is invariant under `c ↦ -c`, so integration gives half the diameter
lower bound in expectation.

This bridge is Lean-checked in
`proof/Tier3_AntipodalLowerBoundReduction.lean`. Scaling the published fixed-
dimension-two construction by `(2m)^{-1/2}` places its center in SolveAll's global
unit ball and changes `τ` to `σ=Θ(τ²)`. The resulting
`Ω(σ^{-1/4}log(1/σ)^{-1/4})` lower bound defeats every fixed polylogarithm. The
full Bach–Huiberts theorem remains literature-supported, but its deterministic
geometric core is now Lean-checked in `proof/Tier3_BachHuibertsRoundness.lean`:
Lemma 55's roundness sandwich, the reciprocal polar radii, the polar-facet diameter
estimate, and Lemma 56's telescoping chain, adjacent-basis overlap, and numerical
length argument, including the abstract adjacent-basis-path capstone. Three companion
files Lean-check the polar-incidence/objective-ray bridge and direct exposed-face
diameter, the finite sphere-net construction, and the simultaneous Gaussian row-norm
tail from exact coordinate laws. Four further modules now Lean-check positive-RHS
normalization, full active bases at actual extreme points, affine-general-position
nondegeneracy, and a genuine-joint-product/projective-marginal theorem proving
simultaneous genericity of all small subsets. The threshold substitution, polynomial failure factor,
and final `d=2` path constant are checked. A repository assembly now also instantiates
simultaneous genericity in the exact translated/scaled augmented-row Gaussian law.
The finite charged basis path now feeds the bounded capstone directly, and the wrapper
combining it with the objective-independent initializer places the lower bound directly
on `T_R`. The exact one-sample product-Gaussian event is now checked too: normal and RHS
tails plus affine genericity have total failure at most `n⁻²`. The deterministic wrapper
through roundness, polar incidence, endpoint rays, and charged `pivotCount` is checked too.

## Where the wall is now

- **Root semantics:** the literal wording still permits an uncharged solve; the
  conventional objective-independent, fully charged repair is now formalized.
- **Formal geometric lower bound:** Bach–Huiberts Theorem 57 is not yet assembled as
  one Lean theorem. Its reusable deterministic components and exact one-sample
  probability/parameter event and deterministic `pivotCount` composition are checked;
  final root-level event-to-data/antipodal packaging remains.
- **Exact order:** after repair, dimension and constraint-count dependencies remain
  open even though the noise exponent is now known up to logarithms in the standard
  row-normalized model.

## What we did / did not prove

- **Did:** the Gaussian small-ball bound (M1) and its finite-family and geometric
  lifts (M1a, M2.0–M2.2); the complete deterministic Rudelson–Vershynin σ_min
  backbone; the conditioning machinery and the full absolute-continuity tower,
  proving a.s.-nonsingularity of the perturbed matrix in the *exact* smoothed model;
  and a complete Tier-2 LP/pivot-model arc up to `Sm_R` and the trivial worst-case
  bound. Three genuine Mathlib gap-fillers along the way (finite-product and
  product-Gaussian absolute continuity; a general-`n` normal direction).
- **Did:** identify the 2026 root-status correction; Lean-check the antipodal
  diameter-to-expectation bridge; derive the global-norm scaling obstruction; and
  Lean-check the deterministic roundness/facet/chain and basis-overlap core of
  Bach–Huiberts Lemmas 55–56, the polar incidence/minimum-point bridge, Lemma 54's
  sphere net, the exact-law finite-row Gaussian tail event, the concrete
  extreme-point/full-basis bridge, normalization, and the genericity probability induction.
- **Did not:** complete the final root-level event-to-data and antipodal packaging,
  repair the full pivot/init model, or determine the exact asymptotic order of
  `inf_R Sm_R`.

## Novelty, labeled

Per the epistemic contract, three kinds of novelty are distinguished. **Mathematical
novelty:** none claimed — the decisive geometric theorem is Bach–Huiberts', and the
newly checked roundness/facet/chain arguments and antipodal/symmetry bridge follow its
published or elementary mathematics.
**Formalization novelty:** several components appear absent from the searched Mathlib
snapshot — the Gaussian anti-concentration lemmas, finite-product and
product-Gaussian absolute continuity, and (as far as this campaign found) any Lean
LP/pivot-rule model. **Repository novelty:** all of it. The correct framing is
formalization progress and cumulative infrastructure, not new mathematical theorems.

## Complementary empirical evidence (non-rigorous, separate layer)

[`simulation/`](simulation/) runs the actual (dense, textbook) simplex method under
Gaussian smoothing on small random LPs and reports observed pivot counts as a
function of `σ`. **This is simulation evidence only — it proves nothing and is not
part of the kernel-verified record** (Layer B, strictly segregated from Layer A). It
exists to give a concrete, reproducible sense of the phenomenon the formal layer is a
foundation for. See [simulation/README.md](simulation/README.md).

## Reproduce

```bash
cd lean-checker
lake env lean "../SolveAll Open Questions/problems/011-smoothed-complexity-simplex-method/proof/<file>.lean"
```

Exit 0 = Lean's kernel accepts every step. Toolchain `leanprover/lean4:v4.32.0-rc1`
+ `mathlib@360da6fa` (this repo's pin). Each proof snapshot in [proof/](proof/) is
self-contained.

## Next steps

See [attack-plan.md](attack-plan.md) and [state.md](state.md). Highest leverage:
formalize a faithful non-oracular initialization semantics, then embed the already
kernel-checked rescaling and polylog contradiction into the concrete LP model. The
σ_min assembly remains useful, but is no longer root-critical after the lower-bound
correction.
