# SolveAll #11 — Smoothed Complexity of the Simplex Method — attack plan

**The page's question (now known to require repair):** does there exist a pivot
rule `R` with near-linear smoothed complexity
`Sm_R(m,n,σ) ≤ O(n · polylog(m,n,1/σ))`, uniformly for all `m ≥ n` and
`σ ∈ (0,1]`? More generally, what is `inf_R Sm_R(m,n,σ)`?

## Honest position

The 2026 literature audit changes the task. Bach–Huiberts now give the upper
bound `O(σ^{-1/2}d^{11/4}log(m)^{7/4})` and a lower bound described by the STOC
2026 follow-up as applying to all pivot rules. Under standard simplex semantics,
that lower bound rules out the page's merely polylogarithmic dependence on
`1/σ`. Under literal unrestricted initialization, an initializer can solve the
LP before counting pivots and start at an optimum, making the target vacuous.
The immediate research job is therefore to pin the missing semantics and
formalize the lower-bound transfer, not to build an upper bound for a malformed
target. See [lower-bound-audit.md](lower-bound-audit.md).

## Tier 1 — elementary probability lemmas (the anti-concentration toolkit)

**M1 — Gaussian small-ball / anti-concentration bound (DONE, 2026-07-17).**
`gaussian_anticoncentration`: for `X ~ N(m, σ²)`, `σ > 0`, `ε ≥ 0`,
`Pr[|X − t| ≤ ε] ≤ 2ε/(σ√(2π))`. Kernel-verified, pass@1, single
`SubmitModule` step (episode `1f3255d1-62b9-4105-bca4-3da2290d5858`). This is
the literal opening estimate of every paper in this literature — it is what
lets you bound the probability that a Gaussian-perturbed coefficient (exactly
this problem's own `A = Ābar + G` model) lands near a degeneracy threshold.
Built from scratch: Mathlib has `gaussianPDFReal`/`gaussianReal` machinery but
no anti-concentration lemma. See [whitepaper.md](whitepaper.md) for the full
account and [proof/](proof/) for the Lean source.

**M1a — finite-family Gaussian anti-concentration (DONE, 2026-07-17).** Two
tracked kernel-verified theorems, both pass@1:
- **M1a.1** `gaussian_anticoncentration_union` (problem `46bd7c1a`, episode
  `e4c031ff`): for a finite family of Gaussian-law random variables on a common
  space, `P(∃ i, |X_i − t_i| ≤ ε_i) ≤ ∑_i 2ε_i/(σ_i√(2π))`. **No independence
  assumption** — countable subadditivity (`measure_iUnion_le`) suffices. This
  is the honest, general lift.
- **M1a.2** `gaussian_anticoncentration_union_homogeneous` (problem `c1e88e47`,
  episode `e04f96ea`): the clean `k · 2ε/(σ√(2π))` when all `k = |ι|`
  coefficients share `σ, ε`.
- **M1a.3** `perturbed_coeff_some_near_threshold` (lean_checked bridge): the
  same in perturbed-coefficient vocabulary. Bounds "some individual perturbed
  coefficient is ε-close to a threshold" — explicitly NOT "a basis is
  near-singular."

Snapshot: [proof/Milestone1a_FiniteFamilyAntiConcentration.lean](proof/Milestone1a_FiniteFamilyAntiConcentration.lean).
All roots: `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**M2.0 — distance from a Gaussian vector to a fixed hyperplane (DONE,
kernel-verified 2026-07-17).** `gaussian_hyperplane_anticoncentration`: for a
multivariate Gaussian `N(center, σ²I_n)` with **arbitrary** center on
`EuclideanSpace ℝ (Fin n)`, any unit normal `u` and threshold `t`,
`P(|⟨u,x⟩ − t| ≤ ε) ≤ 2ε/(σ√(2π))` — i.e. `x` is unlikely to lie in the ε-slab
around the fixed affine hyperplane `{x | ⟨u,x⟩ = t}` (distance `= |⟨u,x⟩−t|` since
`‖u‖=1`). The M2 reconnaissance's prerequisite is RESOLVED: Mathlib's
`IsGaussian.map_eq_gaussianReal` pushes the functional `⟨u,·⟩` to a 1-D `gaussianReal`,
and `covarianceBilin_multivariateGaussian` gives `Var[⟨u,·⟩] = uᵀ(σ²I)u = σ²` exactly.
The proof reuses the M1 helper unchanged; the arbitrary center passes through because
M1 is uniform in the mean. Tracked: problem `ff02637d`, episode `851ff2ce`, statement
hash `7031dca1…`; standalone `lake env lean` exit 0; `#print axioms` = the three
standard axioms. `kernel_verified`, 2 submissions (a helper-transport repair, not a
math error). Source:
[proof/Milestone2_0_HyperplaneAntiConcentration.lean](proof/Milestone2_0_HyperplaneAntiConcentration.lean).

**M2.1 / M2.2 — distance from a Gaussian vector to a fixed subspace (DONE,
kernel-verified).** `gaussian_two_coord_anticoncentration` (M2.1, codim-2 product) and
the **master** `gaussian_subspace_anticoncentration` (M2.2, arbitrary-orientation
codimension-`k`, sharp `(2ε/(σ√(2π)))^k`) — the sharp joint route via independence of
the projections `⟨u_j,·⟩` under `σ²I` (covariance `σ²⟪u_i,u_j⟫ = 0` by orthonormality).
M2.2 subsumes M2.1 and M2.0. Both pass@1.

**M2 — smallest-singular-value anti-concentration (NEAR-COMPLETE; the crux
discharged).** The probabilistic core of Spielman–Teng: `P(σ_min(Ā+G) ≤ ε) ≤ C·n·ε/σ`.
Mathlib has no `smallestSingularValue` and no singular-value/determinant
anti-concentration; the pieces were built. **Deterministic Rudelson–Vershynin backbone
DONE** (`abs_coord_mul_infDist_span_le_norm_sum`, `rv_min_dist_bound`,
`sigmaMin_cols_ge`/`sigmaMin_lower_bound`, `sigmaMin_le_imp_exists_col_dist_le`):
`σ_min(A) ≥ n^{-1/2}·min_i dist(a_i, span others)` and the inclusion
`{σ_min ≤ ε} ⊆ ⋃_i {dist_i ≤ √n·ε}`. **Fixed-subspace bound + conditioning DONE**
(`gaussian_dist_subspace_le`, `matrix_gaussian_columns_iIndepFun`,
`prod_measure_le_of_slice_le`). **The one genuinely-hard analytic obstruction —
`det(Ā+G) ≠ 0` a.s. — DONE** via the absolute-continuity tower (`poly_root_set_measure_zero`,
the Mathlib gap-fillers `pi_absolutelyContinuous` / `gaussian_pi_absolutelyContinuous`,
`stdGaussian_absolutelyContinuous`, and `scaled_gaussian_ac` /
`scaled_gaussian_subspace_measure_zero`): the perturbed column `c+σ·G` has law
`≪ volume` and misses any fixed proper subspace a.s. **Remaining: assembly only** — one
module wiring the verified pieces into the σ_min lower-tail; no new mathematics.

## Tier 2 — infrastructure layer (📐: define the model, then ask what's provable) — COMPLETE ARC

- **The LP / pivot-rule model itself — DONE up to `Sm_R`.** A complete arc was
  formalized (no such model existed in Mathlib or any public Lean corpus found):
  feasible region convex + closed (`lp_feasible_convex`, `lp_feasible_closed`) → LP
  optimum exists (`lp_optimum_exists`) → vertices exist
  (`lp_feasible_extremePoints_nonempty`, Krein–Milman) → strict-improve path ≤ #vertices
  (`simplex_path_length_le_card`) → abstract pivot count `T_R` finite
  (`pivotCount_le_fuel`, axiom-free) → capstone `smoothedComplexity_le_of_forall_le`:
  `Sm_R := ⨆ 𝔼[T_R]` with `Sm_R ≤ B`. With `B = #vertices` this is the trivial
  worst-case `Sm_R ≤ #vertices` — exactly the quantity R1 asks to improve.
- **Remaining to make R1 fully Lean-expressible** (each a real milestone, none the open
  conjecture): a concrete deterministic pivot rule as an adjacent-vertex transition on
  the perturbed polytope; the smoothing product measure on `(Ā,b̄,c̄) + noise`; and
  `𝔼[T_R]` as an integral against it. **Tooling boundary noted:** a tracked root
  statement must elaborate standalone, so it cannot reference a module-local recursive
  `def`; `T_R` was tracked by inlining `Nat.rec`. A SubmitModule "define-then-prove"
  flow would let recursive `T_R`/`Sm_R` rungs be tracked in natural `def` form — a
  candidate upstream MCP-tooling improvement.

## Tier 3 — lower bound and root repair (ACTIVE)

- **Published input (literature_supported):** Bach–Huiberts Theorem 57 gives a
  high-probability max–min diameter lower bound
  `Ω(τ^{-1/2}d^{1/2}log(1/τ)^{-1/4})` for `M=⌊(4/τ)^d⌋`, simultaneous over all
  nonzero objectives.
- **Diameter → expected pivots (DONE, lean_checked):** antipodal objectives
  `c,-c`, a common objective-independent Phase I start, graph-distance triangle
  inequality, and measure-preserving Gaussian negation give `D ≤ 2·𝔼[T]`.
  Source: `proof/Tier3_AntipodalLowerBoundReduction.lean`.
- **Published lower-bound machinery (NEAR-COMPLETE AS COMPONENTS, lean_checked):**
  `proof/Tier3_BachHuibertsRoundness.lean` formalizes Lemma 55 and the full abstract
  adjacent-basis-path form of Lemma 56. `Tier3_PolarIncidence.lean` supplies polar
  closedness/convexity, the minimum-norm face point, reciprocal ball inclusions, active
  normals, and objective rays. `Tier3_SphereNet.lean` proves Lemma 54, and
  `Tier3_GaussianTail.lean` proves the finite-row Gaussian norm event from exact
  coordinate laws, including the explicit `4σ√(log n)` substitution and
  `2·rows·dim/n⁸` failure bound. `Tier3_AffineGenericity.lean`,
  `Tier3_NormalizedLPBasis.lean`, and `Tier3_VertexActiveBasis.lean` now supply
  normalization and the concrete extreme-point/full-basis bridge;
  `Tier3_GenericityProbability.lean` now works on the genuine joint `Measure.pi` law,
  proves its projective subset marginals, and obtains simultaneous genericity for
  every small subset. `Tier3_GaussianAffineGenericityAssembly.lean` composes this with
  exact translated/scaled Gaussian row AC. The `d=2` final path constant is checked.
  `Tier3_FinitePathLowerBoundAssembly.lean` now feeds a finite charged basis path directly
  into the capstone. `Tier3_RepairedPivotSemantics.lean` supplies an objective-independent
  initializer, exact equality of charged execution length with `T_R`, and the common
  antipodal start. `Tier3_ExecutionLowerBoundAssembly.lean` combines this with the
  finite basis path and puts the bound directly on `T_R`. Remaining are good-event
  combination and final assembly.
- **Global-norm transfer (PARTIAL, lean_checked + informal embedding):** for `d=2`, scale constraints by
  `α=(2M)^{-1/2}`. The SolveAll noise becomes `σ=ατ=Θ(τ²)`, the center enters the
  stacked unit ball, and the lower bound becomes
  `Ω(σ^{-1/4}log(1/σ)^{-1/4})`, which defeats every polylogarithm. The floor,
  noise-scaling, and asymptotic separation are Lean-checked; their embedding into the
  concrete LP/smoothing model is still informal.
- **Semantic wall:** define initialization so it cannot perform an uncharged LP
  solve. Objective-independent Phase I is sufficient for the verified reduction;
  an explicitly charged auxiliary-polytope edge walk would be more general.

## Sequencing recommendation (updated 2026-07-19)

The Tier-1 anti-concentration base, the deterministic σ_min backbone, the conditioning
machinery, the absolute-continuity tower (a.s.-nonsingularity in the exact smoothed
model), and the full Tier-2 arc up to `Sm_R` are all kernel-verified. The leverage has
moved past self-contained anti-concentration variants and past the Tier-2 skeleton.

**Highest-leverage target:** the exact one-sample Gaussian norm/genericity event,
its `d=2` arithmetic, and the deterministic Theorem 57 `pivotCount` wrapper are now
checked. Package them with the tracked antipodal expectation and rescaling conclusion,
using the existing dense-net, polar-incidence, global-norm scaling, and
`σ^{-1/4}` versus polylog
contradiction. This would close the displayed existence question under explicit
standard semantics.

**Secondary target:** finish the σ_min lower-tail composition. It remains valuable
formalization work, but it no longer controls the root after the lower-bound correction.
