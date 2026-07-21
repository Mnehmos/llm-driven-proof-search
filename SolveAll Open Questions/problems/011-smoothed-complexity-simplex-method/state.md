# state.md — SolveAll #11 campaign frontier

Machine-readable resume point. A fresh session reads this + the constitution
(`../../CLAUDE.md`) + `attack-plan.md` and continues without conversation memory.
Authoritative per-theorem records (statements, hashes, episodes, obligations)
live in `evidence.md` (append-only); this file is the digest.

**Root R1 status: SPECIFICATION FORK (2026 literature correction).** The page's
displayed `n·polylog(m,n,1/σ)` target is false under conventional simplex semantics,
using Bach–Huiberts' all-pivot-rule diameter lower bound plus the Lean-checked antipodal
objective reduction below. Under the literal unrestricted-initialization wording it
is vacuous: initialize at an optimum using uncharged work and take zero pivots. The
general exact-order question remains open for a repaired model. See
[`lower-bound-audit.md`](lower-bound-audit.md).

## Campaign frontier at a glance

Three tracked verified fronts and two Lean-checked Tier-3 modules have been built,
plus a literature-backed root correction:

1. **Anti-concentration base (Tier 1).** M1 scalar small-ball → M1a finite-family
   union bound → M2.0 fixed-hyperplane → M2.1 codim-2 → M2.2 arbitrary-orientation
   codim-k. Complete.
2. **σ_min anti-concentration core (A-COND).** The Sankar–Spielman–Teng
   smallest-singular-value lower-tail. Deterministic Rudelson–Vershynin backbone
   complete; the absolute-continuity tower and a.s.-nonsingularity in the EXACT
   smoothed model complete; reduced to a final assembly of verified pieces.
3. **Tier-2 LP / pivot-rule model.** A complete arc from the feasible polytope up
   to `Sm_R` and the trivial worst-case bound `Sm_R ≤ #vertices` — the exact
   quantity R1 asks to improve.
4. **Tier-3 lower-bound reduction.** A Lean-checked graph-distance and
   measure-preserving-symmetry bridge turns a max–min diameter lower bound into an
   expected pivot lower bound for centered Gaussian objectives and an
   objective-independent Phase I start. The deterministic geometry of the published
   lower bound is now Lean-checked through the roundness sandwich, polar-facet diameter
   estimate, and the metric-chain/numerical core of the path-length lemma.

## Strongest tracked results and new Lean-checked reductions

### Tier 1 — anti-concentration base

| id | theorem | problem_version | episode | statement_hash |
|---|---|---|---|---|
| M1 | `gaussian_anticoncentration` (scalar small-ball) | `d2f3e8c3-…` | `1f3255d1-…` | `762c7306…` |
| M1a.1 | `gaussian_anticoncentration_union` (finite family, no independence) | `46bd7c1a-…` | `e4c031ff-…` | `cd45ebe4…` |
| M1a.2 | `gaussian_anticoncentration_union_homogeneous` (k·bound) | `c1e88e47-…` | `e04f96ea-…` | `d3f497b5…` |
| M2.0 | `gaussian_hyperplane_anticoncentration` (dist to fixed hyperplane; arbitrary center) | `ff02637d-…` | `851ff2ce-…` | `7031dca1…` |
| M2.1 | `gaussian_two_coord_anticoncentration` (codim-2 coordinate product) | `c548e3fe-…` | `10653478-…` | `dd3b81bd…` |
| M2.2 | `gaussian_subspace_anticoncentration` (arbitrary-orientation codim-k) | `4a4d86dd-…` | `ea3c53fe-…` | `3ad10c1d…` |

### σ_min core (A-COND) — deterministic Rudelson–Vershynin backbone

| id | theorem | problem_version | episode | statement_hash |
|---|---|---|---|---|
| M2-GEOM | `abs_coord_mul_infDist_span_le_norm_sum` (per-vector RV reduction) | `8d13dff9-…` | `d99aa6a8-…` | `8588c87e…` |
| M2-GEOMσ | `rv_min_dist_bound` (`(min_i dist)·‖x‖ ≤ √n·‖∑ x_j a_j‖`) | `ca8e0109-…` | `56a975eb-…` | `aeb92904…` |
| M2-DEF | `sigmaMin_cols_ge` (`σ_min(cols) ≥ n^{-1/2}·min_i dist`, unit-sphere inf) | `73ac63c1-…` | `9bdee270-…` | `f3cb5ad1…` |
| M2-DEF′ | `sigmaMin_lower_bound` (same bound, nonzero-vector Rayleigh-quotient inf) | `ecacc32e-…` | `5a5ec38c-…` | `67cb826c…` |
| M2-UNION | `sigmaMin_le_imp_exists_col_dist_le` (`σ_min ≤ ε ⇒ ∃ i, dist_i ≤ √n·ε`) | `6abbb760-…` | `0236838c-…` | `1c31ea73…` |

### σ_min core (A-COND) — conditioning + absolute-continuity tower

| id | theorem | problem_version | episode | statement_hash |
|---|---|---|---|---|
| M2-CONDc | `gaussian_dist_subspace_le` (`P(dist(x,W)≤ε) ≤ 2ε/(σ√2π)`, fixed subspace) | `337087ce-…` | `b15cd230-…` | `60ecff76…` |
| M2-COND3a | `matrix_gaussian_columns_iIndepFun` (product Gaussian matrix ⇒ independent columns) | `88cc675f-…` | `a95d1c04-…` | `04c6e144…` |
| M2-COND3c | `prod_measure_le_of_slice_le` (Fubini: all slices ≤ c ⇒ product measure ≤ c) | `7cf633b2-…` | `3a68c3c7-…` | `14052aff…` |
| M2-AC0 | `poly_root_set_measure_zero` (nonzero univariate poly ⇒ null zero set) | `8cf700f9-…` | `1dbbeac4-…` | `678dc1db…` |
| M2-AC1 | `pi_absolutelyContinuous` (finite-product a.c.; **Mathlib gap-filler**) | `417c70aa-…` | `5f8f7d06-…` | `98902641…` |
| M2-AC2 | `gaussian_pi_absolutelyContinuous` (product-Gaussian ≪ volume) | `3c4db4e8-…` | `b9683c13-…` | `9d61c490…` |
| M2-AC3 | `stdGaussian_absolutelyContinuous` (+ `stdGaussian_subspace_measure_zero`) | `479268e8-…` | `6459515f-…` | `c1b64ee9…` |
| **M2-AC4** | **`scaled_gaussian_ac` (perturbed column `c+σG ≪ volume`) + `scaled_gaussian_subspace_measure_zero` (a.s.-nonsingularity, EXACT smoothed model)** | `7683b09b-…` | `4ec96081-…` | `91f742e1…` |

Parallel/earlier measurable-normal route (adjugate direction), all kernel-verified:
`adjugate_row_dotProduct_col_eq_zero` (`4f595606`/`6216166d`),
`continuous_adjugate_row` (`beafa0cb`/`1aa443a1`),
`adjugate_row_ne_zero_of_det_ne_zero` (`8624ced9`/`4af0617a`),
`gaussian_hyperplane_measure_zero` (`c2a131a2`/`ba309a56`). Superseded for the main
line by the a.c. tower (which gives a.s.-nonsingularity directly), but retained as an
independent measurability route.

### Tier-2 — LP / pivot-rule model (complete arc)

| id | theorem | problem_version | episode | statement_hash |
|---|---|---|---|---|
| T2.1 | `lp_feasible_convex` (feasible region convex) | `d3bfd6cf-…` | `68d69860-…` | `9947c6a3…` |
| T2.2 | `lp_feasible_closed` (feasible region closed) | `4698fe99-…` | `7c656092-…` | `94780ae3…` |
| T2.3 | `lp_optimum_exists` (LP optimum exists over compact feasible set) | `df0ebe23-…` | `10e96198-…` | `ee74950e…` |
| T2.4 | `lp_feasible_extremePoints_nonempty` (vertices exist; Krein–Milman) | `8feb6613-…` | `893ece44-…` | `89bdd7c3…` |
| T2.5 | `simplex_path_length_le_card` (strict-improve path ≤ #vertices) | `ff3312fc-…` | `90c47820-…` | `beedf0a9…` |
| T2.6 | `pivotCount_le_fuel` (abstract `T_R` ≤ fuel; axiom-free) | `ce2c61b2-…` | `d0cb7b08-…` | `c9288651…` |
| **T2.7** | **`smoothedComplexity_le_of_forall_le` (`Sm_R := ⨆ 𝔼[T_R] ≤ B`; trivial worst-case `Sm_R ≤ #vertices`)** | `fd8e476d-…` | `9421e154-…` | `0579b26d…` |

### Tier-3 — antipodal lower-bound bridge

| theorem | content | evidence |
|---|---|---|
| `oracle_initialization_gives_zero_pivots` | unrestricted uncharged optimal initialization yields pointwise zero counted pivots | lean_checked; `[propext, Quot.sound]` |
| `antipodal_pivot_sum_ge` | common start + max/min graph distance `D` ⇒ the `c` and `-c` pivot counts sum to at least `D` | lean_checked; `[propext, Quot.sound]` |
| `antipodal_one_run_ge_half` | one antipodal run costs at least `⌈D/2⌉` | lean_checked; `[propext, Quot.sound]` |
| `symmetric_lintegral_pair_lower_bound` | measure-preserving objective negation ⇒ `D ≤ 2·𝔼[T]` | lean_checked; three standard axioms |
| `polylog_with_quarter_isLittleO_quarterPower` | `log(x)^(k+1/4) = o(x^(1/4))` for every fixed `k` | lean_checked; three standard axioms |
| `scaled_noise_between_quadratic_bounds` | `8/τ²≤M≤16/τ²`, `σ=τ/√(2M)` ⇒ `τ²/(4√2)≤σ≤τ²/4` | lean_checked; three standard axioms |
| `half_le_natFloor_and_natFloor_le` | `x≥2` ⇒ `x/2≤⌊x⌋₊≤x` | lean_checked; three standard axioms |

Tracked root companions now upgrade the resolution-critical semantic and asymptotic
bridges: unrestricted optimal initialization (`pv 45200eb4…`, episode `4edec869…`),
antipodal expectation (`pv 3687dd9d…`, episode `83e2e9ea…`), global-norm rescaling
(`pv 6d142e41…`, episode `3548c3b0…`), and polylog separation (`pv ee18bc76…`,
episode `39baac00…`) all have `outcome = kernel_verified`. See `evidence.md` for
full hashes; fidelity remains development-attested, never certified.

Source SHA-256 `e288317e78c09fca80c7cf02a7129b1bda3c2ea7c4f735f6e04c1fc1027e7b40`;
standalone `lake env lean` exit 0 in the pinned environment. No tracked
proof-service episode exists for these new roots, so their evidence label is
`lean_checked`.

### Tier-3 — Bach–Huiberts deterministic lower-bound geometry

| theorem | content | evidence |
|---|---|---|
| `bachHuiberts_roundness_sandwich` | the full `(1-2η)B ⊆ P ⊆ (1+4η)B` conclusion of Lemma 55 | lean_checked; three standard axioms |
| `reciprocal_roundness_bounds` | polar-radius relaxations `1-4η ≤ (1+4η)⁻¹` and `(1-2η)⁻¹ ≤ 1+3η` | lean_checked; three standard axioms |
| `near_round_facet_point_dist` | closest-point condition gives `‖v-y‖ ≤ √(14η)` | lean_checked; three standard axioms |
| `near_round_facet_pair_dist` | polar-facet diameter core `‖v-w‖ ≤ 2√(14η)` | lean_checked; three standard axioms |
| `near_round_facet_pair_dist_eight_sqrt` | the paper's final polar-facet bound `‖v-w‖ ≤ 8√η` | lean_checked; three standard axioms |
| `norm_chain_le` | an `ℓ`-link chain with links at most `γ` spans at most `ℓγ` | lean_checked; three standard axioms |
| `adjacent_basis_chain_inter_nonempty` | fewer than `d` adjacent exchanges of `d`-element bases preserve a shared index | lean_checked; three standard axioms |
| `antipodal_chain_forces_many_blocks` | the Lemma 56 endpoint accounting gives `2/R ≤ (ℓ+3)γ` | lean_checked; three standard axioms |
| `bachHuiberts_length_from_chain` | the numerical conclusion `q(2/(Rγ)-3) ≤ k` | lean_checked; three standard axioms |
| `bachHuiberts_basis_path_length_lower` | full abstract adjacent-basis-path form of Lemma 56 | lean_checked; three standard axioms |
| `bachHuiberts_d2_final_constant` | explicit `d=2` small-noise substitution into the final path constant | lean_checked; three standard axioms |

Source: `proof/Tier3_BachHuibertsRoundness.lean`; SHA-256
`15162d2ebc92903e4040ca9162c5f5525d6c05366801d43d0ec08f8e7f391c97`;
594 lines, 23 printed roots, standalone `lake env lean` exit 0. The capstone now
has a bounded finite-path form; the prior infinite-chain form is a wrapper.

### Tier-3 — polar incidence, sphere net, and Gaussian event

| source / theorem group | content | evidence |
|---|---|---|
| `Tier3_PolarIncidence.lean` | closed/convex polar faces; minimum-norm face point and first-order condition; primal-ball ↔ reciprocal-polar-ball inclusions; direct exposed-face diameter from the ball sandwich; active normals and objective rays in the same exposed face; endpoint estimates | lean_checked; 20 roots; three standard axioms |
| `exists_dense_unit_sphere_finset_natFloor` | finite internal `η`-net of the unit sphere with `card ≤ ⌊(4/η)^d⌋₊` (Lemma 54) | lean_checked; three standard axioms |
| `measure_exists_norm_gt_le_of_coordinate_gaussianReal` | exact centered-Gaussian coordinate laws imply the simultaneous finite-row Euclidean-norm tail bound, with no independence needed by the union step | lean_checked; three standard axioms |
| `gaussian_tail_factor_four_mul_sqrt_log` | the paper's threshold `4σ√(log n)` simplifies the scalar failure factor exactly to `2/n⁸` | lean_checked; three standard axioms |
| `measure_exists_norm_gt_four_mul_sqrt_log_le` | simultaneous row event after substitution: failure at most `2·rows·dim/n⁸` | lean_checked; three standard axioms |

Source digests and audit sizes:

- `Tier3_PolarIncidence.lean`: SHA-256 `85fb320b8556a5e843702323aa370df8ecb366c81129ed41f5a2a2b27d7acd24`, 423 lines, 20 roots.
- `Tier3_SphereNet.lean`: SHA-256 `5d352768419760341928508e334cc4f5d0355291e4e0431b9e175bad0eb9f9bc`, 173 lines, 3 roots.
- `Tier3_GaussianTail.lean`: SHA-256 `f7a05056535e0c0738b5bbea010172f5e302fd77469ca748ab8cb64165ee7591`, 288 lines, 13 roots.

### Tier-3 — concrete normalization, vertex bases, and genericity

| source | checked bridge | digest / audit size |
|---|---|---|
| `Tier3_AffineGenericity.lean` | augmented affine general position forbids `d+1` active constraints; active-set cardinality; normalization preserves general position | `46b422530a0ed2f6eec0add52663c7f8e861c7dac578be9a8d5902761ce093bb`; 117 lines; 5 roots |
| `Tier3_NormalizedLPBasis.lean` | positive RHS normalization; concrete feasible bases and one-index-exchange paths; bounded natural-index view of exactly `k` charged pivots; vertex uniqueness | `12bf7b8e7fa9ee9f8e3a46f9c1d55df962f6abd96ffb656621f7ae90715f5ea9`; 182 lines; 8 roots |
| `Tier3_GenericityProbability.lean` | AC induction for the genuine `Measure.pi` law; arbitrary-finite reindexing; projective subset marginals; one joint sample simultaneously generic on every subset; Euclidean-volume interface | `a7ef5947ec66665290bea121aa73b2787ba2cb2534352dce872d536b8b243b61`; 336 lines; 13 roots |
| `Tier3_GaussianAffineGenericityAssembly.lean` | exact translated/scaled augmented-row Gaussian laws satisfy simultaneous affine general position under one joint product sample | `5ee08e7187dc5de3a3817882a0f4bef6eb8aa0ff5389bb807026611a7ee9022b`; 45 lines; 1 root |
| `Tier3_FinitePathLowerBoundAssembly.lean` | every finite charged `NormalizedSimplexPath` satisfying the polar endpoint/face estimates obeys the Bach–Huiberts pivot lower bound | `89814b9f9ac597d7932418ed39963e37a274d70b4ef78bd32c2fd02041e63563`; 40 lines; 1 root |
| `Tier3_RepairedPivotSemantics.lean` | objective-independent initializer; certified finite charged execution; exact equality with Tier-2 `pivotCount`; common antipodal start | `d76d424f7f80123293523fc74ba479c0fae9e874facdd3cac899717a399e7db6`; 77 lines; 3 roots |
| `Tier3_ExecutionLowerBoundAssembly.lean` | aligns repaired charged states with a normalized basis path and rewrites the geometric lower bound directly onto Tier-2 `pivotCount` | `22c140c0076bbad217ed9b9762f1cf59ec925acad48b165f515099c627fdbf39`; 52 lines; 1 root |
| `Tier3_GoodEventAssembly.lean` | adding failure of an a.s. genericity event leaves a quantitative bad-event probability unchanged | `2e41b661a961d3d6c73993e9e8ab259b2968d2110e8481fd56ad26ced3b797e7`; 73 lines; 4 roots |
| `Tier3_BachHuibertsD2Parameters.lean` | exact `d=2` threshold domination and `6n/n⁸ ≤ n⁻²` parameter arithmetic | `d41940147cf148f7fccdf04e5bd806938518b05f03c6f98b556ef449f605a08f`; 126 lines; 5 roots |
| `Tier3_D2TailGenericityAssembly.lean` | combines normal/RHS tails and a.s. genericity into one `n⁻²` failure bound, plus a pointwise good-event eliminator | `dc7c78de5040e5cff7c0f35d75ba012aeb9c5e47c45fd5fb215ccbcc2410a4f5`; 121 lines; 2 roots |
| `Tier3_ExactGaussianD2Assembly.lean` | derives all coordinate marginals from the same exact product augmented-row law and proves the one-sample tail/genericity event | `e80bdbc21035befaecaa0167875e83122bac9fdec3edbc08c442316454e00d45`; 179 lines; 4 roots |
| `Tier3_Theorem57DeterministicAssembly.lean` | raw near-spherical inequalities → roundness → polar face/endpoint estimates → charged Tier-2 `pivotCount` lower bound | `fc28c38210c3a8c0d27cf4d5080123f70a6fbed3303e317f932a01ba3a920d49`; 163 lines; 1 root |
| `Tier3_VertexActiveBasis.lean` | every extreme point has spanning active normals and a full active basis; under nondegeneracy its complete active set has cardinality `d` and is linearly independent | `61f87c2eefc127c2c2464909a91f3480f3c7e7e9d52574bf3601e18b286d52bb`; 198 lines; 5 roots |

All eighteen Tier-3 lower-bound component/assembly files compile in the pinned
environment, and every printed root uses only `[propext, Classical.choice,
Quot.sound]`. The module roots remain `lean_checked`; four faithful
resolution-critical companion statements were subsequently replayed through the
tracked proof service and are `kernel_verified` (details immediately above and in
`evidence.md`).

lean_checked (not separately tracked): M1a.3 `perturbed_coeff_some_near_threshold`.

All tracked roots `#print axioms` = `[propext, Classical.choice, Quot.sound]` (T2.6's
tracked inlined form is axiom-free); each proof snapshot `lake env lean` exit 0. Env
`9e26d28e…`; toolchain `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`. Fidelity
`attested` throughout (dev-mode; caps at `kernel_verified`, never `certified`).

Proof snapshots under [proof/](proof/):
`Milestone1_*`, `Milestone1a_*`, `Milestone2_0_*`, `Milestone2_SubspaceAntiConcentration.lean`
(M2.1+M2.2), `Milestone2_GEOM_RudelsonVershynin.lean`, `Milestone2_DEF_SigmaMin.lean`,
`Milestone2_COND_{PolyNullBase,PiAbsCont,StdGaussianAC,ScaledGaussianAC,ColumnIndependence,ConditionalDistBound,FubiniGlue,AdjugateNormal,HyperplaneNull}.lean`,
`Milestone2_UNION_SigmaReduction.lean`, `Tier2_LPModel_FeasibleConvex.lean`,
`Tier2_PivotCount.lean`, `Tier3_AntipodalLowerBoundReduction.lean`, and
`Tier3_{BachHuibertsRoundness,PolarIncidence,SphereNet,GaussianTail,AffineGenericity,NormalizedLPBasis,GenericityProbability,GaussianAffineGenericityAssembly,FinitePathLowerBoundAssembly,RepairedPivotSemantics,ExecutionLowerBoundAssembly,VertexActiveBasis,GoodEventAssembly,BachHuibertsD2Parameters,D2TailGenericityAssembly,ExactGaussianD2Assembly,Theorem57DeterministicAssembly}.lean`.

## What is proved vs. what remains — the σ_min lower-tail

The target is the Sankar–Spielman–Teng estimate `P(σ_min(Ā + G) ≤ ε) ≤ C·n·ε/σ`,
`G` entrywise `N(0,σ²)`. Its pieces:

- **Deterministic backbone — COMPLETE.** M2-GEOM/GEOMσ reduce `σ_min` to per-column
  distances (`σ_min(A) ≥ n^{-1/2}·min_i dist(a_i, span others)`); M2-DEF fixes the
  `σ_min` definition; M2-UNION gives the set inclusion `{σ_min ≤ ε} ⊆ ⋃_i {dist_i ≤ √n·ε}`.
- **Fixed-subspace anti-concentration — COMPLETE.** M2-CONDc: `P(dist(x,W) ≤ ε) ≤
  2ε/(σ√2π)` for any fixed `W` with a unit normal (via M2.0/M2.2). Because `n−1`
  vectors can never span `ℝⁿ`, the required normal always exists.
- **Conditioning machinery — COMPLETE.** M2-COND3a (independent columns of the product
  Gaussian) + M2-COND3c (Fubini slice→product promotion).
- **A.s.-nonsingularity in the EXACT smoothed model — COMPLETE.** M2-AC4: the perturbed
  column `c + σ·G` has law `≪ volume` and misses any fixed proper subspace a.s., so
  `det ≠ 0` a.s. This was the single genuinely-hard analytic obstruction; it is now
  kernel-verified (built on the AC0–AC3 tower, incl. two genuine Mathlib gap-fillers:
  finite-product absolute continuity and product-Gaussian absolute continuity).

**Remaining (assembly only): the final probabilistic composition.** Combine M2-UNION
(inclusion) → M2-COND3a (independence) → M2-CONDc (per-column bound with `W = span of
the other columns`, existence of the normal guaranteed by M2-AC4's nonsingularity) →
M2-COND3c (Fubini) → M1a-style union over the `n` columns. Every ingredient is
kernel-verified; what is left is wiring them into one module. This is the precise next
target and spans no new mathematics — only a multi-lemma module assembly.

## Tier-2 arc — what is proved vs. what remains

The arc is COMPLETE up to the trivial worst-case bound: feasible region convex + closed
(T2.1–2) → LP optimum exists (T2.3) → vertices exist (T2.4) → strict-improve path ≤
#vertices (T2.5) → abstract pivot count `T_R` finite (T2.6) → `Sm_R := ⨆ 𝔼[T_R]` and
`Sm_R ≤ B` (T2.7). With `B = #vertices` this is `Sm_R ≤ #vertices` — exactly the
quantity R1 asks to improve to `O(n·polylog(m,n,1/σ))`.

Remaining to make R1 fully Lean-expressible (each a real milestone, none the open
conjecture): a concrete deterministic pivot rule as an adjacent-vertex transition on the
perturbed polytope; the smoothing product measure on `(Ā,b̄,c̄) + noise`; and `𝔼[T_R]`
as an integral against it. **Tooling boundary (candidate upstream issue):** a tracked
root statement must elaborate standalone, so it cannot reference a module-local recursive
`def`; T2.6 was tracked by inlining `Nat.rec`. A SubmitModule "define-then-prove" flow
would let recursive `T_R`/`Sm_R` rungs be tracked in natural `def` form.

## Known walls (do not re-derive)

- **Initialization semantics:** the literal root still permits an oracle initializer,
  but `Tier3_RepairedPivotSemantics.lean` now formalizes the conventional repair:
  the initializer cannot inspect the objective and every counted transition is charged.
- **Published theorem not yet assembled end-to-end:** Bach–Huiberts Theorem 57 remains
  literature-supported rather than repository-proved. Lemma 54, Lemma 55, the abstract
  basis-path form of Lemma 56, polar incidence/objective rays, polar minimum-norm points,
  reciprocal ball inclusions, direct polar-face diameter, finite-row Gaussian tail,
  positive-RHS normalization, concrete basis paths, extreme-point active-basis
  existence/uniqueness, affine-general-position consequences, and the abstract
  absolute-continuity genericity induction and exact Gaussian-row assembly are now
  Lean-checked. A finite charged one-index-exchange path now feeds the lower-bound
  capstone directly, and the repaired execution is equal to Tier-2 `pivotCount` with
  a definitional common antipodal start. The combined wrapper places the lower bound
  directly on that count. The exact one-sample probability-event, `d=2` parameter
  assembly, and deterministic end-to-end roundness/incidence/execution wrapper are now
  checked as well. Remaining root packaging identifies a good sample's split augmented
  rows with the raw `(A,b)` hypotheses and applies the tracked antipodal/rescaling spine.
- **General exact order:** still open after model repair. The current upper bound is
  `O(σ^{-1/2}d^{11/4}log(m)^{7/4})` in the row-normalized literature model; upper and
  lower bounds still differ in dimension and constraint dependence.

## Attempted routes / lessons

- M1, M1a.1, M1a.2, M2.1, M2.2 pass@1. M2.0 took 2 submissions (first kernel_fail = a
  helper-transport artifact, not a math gap). The σ_min tower and Tier-2 arc were all
  pass@1. Method: (1) read the actual pinned Mathlib source for each new API; (2) write
  the EXACT flattened module assembly to a scratch `.lean` and `lake env lean` it; (3)
  submit byte-identical.
- **Transport rule (reconfirmed):** helper `proof_term`s must be single-line semicolon
  chains with every inline `by` parenthesized `(by …)`; bullets (`·`) do not survive
  `flat_tactic_sequence`; only the root supports `raw_lean_block`. First use of an
  `open MeasureTheory` manifest directive (for `∫⁻`) in M2-COND3c.
- **Mathlib gap-fillers found and filled this campaign:** no finite-product
  (`Measure.pi`) absolute-continuity lemma (only binary `AbsolutelyContinuous.prod`); no
  multivariate-Gaussian absolute continuity (only 1-D `gaussianReal_absolutelyContinuous`);
  no general-`n` cross product (`Matrix.crossProduct` is `Fin 3` only) — the adjugate row
  fills the normal-direction role. These are formalization-novel components.
- Tracked statements are fixed at universe 0 (`Type`) / `Fin n` for hashing; the
  underlying mathematics is general.

## Next-cycle directive

Highest-leverage target: package the now-checked exact one-sample event and deterministic
Theorem 57 pivot-count wrapper with the tracked antipodal expectation, global-norm scaling,
and asymptotic contradiction as the repaired root statement.

The σ_min lower-tail composition remains valuable reusable formalization, but it is no
longer the root-critical next step. Do not seek a near-linear upper bound for the displayed
polylogarithmic-noise target: the current primary literature rules that dependence out
under standard simplex semantics.
