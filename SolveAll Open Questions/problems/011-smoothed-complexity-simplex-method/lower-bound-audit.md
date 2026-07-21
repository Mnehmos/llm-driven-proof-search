# Lower-bound audit — the stated near-linear target is not a sound open conjecture

**Updated 2026-07-19 after checking the current primary literature.**

## Finding

The repository's previous frontier was stale. Bach and Huiberts, *Optimal
Smoothed Analysis of the Simplex Method*, arXiv:2504.04197v2 (23 May 2026),
prove an upper bound

\[
  O\!\left(\tau^{-1/2}d^{11/4}\log(M)^{7/4}\right)
\]

and a high-probability lower bound on the combinatorial diameter of a smoothed
polyhedron. Their Theorem 57 says that, for fixed `d ≥ 2`, sufficiently small
noise `τ`, and `M = ⌊(4/τ)^d⌋` constraints, there are centers for which, with
probability at least `1-M^{-d}`, every simplex path between the minimizing and
maximizing vertices of every nonzero objective has length at least

\[
  L_d(\tau)
  = \frac{\sqrt{d-1}}
           {24\sqrt{\tau\sqrt{\log(4/\tau)}}}.
\]

The STOC 2026 paper by Bach, Black, Kafer, and Huiberts summarizes this as a
lower bound applying to **all pivot rules**. Sources:

- [Bach–Huiberts, arXiv:2504.04197v2](https://arxiv.org/abs/2504.04197)
- [Bach–Black–Kafer–Huiberts, STOC 2026](https://doi.org/10.1145/3798129.3800742)

This changes the status of SolveAll #11. Its displayed example asks for only
polylogarithmic dependence on `1/σ`. Under standard simplex semantics, that
dependence is ruled out by the published lower bound. Under the page's literal,
unrestricted wording for “initialization,” the target has the opposite defect:
an initializer can solve the LP by uncharged non-pivot work, start at an optimum,
and make the pivot count zero. The definition therefore needs repair before the
existence question has a unique truth value.

## Adapting the lower bound to SolveAll's global norm convention

The literature theorem uses a rowwise-normalized center and perturbs `A,b` with
standard deviation `τ`. SolveAll instead puts the entire stacked center in one
unit ball and also perturbs `c`. The mismatch does not remove the obstruction.

It is enough to take `d=2`. Let

\[
  M=\left\lfloor(4/\tau)^2\right\rfloor,
  \qquad \alpha=(2M)^{-1/2},
  \qquad \sigma=\alpha\tau.
\]

In the Bach–Huiberts construction the constraint normals have norm one and the
right-hand sides equal one. With objective center zero,

\[
  \|\alpha(\bar A,\bar b,0)\|^2
  =\alpha^2(M+M)=1.
\]

Thus the scaled center is admissible for SolveAll. Multiplying all constraints
by the same positive `α` does not change the feasible polytope, while scaled
Gaussian noise has standard deviation `ατ=σ`. The theorem's event is simultaneous
over every nonzero objective, so an additional independent
`c\sim N(0,\sigma^2I_2)` does not change the diameter statement and is nonzero
almost surely.

For small `τ`, `8/τ² ≤ M ≤ 16/τ²`, hence

\[
  \frac{\tau^2}{4\sqrt2}\le\sigma\le\frac{\tau^2}{4},
  \qquad M\le \frac4\sigma.
\]

Consequently the diameter lower bound becomes

\[
  L_2(\tau)
  =\Omega\!\left(
       \frac{\sigma^{-1/4}}{\log(1/\sigma)^{1/4}}
     \right),
\]

whereas, along the same sequence,

\[
  \log(Md/\sigma)+1=O(\log(1/\sigma)).
\]

Every fixed power of a logarithm is `o(σ^{-1/4})`. Therefore no constants
`C,k` can make the displayed R1 bound hold along this family once the diameter
lower bound is transferred to the rule's pivot count.

## Objective noise and the initialization obligation

For the standard two-phase simplex method, Phase I selects a feasible starting
basis from `(A,b)` and is independent of the Phase II objective. Fix the smoothed
polytope and call this start `s`. For objective `c`, let `v_+(c)` and `v_-(c)` be
maximizing and minimizing vertices. Shortest-path distance in the 1-skeleton gives

\[
  \operatorname{dist}(v_+,v_-)
  \le \operatorname{dist}(s,v_+)+\operatorname{dist}(s,v_-).
\]

The two terms lower-bound the pivot counts for objectives `c` and `-c`. Since a
centered Gaussian objective has the same law as its negation, integration yields

\[
  2\,\mathbb E[T_R(A,b,c)]\ge L_2(\tau)
\]

on the high-probability diameter event, and hence

\[
  \mathbb E[T_R]\ge \tfrac12(1-M^{-2})L_2(\tau).
\]

This short bridge is Lean-checked in
[`proof/Tier3_AntipodalLowerBoundReduction.lean`](proof/Tier3_AntipodalLowerBoundReduction.lean):

- `oracle_initialization_gives_zero_pivots` — the literal uncharged-initialization
  loophole;
- `antipodal_pivot_sum_ge` — the graph-distance triangle reduction;
- `antipodal_one_run_ge_half` — one sign costs at least `⌈L/2⌉`;
- `symmetric_lintegral_pair_lower_bound` — the measure-preserving symmetry and
  expectation step.
- `polylog_with_quarter_isLittleO_quarterPower` — the exact
  `log(x)^(k+1/4)=o(x^(1/4))` asymptotic separation.
- `scaled_noise_between_quadratic_bounds` — the constant-factor conversion
  `σ=Θ(τ²)`.
- `half_le_natFloor_and_natFloor_le` — the floor bound behind
  `8/τ²≤M≤16/τ²`.

The file compiles standalone with Lean `v4.32.0-rc1` and
Mathlib `360da6fa`; SHA-256
`e288317e78c09fca80c7cf02a7129b1bda3c2ea7c4f735f6e04c1fc1027e7b40`.
The oracle and two combinatorial roots use `[propext, Quot.sound]`; the analytic
roots use the three standard axioms `[propext, Classical.choice, Quot.sound]`.

## Deterministic geometry imported from Theorem 57

[`proof/Tier3_BachHuibertsRoundness.lean`](proof/Tier3_BachHuibertsRoundness.lean)
now Lean-checks the following published deterministic steps:

- Lemma 55 in full: an `η`-dense unit-normal family, `η`-small perturbations,
  and right-hand sides in `[1-η,1+η]` imply
  `(1-2η)B₂ ⊆ P ⊆ (1+4η)B₂`;
- the reciprocal-radius relaxations used for the polar body;
- the closest-point calculation `‖v-y‖ ≤ √(14η)` and the resulting pairwise
  polar-facet estimate `‖v-w‖ ≤ 2√(14η)`;
- the metric telescoping and scalar conclusion in Lemma 56 that turn `ℓ`
  short facet links into the path lower bound `(d-1)(2/(Rγ)-3)`.
- the finite-basis overlap fact used to choose the paper's block representatives:
  after fewer than `d` adjacent exchanges, two `d`-element bases still share an index.
- the full abstract adjacent-basis-path form of Lemma 56.
- the explicit `d=2`, small-noise final constant needed by the scaled
  counterexample family.

The file compiles standalone in the same pinned environment; SHA-256
`15162d2ebc92903e4040ca9162c5f5525d6c05366801d43d0ec08f8e7f391c97`.
Every printed root uses only `[propext, Classical.choice, Quot.sound]`. The
evidence label is `lean_checked`, not `kernel_verified`, because no tracked
proof-service episode was available.

Seven companion files now check the other reusable pieces of the published proof:

- `Tier3_PolarIncidence.lean` proves that polar bodies and their exposed faces are
  closed and convex; obtains the minimum-norm face point and its first-order condition
  from the Hilbert projection theorem; reverses primal Euclidean-ball inclusions into
  reciprocal polar-ball inclusions; and puts active normals and normalized objective
  rays in the same exposed face, and derives the paper's exposed-face diameter
  directly from the primal ball sandwich. SHA-256
  `85fb320b8556a5e843702323aa370df8ecb366c81129ed41f5a2a2b27d7acd24`.
- `Tier3_SphereNet.lean` proves Lemma 54's finite internal sphere net, including the
  natural-floor cardinal bound. SHA-256
  `5d352768419760341928508e334cc4f5d0355291e4e0431b9e175bad0eb9f9bc`.
- `Tier3_GaussianTail.lean` derives centered-Gaussian Chernoff bounds from Mathlib's
  exact MGF, lifts them to finite families and Euclidean row norms, and exposes an
  exact pushforward-law interface for all rows at once. It also checks the paper's
  substitution `t=4σ√(log n)`, yielding the exact scalar factor `2/n⁸` and the
  simultaneous row failure bound `2·rows·dim/n⁸`. SHA-256
  `f7a05056535e0c0738b5bbea010172f5e302fd77469ca748ab8cb64165ee7591`.
- `Tier3_AffineGenericity.lean` proves that augmented affine general position
  forbids `d+1` active constraints and is preserved by positive normalization.
- `Tier3_NormalizedLPBasis.lean` identifies the original and normalized feasible
  polyhedra and defines concrete full bases and one-index-exchange simplex paths.
- `Tier3_VertexActiveBasis.lean` proves that every extreme point has spanning
  active normals; under nondegeneracy its whole active set is a unique full basis.
- `Tier3_GenericityProbability.lean` works directly with the genuine joint
  `Measure.pi` law: product induction, finite reindexing, projective subset
  marginals, and a finite intersection prove that one sample is simultaneously
  generic on every subset up to ambient dimension.
- `Tier3_GaussianAffineGenericityAssembly.lean` composes that theorem with the
  checked translated/scaled Gaussian absolute-continuity root, yielding exact
  a.s. affine general position for the augmented smoothed rows.
- `Tier3_FinitePathLowerBoundAssembly.lean` turns a concrete finite charged
  `NormalizedSimplexPath` of exactly `k` one-index exchanges directly into the
  Bach–Huiberts lower bound; the capstone no longer assumes an infinite chain.
- `Tier3_RepairedPivotSemantics.lean` makes the conventional repair explicit:
  Phase-I initialization cannot inspect the objective, every recorded transition
  is charged, its length equals Tier-2 `pivotCount`, and antipodal runs share a start.

The execution/basis-path wrapper and the exact one-sample Gaussian good event are now
checked. The latter derives both coordinate tail laws and simultaneous affine general
position from the same translated/scaled augmented-row product measure, with total
failure at most `n⁻²`. `theorem57_deterministic_pivotCount_lower` now supplies the
roundness, normalization, polar-incidence, endpoint, and charged-execution wrapper.
The remaining obligation is root packaging: split a good augmented-row sample into
the raw `(A,b)` hypotheses and invoke the antipodal/rescaling contradiction.

## Honest resolution status

There are now three distinct statements, and they must not be conflated:

1. **Literal R1 with unrestricted, uncharged initialization:** ill-posed and
   vacuously satisfiable by initializing at an optimum. The pointwise zero-pivot
   construction is Lean-checked as `oracle_initialization_gives_zero_pivots`.
2. **R1 under the conventional objective-independent Phase I / counted edge-walk
   semantics:** the displayed `n·polylog(m,n,1/σ)` bound is **disproved**, using
   Bach–Huiberts plus the Lean-checked reduction above.
3. **The general asymptotic order of `inf_R Sm_R`:** still open after the model is
   repaired. The 2026 upper and lower bounds agree on the `σ^{-1/2}` exponent in
   the row-normalized literature model up to logarithms, but not on dimension or
   constraint-count dependence; translating optimal rates under SolveAll's global
   norm convention is also nontrivial.

Accordingly, this repository should not emit an unqualified `RESOLUTION: PROVED`
or `RESOLUTION: DISPROVED` for the compound page. It should report that the
page's example existence target is either vacuous or false depending on the
missing initialization semantics, and request a corrected problem statement.
