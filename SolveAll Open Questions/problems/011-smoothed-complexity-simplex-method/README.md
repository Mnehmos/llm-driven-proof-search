# Smoothed Complexity of the Simplex Method

**Status:** Stated existence target requires repair; general exact order unsolved  
**Importance:** Notable
**Source:** Posed by Spielman & Teng (implicit) (2004)

## Categories

- Optimization & Variational Methods
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #11 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix integers $n \ge 1$ (variables) and $m \ge n$ (constraints). Consider linear programs

$
\max_{x \in \mathbb R^n} c^\top x \quad \text{subject to} \quad Ax \le b,
$

with $A \in \mathbb R^{m \times n}$ , $b \in \mathbb R^m$ , $c \in \mathbb R^n$ . A simplex pivot rule $R$ means a complete deterministic specification of entering/leaving choices (including tie-breaking and initialization details), so the pivot count is well defined on nondegenerate instances.

Convention for this problem: in the Gaussian smoothed model, an adversary chooses $(\bar A,\bar b,\bar c)$ with $\|(\bar A,\bar b,\bar c)\|\le 1$ , then independent Gaussian noise is added to every scalar coefficient of $A,b,c$ :

$
A=\bar A+G,\qquad b=\bar b+h,\qquad c=\bar c+g,
$

where entries of $G,h,g$ are i.i.d. $N(0,\sigma^2)$ with $\sigma\in(0,1]$ . Let $T_R(A,b,c)$ be the total number of pivots performed by the full simplex algorithm using rule $R$ . Define

$
\mathrm{Sm}_R(m,n,\sigma):=\sup_{\|(\bar A,\bar b,\bar c)\|\le 1}\ \mathbb E\!\left[T_R(\bar A+G,\bar b+h,\bar c+g)\right].
$

### Unsolved Problem

Does there exist a pivot rule $R$ with near-linear smoothed complexity (up to polylogarithmic factors), uniformly for all $m\ge n$ and $\sigma\in(0,1]$ ; for example

$
\mathrm{Sm}_R(m,n,\sigma)\le O\!\left(n\cdot \mathrm{polylog}(m,n,1/\sigma)\right)?
$

More generally, what is the correct asymptotic order of

$
\inf_R \mathrm{Sm}_R(m,n,\sigma)
$

as a function of $m,n,\sigma$ under this perturbation model?

## Significance & Implications

The simplex method is the most widely used algorithm for linear programming, and its strong practical performance has motivated decades of theory. [Spielman & Teng (2004)](#references) established polynomial smoothed complexity for shadow vertex, and later work substantially improved parameter dependence. However, current upper and lower bounds are still separated, and a tight characterization of optimal smoothed complexity across pivot rules remains open.

## Known Partial Results

- [Spielman & Teng (2004)](#references) : first polynomial smoothed bound for a shadow-vertex simplex algorithm (with very large exponents).

- [Dadush & Huiberts (2018)](#references) : major simplification and improvement; STOC-version bound includes a $d^5$ term (often cited as roughly $O(d^2\sqrt{\log n}\,\sigma^{-2}+d^5\log^{3/2}n)$ ).

- [Huiberts et al. (2023)](#references) : improved upper bound to $O(\sigma^{-3/2} d^{13/4}\log^{7/4} n)$ and proved a first non-trivial lower bound for shadow-vertex simplex in the smoothed setting.

- [Huiberts et al. (2025)](#references) : journal version consolidating and extending the STOC 2023 analysis.

- [Bach & Huiberts (2025/2026)](https://arxiv.org/abs/2504.04197) : improved upper
  bound `O(σ^{-1/2}d^{11/4}log(m)^{7/4})` and a high-probability
  `Ω(σ^{-1/2}d^{1/2}log(1/σ)^{-1/4})` combinatorial-diameter lower bound for
  `m=⌊(4/σ)^d⌋`; the v2 manuscript is dated 23 May 2026.

- [Bach, Black, Kafer & Huiberts (STOC 2026)](https://doi.org/10.1145/3798129.3800742) :
  explicitly summarizes the Bach–Huiberts lower bound as applying to all pivot
  rules.

- Despite this progress, the optimal dependence on $(m,n,\sigma)$ for the best pivot rule is still not tightly characterized.

## References

[1]

 [Smoothed analysis of algorithms: Why the simplex algorithm usually takes polynomial time](https://doi.org/10.1145/990308.990310) 

Daniel Spielman, Shang-Hua Teng (2004)

Journal of the ACM

📍 Section 6.2 (further analysis/open directions for simplex pivot rules under smoothed analysis), J. ACM 51(3):385-463.

 [DOI ↗](https://doi.org/10.1145/990308.990310) [2]

 [Smoothed analysis of algorithms: Why the simplex algorithm usually takes polynomial time](https://doi.org/10.1145/380752.380813) 

Daniel A. Spielman, Shang-Hua Teng (2001)

Proceedings of the 33rd Annual ACM Symposium on Theory of Computing (STOC)

📍 Theorem 1.1 (polynomial smoothed complexity for a shadow-vertex simplex algorithm), STOC 2001.

 [DOI ↗](https://doi.org/10.1145/380752.380813) [3]

 [A friendly smoothed analysis of the simplex method](https://doi.org/10.1145/3188745.3188826) 

Daniel Dadush, Sophie Huiberts (2018)

Proceedings of the 50th Annual ACM STOC

📍 Main theorem in the STOC 2018 version (bound with a $d^5$ term).

 [DOI ↗](https://doi.org/10.1145/3188745.3188826) [4]

 [Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method](https://doi.org/10.1145/3564246.3585124) 

Sophie Huiberts, Yin Tat Lee, Xinzhi Zhang (2023)

Proceedings of the 55th Annual ACM STOC

📍 Main STOC 2023 theorem: improved upper bound and first non-trivial lower bound for shadow-vertex simplex.

 [DOI ↗](https://doi.org/10.1145/3564246.3585124) [5]

 [Upper and Lower Bounds on the Smoothed Complexity of the Simplex Method](https://doi.org/10.46298/theoretics.25.23) 

Sophie Huiberts, Yin Tat Lee, Xinzhi Zhang (2025)

TheoretiCS

📍 Journal version (TheoretiCS 2025) of STOC 2023 results, with full proofs and refined presentation of upper/lower bounds.

 [DOI ↗](https://doi.org/10.46298/theoretics.25.23) [arXiv ↗](https://arxiv.org/abs/2211.11860)

## Notes / Progress

**2026 correction:** the displayed `n·polylog(m,n,1/σ)` target is not a sound
open conjecture as currently specified. Under conventional simplex semantics,
the Bach–Huiberts all-rule lower bound rules out its polylogarithmic `1/σ`
dependence. Under literal unrestricted initialization, a rule can do an uncharged
LP solve, initialize at an optimum, and use zero pivots. The exact order of
`inf_R Sm_R` remains open after repairing that ambiguity. The detailed reduction
is [lower-bound-audit.md](lower-bound-audit.md).

A staged companion-lemma campaign runs in this folder. Full per-theorem records
(hashes, episodes, obligations, axiom reports) are in
[evidence.md](evidence.md); the narrative is [whitepaper.md](whitepaper.md); the
machine-readable frontier is [state.md](state.md); staging is
[attack-plan.md](attack-plan.md).

All tracked roots use at most the three standard axioms
`[propext, Classical.choice, Quot.sound]` (several use fewer; the abstract
pivot-count bound is axiom-free); each proof snapshot recompiles
standalone under `lake env lean` (exit 0), toolchain
`leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa`; fidelity `attested` throughout
(dev-mode, caps at `kernel_verified`, never `certified`).

### Front 1 — Gaussian anti-concentration base (DONE)

- **M1** `gaussian_anticoncentration` — `X ~ N(m,σ²) ⇒ Pr[|X−t|≤ε] ≤ 2ε/(σ√(2π))`,
  in this problem's own `A = Ā+G` model. The small-ball estimate every paper in the
  literature opens with; new formalization (Mathlib has the density machinery, no
  anti-concentration lemma). Problem `d2f3e8c3…`, episode `1f3255d1…`, pass@1.
- **M1a** finite-family union bound (no independence): `gaussian_anticoncentration_union`
  (M1a.1, `P(∃ i,|X_i−t_i|≤ε_i) ≤ ∑ 2ε_i/(σ_i√2π)`), the homogeneous `k·2ε/(σ√2π)`
  (M1a.2), and the perturbed-coefficient bridge (M1a.3, lean_checked).
- **M2.0 → M2.1 → M2.2** geometric anti-concentration:
  `gaussian_hyperplane_anticoncentration` (arbitrary-center hyperplane slab) lifts
  through a codim-2 product to the **master** `gaussian_subspace_anticoncentration`
  (arbitrary-orientation codimension-`k`, sharp `(2ε/(σ√2π))^k`, via independence of
  the projections under `σ²I`).

### Front 2 — smallest-singular-value lower-tail (A-COND, near-complete)

The probabilistic core of Spielman–Teng: `P(σ_min(Ā+G) ≤ ε) ≤ C·n·ε/σ`. Mathlib has
no `smallestSingularValue` and no singular-value/determinant anti-concentration; this
campaign built the pieces.

- **Deterministic Rudelson–Vershynin backbone (complete):**
  `abs_coord_mul_infDist_span_le_norm_sum`, `rv_min_dist_bound`, `sigmaMin_cols_ge`
  (+ `sigmaMin_lower_bound`), `sigmaMin_le_imp_exists_col_dist_le`.
- **Fixed-subspace bound + conditioning (complete):** `gaussian_dist_subspace_le`,
  `matrix_gaussian_columns_iIndepFun`, `prod_measure_le_of_slice_le`.
- **Absolute-continuity tower + a.s.-nonsingularity in the EXACT smoothed model
  (complete — the crux discharged):** `poly_root_set_measure_zero`,
  `pi_absolutelyContinuous` and `gaussian_pi_absolutelyContinuous` (**genuine Mathlib
  gap-fillers** — no finite-product / `Measure.pi` a.c. lemma exists),
  `stdGaussian_absolutelyContinuous`, and `scaled_gaussian_ac` /
  `scaled_gaussian_subspace_measure_zero` — the perturbed column `c+σ·G` has law
  `≪ volume` and misses any fixed proper subspace a.s., so `det(Ā+G) ≠ 0` a.s.

  Remaining: **assembly only** — one module wiring the verified pieces into the σ_min
  lower-tail. No new mathematics; it would be the first Lean formalization of the
  σ_min core in the smoothed model.

### Front 3 — LP / pivot-rule model (Tier 2, complete arc)

R1 is not Lean-expressible without a formal LP/pivot model (none exists in Mathlib or
any public Lean corpus found). A complete arc: feasible region convex + closed
(`lp_feasible_convex`, `lp_feasible_closed`) → LP optimum exists (`lp_optimum_exists`)
→ vertices exist (`lp_feasible_extremePoints_nonempty`, Krein–Milman) → strict-improve
path ≤ #vertices (`simplex_path_length_le_card`) → abstract pivot count `T_R` finite
(`pivotCount_le_fuel`, axiom-free) → **capstone** `smoothedComplexity_le_of_forall_le`:
`Sm_R := ⨆ 𝔼[T_R]` with `Sm_R ≤ B`. Taking `B = #vertices` gives the **trivial
worst-case** `Sm_R ≤ #vertices` — exactly the quantity R1 asks to improve to
`O(n·polylog(m,n,1/σ))`.

Remaining to make R1 fully Lean-expressible (each a real milestone, none the open
conjecture): a concrete adjacent-vertex pivot rule, the smoothing product measure,
and `𝔼[T_R]` as an integral against it.

### Front 4 — lower-bound correction (ACTIVE)

`proof/Tier3_AntipodalLowerBoundReduction.lean` Lean-checks the bridge from a
max–min graph-diameter lower bound to an expected pivot lower bound under symmetric
Gaussian objective noise and an objective-independent Phase I start. Combined with
Bach–Huiberts Theorem 57 and a global-norm rescaling, this gives
`Ω(σ^{-1/4}log(1/σ)^{-1/4})` in SolveAll's convention at fixed dimension two,
contradicting every fixed polylogarithmic `1/σ` bound. The published geometric
theorem is currently `literature_supported`, but
`proof/Tier3_BachHuibertsRoundness.lean` now Lean-checks its deterministic core:
the full near-ball sandwich (Lemma 55), reciprocal polar radii, the
`2√(14η)`/`8√η` facet-diameter estimates, and the metric-chain, adjacent-basis
overlap, and full abstract basis-path form of Lemma 56. Companion checked files now
supply polar incidence and objective rays, direct exposed-face diameter from the ball
sandwich, Lemma 54's finite sphere net, and the simultaneous finite-row Gaussian norm
tail from exact coordinate laws. New concrete modules prove positive-RHS normalization,
full active bases at extreme points, affine-general-position nondegeneracy, and the
exact joint-product/projective-marginal theorem for simultaneous genericity. The
paper's threshold substitution and the final `d=2` path constant are also checked.
The exact translated/scaled augmented-row Gaussian genericity assembly is checked too,
and a finite charged `NormalizedSimplexPath` now feeds the lower-bound capstone directly.
The conventional semantic repair is also checked: initialization cannot inspect the
objective, charged executions equal Tier-2 `pivotCount`, and antipodal objectives share
their start. The execution/geometry wrapper now places the lower bound directly on that
count. The exact one-sample event assembly is also checked: normal tails, RHS tails,
and affine genericity hold together with failure at most `n⁻²` under the same
translated/scaled augmented-row product law. The deterministic Theorem 57 wrapper is
also checked and places the result directly on Tier-2 `pivotCount`; only the final
root-level event-to-data and antipodal/rescaling packaging remains.

### Non-rigorous corroboration

[simulation/](simulation/) — a clearly-separated Monte Carlo layer running the
actual simplex method under Gaussian smoothing on small LPs. Illustrative only;
proves nothing.
