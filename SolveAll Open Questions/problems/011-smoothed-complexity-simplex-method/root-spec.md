# Root Specification — SolveAll #11 (canonical, locked 2026-07-17)

This file locks the exact target. Nothing in the campaign may silently replace
it. Every mismatch between this spec and the repository's Lean model is a
recorded **obligation**, never a license to weaken the target.

## R0 — Canonical statement (verbatim mathematical content)

Fix integers `n ≥ 1` (variables) and `m ≥ n` (constraints). Consider linear
programs

    maximize   cᵀx     subject to   A x ≤ b,        x ∈ ℝⁿ

with `A ∈ ℝ^{m×n}`, `b ∈ ℝ^m`, `c ∈ ℝⁿ`.

A **simplex pivot rule `R`** is a complete deterministic specification of
entering/leaving choices (including tie-breaking and initialization), so that
the pivot count is well defined on nondegenerate instances.

**Gaussian smoothed model.** An adversary chooses a center `(Ā, b̄, c̄)` with
`‖(Ā, b̄, c̄)‖ ≤ 1`; then independent Gaussian noise is added to every scalar
coefficient:

    A = Ā + G,   b = b̄ + h,   c = c̄ + g,

with entries of `G, h, g` i.i.d. `N(0, σ²)`, `σ ∈ (0, 1]`.

Let `T_R(A,b,c)` be the total number of pivots performed by the full simplex
algorithm using rule `R`. Define

    Sm_R(m,n,σ)  :=  sup_{‖(Ā,b̄,c̄)‖ ≤ 1}  E[ T_R(Ā+G, b̄+h, c̄+g) ].

**Unsolved target (existence form):** does there exist a pivot rule `R` with

    Sm_R(m,n,σ)  ≤  O( n · polylog(m, n, 1/σ) )

uniformly for all `m ≥ n` and `σ ∈ (0,1]`? **General form:** determine the
asymptotic order of `inf_R Sm_R(m,n,σ)`.

## R1 — Quantifier skeleton of the existence target

    ∃ (R : PivotRule),
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (n m : ℕ), 1 ≤ n → n ≤ m →
    ∀ (σ : ℝ), 0 < σ → σ ≤ 1 →
      Sm_R m n σ  ≤  C · (n : ℝ) · (Real.log (m * n / σ) + 1) ^ k

(The `+1` guards `log ≤ 0` for small arguments; any faithful polylog encoding
is acceptable so long as it is `n · polylog(m,n,1/σ)`.) The **general form**
replaces the `∃ R` + bound by the exact growth rate of `inf_R Sm_R`.

Order of quantifiers is **essential and must not be permuted**: `R`, `C`, `k`
are chosen *first* (one rule, uniform constants), then the bound holds for *all*
`(n,m,σ)`. A per-instance or per-dimension rule does **not** satisfy R1.

## R2 — Component definitions that must be pinned (each an obligation)

| symbol | meaning | status in repo |
|---|---|---|
| `PivotRule` | deterministic entering+leaving+init+tie-break function; pivot count well-defined on nondegenerate inputs | **not formalized** (obligation T2-R) |
| `T_R(A,b,c)` | number of simplex pivots of `R` on the (nondegenerate, feasible, bounded) LP | **not formalized** (T2-T) |
| feasibility/boundedness | domain where `T_R` is defined; degeneracy is measure-zero under the Gaussian smoothing | **not formalized** (T2-F) |
| `‖(Ā,b̄,c̄)‖ ≤ 1` | norm on the stacked data triple. **Convention obligation:** Spielman–Teng use the ℓ² (Euclidean/Frobenius) norm of the concatenated coefficient vector; confirm against the SolveAll page's intended norm | **not formalized** (T2-N) |
| Gaussian smoothing measure | product `N(0,σ²)` over all `m·n + m + n` coefficients, translated by the center | partially: `gaussianReal` (1-D) verified; product measure not assembled (T2-G) |
| `E[·]` | expectation of `T_R` (a ℕ-valued, hence integrable once a.s. finite) random variable over the smoothing measure | **not formalized** (T2-E) |
| `sup` | supremum over the ℓ²-ball of centers, **outside** the expectation | **not formalized** (T2-S) |
| `O(n·polylog)` | ∃ `C,k` uniform in `(n,m,σ)` | encodable once the above exist |

**Model-fidelity note (critical):** even *stating* R1 in Lean requires T2-R,
T2-T, T2-F, T2-N, T2-G, T2-E, T2-S. None exists in Mathlib or (as far as this
campaign has found) any public Lean corpus. So the root Lean theorem is **not
yet expressible**, independent of whether it is provable. This is the dominant
obstruction and is itself a multi-milestone formalization program.

## R3 — Honest status after the 2026 literature audit

The previous status was stale. Bach–Huiberts, *Optimal Smoothed Analysis of the
Simplex Method* (FOCS 2025; arXiv v2 dated 2026-05-23), prove the improved upper
bound `O(σ^{-1/2} d^{11/4} log^{7/4} m)` and a high-probability lower bound
`Ω(σ^{-1/2} d^{1/2} log(1/σ)^{-1/4})` on smoothed combinatorial diameter when
`m = ⌊(4/σ)^d⌋`. Bach–Black–Kafer–Huiberts (STOC 2026) explicitly summarize the
lower bound as applying to **all pivot rules**.

This creates a specification fork:

- Under standard simplex semantics (Phase I supplies an objective-independent
  feasible start and all 1-skeleton moves are counted), the displayed R1 bound
  with only `polylog(1/σ)` dependence is **false**. Scaling the published `d=2`
  construction by `(2m)^{-1/2}` puts its stacked center in this specification's
  global unit ball and changes the noise to `σ = Θ(τ²)`. The resulting expected
  pivot lower bound is
  `Ω(σ^{-1/4} log(1/σ)^{-1/4})`, which dominates every fixed polylogarithm.
  Centered Gaussian objective noise is handled by pairing `c` and `-c`; see
  `lower-bound-audit.md` and the Lean-checked Tier-3 reduction.
- Under the literal prose, initialization has no computational restriction. An
  initializer may solve the LP by uncharged non-pivot work, choose an optimal
  vertex, and give `T_R=0`. On that reading R1 is vacuously true.

Thus the existence question is **not a well-posed open conjecture as written**.
The exact asymptotic order of `inf_R Sm_R` remains open only after initialization,
allowed operations, and charged work are repaired. No unqualified terminal label
is emitted for the compound page.

## R4 — Root dependency graph (living)

Root: **R1** (specification fork; displayed bound false under standard semantics,
vacuous under unrestricted initialization).

```
R1  (MALFORMED; initialization semantics decide truth value)
├─ T2-MODEL: faithful Lean LP + pivot-rule + T_R + smoothing-measure + Sm_R
│   ├─ T2-G  product Gaussian smoothing measure on ℝ^(mn+m+n)      [OPEN]
│   ├─ T2-R  PivotRule as deterministic function                   [OPEN]
│   ├─ T2-T  pivot-count T_R well-defined a.s.                     [OPEN]
│   └─ T2-{F,N,E,S} feasibility / norm / expectation / sup         [OPEN]
├─ A-COND: condition-number / σ_min architecture
│   ├─ M1   scalar Gaussian small-ball            [kernel_verified ✓]
│   ├─ M1a  finite-family union bound (no indep.) [kernel_verified ✓]
│   ├─ M2.0 distance to a FIXED hyperplane        [kernel_verified ✓ ep 851ff2ce]
│   ├─ M2.1 codim-2 coordinate product bound      [kernel_verified ✓ ep 10653478]
│   ├─ M2.2 arbitrary-orientation codim-k subspace[kernel_verified ✓ ep ea3c53fe]
│   │     (independence of projections PROVED from σ²I + orthonormality; MASTER,
│   │      subsumes M2.0/M2.1; the distance-to-FIXED-subspace estimate σ_min needs)
│   ├─ M2-GEOM  RV per-vector core |x i|·dist ≤ ‖∑ x_j a_j‖   [kernel_verified ✓ ep d99aa6a8]
│   ├─ M2-GEOMσ RV σ_min form (min_i dist)·‖x‖ ≤ √n·‖∑‖        [kernel_verified ✓ ep 56a975eb]
│   ├─ M2-DEF   σ_min := ⨅_{‖x‖=1}‖∑ x_j a_j‖; σ_min ≥ n^{-1/2}·min_i dist
│   │                                                          [kernel_verified ✓ ep 9bdee270]
│   ├─ M2-CONDc P(dist(x,W)≤ε) ≤ 2ε/(σ√2π), FIXED subspace via infDist
│   │                                                          [kernel_verified ✓ ep b15cd230]
│   ├─ M2   σ_min lower-TAIL of a Gaussian matrix              [ACTIVE — single edge left]
│   │     remaining: matrix-Gaussian-as-product measure (Fubini) + MEASURABLE unit-normal
│   │     of the random span Hᵢ (integrate M2-CONDc over other columns) → M2-UNION.
│   │     Deterministic spine (M2-DEF/GEOM) + conditional inequality (M2-CONDc) DONE.
│   └─ M2→shadow bridge: σ_min ⇒ pivot-count bound                [OPEN, the crux]
├─ A-SHADOW: shadow-vertex / projected-polytope edge count
│   └─ best current upper bound (Bach–Huiberts 2025/2026)         [LITERATURE]
└─ A-LOWER: smoothed diameter → pivot lower bound
    ├─ Bach–Huiberts Theorem 57                                  [LITERATURE]
    ├─ Lemma 54 sphere net                                      [lean_checked ✓]
    ├─ Lemma 55 + abstract basis-path Lemma 56                   [lean_checked ✓]
    ├─ polar incidence/minimum point/reciprocal balls            [lean_checked ✓]
    ├─ finite-row exact-law Gaussian tail                        [lean_checked ✓]
    ├─ normalization + extreme-point full active basis           [lean_checked ✓]
    ├─ affine-GP consequences + AC product induction             [lean_checked ✓]
    ├─ antipodal-objective expectation bridge                    [lean_checked ✓]
    └─ rescaling algebra + polylog separation                    [lean_checked ✓]
```

Rule-of-progress: after ≤2 low-risk helpers, return to a high-leverage edge.
For the corrected root this is now algorithmic
edge-walk wiring / repaired initialization, not a new near-linear upper bound.

## R5 — Architecture ledgers (end-to-end routes to R1)

**A-COND (condition-number → pivot bound).** Chain: scalar small-ball (M1 ✓) →
distance-to-subspace (M2.0) → σ_min lower tail over relevant bases (M2) → bound
improving-adjacent-bases / shadow size by 1/σ_min powers → E[T_R] bound. First
open edge: **M2** and, decisively, the **σ_min ⇒ pivot-count** implication
(A result about one fixed basis must not be promoted to all adaptively visited
bases — a union bound over exponentially many bases is the classic trap). Param
loss: naive union over `C(m,n)` bases is fatal; the real proofs avoid it via the
shadow geometry. Fidelity: does not by itself fix a specific pivot rule.

**A-SHADOW (shadow-vertex).** Chain: bound E[#edges of the projection of the
feasible polytope onto a random/`c`-aligned 2-plane] → this equals the pivot
count of the shadow-vertex rule → sum over phases. First open edge: the expected
shadow-size bound (this is exactly the Spielman–Teng/Dadush–Huiberts/HLZ
theorem; the near-linear-in-`n` version is open). Fidelity: pins `R` =
shadow-vertex, satisfying R1's `∃R`. This is the only architecture that has ever
produced a *polynomial* smoothed bound, so it is the primary route.

**A-LOWER (disproof / specification-audit route).** The required literature
input now exists: Bach–Huiberts Theorem 57 gives a diameter lower bound and the
STOC 2026 summary states that it applies to all pivot rules. The repository adds
a Lean-checked import of its sphere-net, deterministic roundness/facet/basis-path,
  polar-incidence/minimum-point, Gaussian-tail, normalization, extreme-point
  active-basis, and genericity-induction components, an
antipodal-objective/expectation bridge, and an explicit rescaling from rowwise
normalization to the global stacked norm. This disproves the displayed
polylogarithmic-noise target for the conventional objective-independent Phase I
  model. The exact one-sample probability-event assembly is now Lean-checked.
  The deterministic Theorem 57 `pivotCount` wrapper is also Lean-checked. Remaining are
  the final event-to-data/antipodal packaging and
the root-level semantic obligation: pin a non-oracular notion of initialization.
Without it the zero-pivot initializer defeats any lower bound.

**Best falsification test right now:** formalize the repaired pivot-rule semantics
and the global-norm rescaling. Do not spend the next cycle seeking a near-linear
upper bound for a target already contradicted by the current lower-bound frontier.

## R6 — What this campaign can rigorously deliver (and cannot)

- **Can:** kernel-verified machinery beneath A-COND; a partial T2-MODEL; the
  antipodal-objective lower-bound bridge; and a precise diagnosis of the root's
  initialization ambiguity.
- **Cannot yet:** kernel-verify the full Bach–Huiberts geometric theorem or state
  the literal root in Lean before the pivot-rule and initialization semantics are
  repaired.

The terminal line remains qualified rather than absolute:

`RESOLUTION (standard objective-independent Phase I): DISPROVED`.

`RESOLUTION (literal unrestricted initialization): VACUOUS / ILL-POSED`.

The general exact-order question remains open for a repaired model.
