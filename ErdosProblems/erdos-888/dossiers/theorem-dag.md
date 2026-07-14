# Proof Search Theorem DAG — Erdős 888

## Phase 0: Source and Environment
- [ ] A0 — Freeze source versions and citations
- [ ] A1 — Inspect Ulam Lean draft (`erdos888.lean`)
- [ ] A2 — Mathlib inventory (squarefree, factorization, asymptotics, graphs)
- [ ] A3 — Write `mathlib-gap-map.md`

## Phase 1: Foundational Definitions
- [ ] B1 — `SquareProductRigid` (admissible set definition)
- [ ] B2 — `F(n)` = maximum cardinality
- [ ] B3 — `G(n)` = maximum cardinality for squarefree sets
- [ ] B4 — `A_k = {s | k²s ∈ A}` fixed-square-part fiber
- [ ] B5 — `IsSemiprime`, `IsSquarefreeSemiprime`
- [ ] B6 — Largest/second-largest prime factor for squarefree integers ≥ 2 primes
- [ ] B7 — Basic monotonicity, finiteness, positivity lemmas

## Phase 2: Lower Bound — Rigidity of Primes + Semiprimes
- [ ] C1 — `B(n)` = primes ∪ squarefree semiprimes ≤ n
- [ ] C2 — Every element of B(n) is squarefree with ≤ 2 prime factors
- [ ] C3 — Case analysis: 4 primes → ad = bc
- [ ] C4 — Case analysis: 2 primes + 2 semiprimes → ad = bc
- [ ] C5 — Case analysis: 4 semiprimes → ad = bc
- [ ] C6 — `B(n)` is admissible (composite: `lowerBoundSet_rigid`)

## Phase 3: Squarefree Reduction
- [ ] D1 — Every n = k²·s uniquely with s squarefree
- [ ] D2 — Each fixed-k fiber A_k is admissible
- [ ] D3 — F(n) ≤ Σ_{k ≤ √n} G(⌊n/k²⌋)
- [ ] D4 — If G(m) ≪ m·log log m / log m then F(n) ≪ n·log log n / log n
- [ ] D5 — Split k at n^{1/3} for tail bound

## Phase 4: Two-Largest-Prime Encoding
- [ ] E1 — For squarefree a with ≥ 2 primes: a = c·p·q, p < q = largest primes
- [ ] E2 — c is squarefree, primes(c) < p, p ∤ c, q ∤ c
- [ ] E3 — Reusable factorization module + VAR candidate

## Phase 5: Colored Rectangle Obstruction
- [ ] F1 — Dyadic prime blocks (X,2X] × (Y,2Y]
- [ ] F2 — For core c, graph H_c: p–q iff cpq ∈ A
- [ ] F3 — No 2×2 rectangle complete in 2 distinct colors (Lemma 5.1)
- [ ] F4 — Sorting: if no pairing has equal product, extremes also fail

## Phase 6: Colored KST Supersaturation
- [ ] G1 — Single bipartite graph C4 bound: e ≪ N + M√N + √(MN)·R^{1/4}
- [ ] G2 — Colored family: Σ e(H_γ) ≪ T(N + M√N) + T^{3/4}·MN
- [ ] G3 — Required: degree sums, 2-paths, common neighbors, rectangle counting
- [ ] G4 — Discrete convexity / binomial coefficient bounds
- [ ] G5 — Finite Hölder

## Phase 7: Dyadic Summation
- [ ] H1 — λ(x) = log(e·x) or equivalent
- [ ] H2 — Geometric dyadic sum of Y^θ / λ(Y)
- [ ] H3 — min(X, B/Z)·√Z estimate
- [ ] H4 — Reciprocal product-log dyadic sum → log L / L

## Phase 8: Number Theoretic Estimates
- [ ] I1 — π(x) ≪ x / log x
- [ ] I2 — ∏_{p≤x} (1 + 1/p) ≪ log x
- [ ] I3 — ∏_{p≤x} p ≤ exp(C·x)
- [ ] I4 — Σ_{p≤x} p^{-α} ≪ x^{1-α} / λ(x) for 0<α<1
- [ ] I5 — Landau's semiprime asymptotic
- [ ] I6 — Remove O(√n) prime-square contribution

## Phase 9: Dyadic Block Sums
- [ ] J1 — S1 (rectangle term) ≪ n log log n / log n
- [ ] J2 — S2 (T·N term) ≪ n / log n
- [ ] J3 — S3 (T·M√N term) ≪ n / log n
- [ ] J4 — Lemma 7.1: one-dimensional dyadic core bound
- [ ] J5 — Lemma 7.2: squarefree-core sum
- [ ] J6 — Decomposition c = r·d with r = largest prime factor
- [ ] J7 — Small-r / large-r split
- [ ] J8 — Rankin's trick for smooth squarefree cores
- [ ] J9 — Large-X / small-X split for T₀(X)

## Phase 10: Final Assembly
- [ ] K1 — Squarefree upper bound G(n) ≪ n log log n / log n
- [ ] K2 — Unrestricted upper bound via squarefree reduction
- [ ] K3 — Lower bound via semiprime construction
- [ ] K4 — Final Θ theorem
- [ ] K5 — Replay all dependencies
- [ ] K6 — Build from clean environment
- [ ] K7 — Verify no sorries/admit/untracked axioms
- [ ] K8 — Export portable proof source
- [ ] K9 — Compare with Formal Conjectures statement
