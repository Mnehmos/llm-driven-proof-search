# Formalization Walls — Erdős 888

## Wall 1: Landau's Semiprime Asymptotic
**Estimated difficulty**: High
**Status**: Absent from Mathlib
**Description**: The asymptotic number of integers ≤ x with exactly two prime factors (Ω(n)=2, counted with multiplicity or without) is x·log log x / log x. This is needed for the lower bound count.
**Mitigation**: Prove an unconditional lower bound via Chebyshev estimates if full Landau is too heavy for budget.

## Wall 2: Colored KST Supersaturation
**Estimated difficulty**: High
**Status**: Absent from Mathlib
**Description**: For T bipartite graphs on classes of sizes M ≤ N, if no C4 is complete in two colors, the total edge count is bounded by O(T(N + M√N) + T^{3/4}·MN). This is the graph-theoretic heart of the upper bound.
**Mitigation**: This is our largest reusable contribution. Build generic infra in a `FiniteGraph` or `BipartiteGraph` namespace.

## Wall 3: Smooth Number / ψ(x,y) Estimates
**Estimated difficulty**: Medium-High
**Status**: Likely absent
**Description**: Rankin's trick for smooth squarefree cores (Lemma 7.2) requires bounds on the count of integers all of whose prime factors are ≤ some threshold.
**Mitigation**: Elementary Rankin's trick with Chebyshev product bounds may suffice.

## Wall 4: Dyadic Summation Infrastructure
**Estimated difficulty**: Medium
**Status**: Absent in this specific form
**Description**: Multiple dyadic sums (geometric, product-log) need formalization.
**Mitigation**: Straightforward but tedious. Decompose into small named lemmas.

## Wall 5: Mertens Product Estimates
**Estimated difficulty**: Low-Medium
**Status**: Partially available from erdos-647
**Description**: ∏_{p≤x} (1+1/p) ≪ log x needed for core sums.
**Mitigation**: Inspect erdos-647 Mertens artifacts for reusability.

## Wall 6: Largest Prime Factor Decomposition
**Estimated difficulty**: Low
**Status**: Need to build, but well-supported by factorization API
**Description**: a = c·p·q with p,q largest primes, c squarefree with primes < p.
**Mitigation**: Build as a dedicated module with VAR nomination.

## Recommended Order of Attack

1. **Phase 1** (Foundations): Low difficulty, high leverage — definitions drive everything downstream.
2. **Phase 2** (Lower bound rigidity): Low-medium difficulty — existing Ulam draft gives template.
3. **Phase 5** (Colored rectangle): Medium difficulty — graph encoding, finite combinatorial reasoning.
4. **Phase 3** (Squarefree reduction): Low-medium difficulty — clean partition argument.
5. **Phase 6** (Colored KST): High difficulty, but most reusable — start early and iterate.
6. **Phase 4** (Largest prime encoding): Low difficulty — factorization API ready.
7. **Phases 7-9** (Analytic): Variable — tackle after finite-combinatorial core is done.
8. **Phase 10** (Assembly): Integrates all pieces.
