# Polynomial linearly-convergent method for g-convex optimization?

**Status:** Unsolved  
**Source:** Posed by Christopher Criscitiello et al. (2023)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #101 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(\mathcal{M},g)$ be a $d$ -dimensional Riemannian manifold with geodesic distance $\operatorname{dist}(\cdot,\cdot)$ . A function $f:\mathcal{M}\to\mathbb{R}$ is $L$ -Lipschitz if $|f(x)-f(y)|\le L\,\operatorname{dist}(x,y)$ for all $x,y\in\mathcal{M}$ , and geodesically convex (g-convex) if for every constant-speed geodesic $\gamma:[0,1]\to\mathcal{M}$ , the map $t\mapsto f(\gamma(t))$ is convex on $[0,1]$ .

Assume $f^\star:=\inf_{y\in\mathcal{M}} f(y)$ is finite. Consider a deterministic first-order oracle model in which, given a query point $x\in\mathcal{M}$ , the oracle returns a Riemannian subgradient $s\in T_x\mathcal{M}$ satisfying

$
f(\exp_x(v))\ge f(x)+\langle s, v\rangle \quad\text{for all tangent vectors $v$ for which $\exp_x(v)$ is defined,}
$

where $\exp_x:T_x\mathcal{M}\to\mathcal{M}$ is the exponential map and $\langle\cdot,\cdot\rangle$ is the inner product induced by $g$ on $T_x\mathcal{M}$ .

### Unsolved Problem

Does there exist a deterministic first-order algorithm that, for every dimension $d$ , every $d$ -dimensional Riemannian manifold $\mathcal{M}$ , every Lipschitz g-convex $f:\mathcal{M}\to\mathbb{R}$ , and every accuracy $\epsilon\in(0,1)$ , outputs a point $x\in\mathcal{M}$ such that

$
f(x)-f^\star\le \epsilon,
$

using at most $O(\mathrm{poly}(d)\,\log(\epsilon^{-1}))$ oracle queries, and with at most $O(\mathrm{poly}(d))$ arithmetic operations performed per oracle query (i.e., per-query work polynomial in $d$ and not growing with $\epsilon^{-1}$ beyond constants)?

## Significance & Implications

In Euclidean convex optimization, the ellipsoid method gives a deterministic, worst-case polynomial-time framework whose oracle complexity is logarithmic in $\epsilon^{-1}$ for achieving $\epsilon$ -suboptimality. An affirmative answer here would show that g-convexity on arbitrary Riemannian manifolds admits an analogous uniform, dimension-polynomial first-order method with $\log(\epsilon^{-1})$ query dependence; a negative answer would indicate that manifold geometry (beyond g-convexity and Lipschitz continuity) creates a genuine barrier to extending Euclidean-style polynomial-time guarantees.

## Known Partial Results

- In the Euclidean special case $\mathcal{M}=\mathbb{R}^d$ , the classical ellipsoid method achieves $O(\mathrm{poly}(d)\log(\epsilon^{-1}))$ first-order (separation/subgradient) oracle complexity for convex optimization.

- Criscitiello, Martinez-Rubio, and Boumal (COLT 2023) give an ellipsoid-like algorithm for certain constant-curvature manifolds (hemisphere or hyperbolic space) with subgradient query complexity $O(d^2\log^2(\epsilon^{-1}))$ .

- In that constant-curvature setting, their method has per-query computational cost $O(d^2)$ arithmetic operations.

- For general Riemannian manifolds, the existence of a deterministic first-order method with $O(\mathrm{poly}(d)\log(\epsilon^{-1}))$ queries and $O(\mathrm{poly}(d))$ per-query work remains open; the COLT 2023 paper discusses candidate approaches and obstacles but does not establish such a general algorithm.

## References

[1]

 [Open Problem: Polynomial linearly-convergent method for g-convex optimization?](https://proceedings.mlr.press/v195/criscitiello23b.html) 

Christopher Criscitiello, David MartÃ­nez-Rubio, Nicolas Boumal (2023)

Conference on Learning Theory (COLT), PMLR 195

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v195/criscitiello23b.html) [2]

 [Open Problem: Polynomial linearly-convergent method for g-convex optimization? (PDF)](https://proceedings.mlr.press/v195/criscitiello23b/criscitiello23b.pdf) 

Christopher Criscitiello, David MartÃ­nez-Rubio, Nicolas Boumal (2023)

Conference on Learning Theory (COLT), PMLR 195

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v195/criscitiello23b/criscitiello23b.pdf)

## Notes / Progress

_Work log goes here._
