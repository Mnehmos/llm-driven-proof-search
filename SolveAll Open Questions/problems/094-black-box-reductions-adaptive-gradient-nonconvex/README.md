# Black-Box Reductions and Adaptive Gradient Methods for Nonconvex Optimization

**Status:** Unsolved  
**Source:** Posed by Xinyi Chen et al. (2024)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #94 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $d,T\in\mathbb{N}$ and let $K\subseteq\mathbb{R}^d$ be a nonempty convex set. In online convex optimization (OCO), an algorithm $A$ produces decisions $x_t\in K$ over rounds $t=1,\dots,T$ . An adversary then reveals a convex loss function $\ell_t:K\to\mathbb{R}$ , and $A$ incurs loss $\ell_t(x_t)$ . The (static) regret is

$
\mathrm{Regret}_T(A;\ell_{1:T})=\sum_{t=1}^T \ell_t(x_t)-\min_{x\in K}\sum_{t=1}^T \ell_t(x).
$

Assume $A$ admits a worst-case bound $\mathrm{Regret}_T(A;\ell_{1:T})\le \mathrm{Regret}_T(A)$ for all convex sequences $\ell_{1:T}$ .

In offline stochastic nonconvex optimization, let $f:\mathbb{R}^d\to\mathbb{R}$ be differentiable and $\beta$ -smooth, i.e., $\|\nabla f(x)-\nabla f(y)\|_2\le \beta\|x-y\|_2$ for all $x,y\in\mathbb{R}^d$ . Fix a start point $x_1$ such that for some global minimizer $x^*$ we have $f(x_1)-f(x^*)\le M$ . Access to $f$ is via a stochastic gradient oracle: on input $x$ , it returns a random vector $\widetilde{\nabla}f(x)$ with $\mathbb{E}[\widetilde{\nabla}f(x)]=\nabla f(x)$ and $\mathbb{E}[\|\widetilde{\nabla}f(x)-\nabla f(x)\|_2^2]\le \sigma^2$ .

### Unsolved Problem

Design a black-box reduction that, given (i) oracle access to $f$ as above and (ii) black-box access to any OCO algorithm $A$ only through its interface on convex losses $\ell_t$ constructed by the reduction, outputs iterates $x_1,\dots,x_T\in\mathbb{R}^d$ such that

$
\frac{1}{T}\sum_{t=1}^T \mathbb{E}[\|\nabla f(x_t)\|_2^2]\le O\!\left(\frac{\sqrt{M\beta\,\mathrm{Regret}_T(A)}}{T}\right).
$

The expectation is over the oracle randomness (and any internal randomness of the reduction/algorithm). Equivalently (by averaging), such a guarantee implies existence of an iterate $t\in\{1,\dots,T\}$ with $\mathbb{E}[\|\nabla f(x_t)\|_2^2]$ bounded by the same right-hand side up to constants.

## Significance & Implications

A reduction of the above form would make convergence guarantees for smooth nonconvex stochastic objectives modular: any OCO method with a provable regret bound (including adaptive, geometry-aware bounds such as coordinate-wise or $\ell_\infty$ -diameter dependence) could be plugged in as a black box to yield a corresponding bound on stationarity $\mathbb{E}[\|\nabla f(x_t)\|_2^2]$ . This would directly connect regret analyses of adaptive gradient methods to the $\Theta(1/\sqrt{T})$ -type iteration rates typically targeted in stochastic nonconvex optimization, potentially isolating when and how adaptive preconditioning can improve dimension/geometry dependence relative to non-adaptive baselines under the same smoothness and unbiased-noise assumptions.

## Known Partial Results

- Existing reduction templates discussed in the COLT 2024 open-problem note are often episodic/epoch-based (e.g., by adding quadratic regularization to induce strong convexity within epochs), which leads to guarantees that depend on regret aggregated over epochs or on regret notions beyond a single global static regret term.

- The note describes black-box-style guarantees that can be proved when the online learner is evaluated with stronger regret measures (e.g., adaptive-regret-type notions) rather than standard static regret.

- The note also presents a non-episodic bound in terms of dynamic regret for suitable strongly convex regularized losses $\widetilde f_t$ : informally,

$
\frac{1}{T}\sum_{t=1}^T\mathbb{E}[\|\nabla f(x_t)\|_2^2]\le \frac{6\beta}{T}\left(M+\mathbb{E}[\mathrm{DynamicRegret}_A(\widetilde f_{2:T+1},x^*_{2:T+1})]\right),
$

highlighting that dynamic-regret control is sufficient but not the desired static-regret-only form.

- The note argues that if the conjectured static-regret reduction held, plugging in AdaGrad-type regret bounds would preserve the $1/\sqrt{T}$ dependence in $T$ while potentially improving dimension/geometry dependence when gradients are sparse or coordinates have different scales.

- Under an additional stationary-distribution heuristic for the constructed linearized losses, the note explains that using a lazy-OGD (lazy FTRL) regret bound recovers a standard SGD-like dependence of order $O\!\left(\sigma\sqrt{\frac{M\beta}{T}}\right)$ in that special case.

- The note points out that there are also direct (non-reduction) analyses of adaptive methods in nonconvex settings, but these do not yield a general black-box implication from an arbitrary OCO static-regret bound to a nonconvex stationarity guarantee of the conjectured form.

## References

[1]

 [Open Problem: Black-Box Reductions and Adaptive Gradient Methods for Nonconvex Optimization](https://proceedings.mlr.press/v247/chen24e.html) 

Xinyi Chen, Elad Hazan (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/chen24e.html) [2]

 [Open Problem: Black-Box Reductions and Adaptive Gradient Methods for Nonconvex Optimization (PDF)](https://proceedings.mlr.press/v247/chen24e/chen24e.pdf) 

Xinyi Chen, Elad Hazan (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/chen24e/chen24e.pdf) [3]

 [Adaptive subgradient methods for online learning and stochastic optimization](https://jmlr.org/papers/v12/duchi11a.html) 

John Duchi, Elad Hazan, Yoram Singer (2011)

Journal of Machine Learning Research

📍 JMLR official paper page

 [Link ↗](https://jmlr.org/papers/v12/duchi11a.html)

## Notes / Progress

_Work log goes here._
