# Tight Convergence of SGD in Constant Dimension

**Status:** Unsolved  
**Source:** Posed by Tomer Koren et al. (2020)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #111 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix a dimension $d\ge 1$ that is a constant independent of the iteration budget $T$ . Let $\mathcal K\subseteq\mathbb R^d$ be a nonempty closed convex set with finite Euclidean diameter $D:=\sup\{\|x-y\|_2:x,y\in\mathcal K\}<\infty$ . Let $f:\mathcal K\to\mathbb R$ be convex and attain its minimum on $\mathcal K$ , and fix some minimizer $x^*\in\arg\min_{x\in\mathcal K} f(x)$ . Assume access to a stochastic first-order oracle such that, for each query point $x\in\mathcal K$ , it returns a random vector $g(x)$ satisfying (i) unbiasedness: $\mathbb E[g(x)]\in\partial f(x)$ , and (ii) bounded second moment: $\mathbb E[\|g(x)\|_2^2]\le G^2$ for a known constant $G<\infty$ .

Projected stochastic gradient descent (SGD) starts from some $x_1\in\mathcal K$ and iterates

$
x_{t+1}=\Pi_{\mathcal K}\bigl(x_t-\eta_t g(x_t)\bigr),\qquad t=1,2,\dots,T-1,
$

where $\Pi_{\mathcal K}$ is Euclidean projection and $(\eta_t)_{t\ge 1}$ is a stepsize schedule that may depend on $T,d,D,G$ but not on additional unknown properties of $(f,\text{oracle})$ beyond the model above. The performance measure is the expected last-iterate suboptimality $\mathbb E[f(x_T)-f(x^*)]$ , where the expectation is over the oracle randomness.

### Unsolved Problem

Characterize the minimax-optimal dependence on $T$ of the worst-case expected last-iterate suboptimality achievable by projected SGD over the above problem class when $d$ is fixed. In particular, determine whether there exist constants $c_1,c_2>0$ (depending only on $d,D,G$ ) and a stepsize schedule such that for all $T$ ,

$
c_1\,T^{-1/2}\ \le\ \sup_{(f,\text{oracle})}\mathbb E[f(x_T)-f(x^*)]\ \le\ c_2\,T^{-1/2},
$

and whether this $\Theta(1/\sqrt T)$ characterization already holds in the one-dimensional case $d=1$ .

## Significance & Implications

SGD is typically deployed without iterate averaging, so last-iterate guarantees govern the algorithm's actual output. A tight minimax characterization in fixed (especially one) dimension would resolve a basic mismatch between existing upper and lower bounds for $\mathbb E[f(x_T)-f(x^*)]$ in the standard stochastic subgradient oracle model, clarifying whether last-iterate SGD fundamentally matches the canonical $1/\sqrt T$ stochastic-optimization rate in low dimensions or is intrinsically slower.

## Known Partial Results

- Koren and Segal (COLT 2020 open problem) highlight that, when the dimension $d$ is a constant independent of $T$ , known upper and lower bounds for the expected last-iterate suboptimality of projected SGD do not match.

- They emphasize that this gap persists even for $d=1$ .

- They provide evidence in the one-dimensional case consistent with a $\Theta(1/\sqrt T)$ last-iterate rate.

- They conjecture that the same $\Theta(1/\sqrt T)$ last-iterate rate should hold for any constant dimension $d$ .

## References

[1]

 [Open Problem: Tight Convergence of SGD in Constant Dimension](https://proceedings.mlr.press/v125/koren20a.html) 

Tomer Koren, Shahar Segal (2020)

Conference on Learning Theory (COLT), PMLR 125

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v125/koren20a.html) [2]

 [Open Problem: Tight Convergence of SGD in Constant Dimension (PDF)](http://proceedings.mlr.press/v125/koren20a/koren20a.pdf) 

Tomer Koren, Shahar Segal (2020)

Conference on Learning Theory (COLT), PMLR 125

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v125/koren20a/koren20a.pdf)

## Notes / Progress

_Work log goes here._
