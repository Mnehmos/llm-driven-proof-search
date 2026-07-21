# Optimal adaptation beyond compact manifolds

**Status:** Unsolved  
**Source:** Sourced from the work of Tao Tang, Nan Wu, Xiuyuan Cheng, David Dunson

## Categories

- Mathematical Statistics
- Learning Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #65 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $D\ge 1$ and let $S\subset \mathbb R^D$ be a compact predictor domain. Assume the predictors $X_1,\dots,X_n$ are i.i.d. from a probability measure $P_X$ supported on $S$ , and responses satisfy

$
Y_i=f_0(X_i)+\varepsilon_i,\qquad \varepsilon_i\stackrel{\text{i.i.d.}}{\sim}N(0,\sigma^2),\ \sigma^2\in(0,\infty).
$

Place a squared-exponential GP prior restricted to $S$ ,

$
f\mid A\sim \mathrm{GP}\!\left(0,\ K_A(x,x')\right),\qquad K_A(x,x')=\exp\!\big(-A^2\|x-x'\|^2\big),
$

with a data-driven or hierarchical prior on bandwidth $A$ that does not use the unknown pair $(d,\beta)$ .

What is proved in the cited work is the compact-manifold case: for intrinsically $\beta$ -smooth targets on compact smooth manifolds, RKHS approximation bounds are established and adaptive posterior contraction rates are derived at the minimax exponent, up to logarithmic factors.

### Unsolved Problem

Obtain analogous RKHS approximation conditions on genuinely non-manifold supports. Assume only low-dimensional metric complexity, e.g. for some $d\in(0,D]$ and $c_1,c_2,\delta_0>0$ ,

$
c_1\,\delta^{-d}\le N(S,\delta)\le c_2\,\delta^{-d}\quad\text{for all }0<\delta<\delta_0,
$

where $N(S,\delta)$ is the covering number. For $f_0\in\mathcal F_\beta(S)$ (an intrinsic $\beta$ -smooth class on $S$ ), identify geometric assumptions beyond manifold structure under which one can prove, for large $A$ , existence of $h_A\in\mathbb H_A$ with

$
\|h_A-f_0\|_{L^2(P_X)}\lesssim A^{-\beta},
\qquad
\|h_A\|_{\mathbb H_A}^2\lesssim A^{d},
$

allowing at most controlled logarithmic losses when necessary, and thereby obtain adaptive contraction

$
\varepsilon_n\asymp n^{-\beta/(2\beta+d)}
$

up to log factors with $A$ -prior independent of $(d,\beta)$ .

The general non-manifold characterization (necessary/sufficient geometric conditions for such RKHS bounds and rates) remains open.

## Significance & Implications

The abstract of [Tang et al. (2024)](#references) indicates optimality is obtained on compact manifolds using a novel RKHS approximation analysis, suggesting geometry is crucial for sharp rates. Extending optimal guarantees to broader intrinsic structures would substantially widen the theory's applicability to realistic data supports.

## Known Partial Results

The paper proves RKHS approximation to intrinsically defined H"older functions on compact manifolds of any smoothness order and derives adaptive contraction rates there at the optimal exponent, up to logarithmic factors. For more general low-dimensional non-manifold structures, comparable RKHS approximation conditions are not yet established.

## References

[1]

 [Adaptive Bayesian regression on data with low intrinsic dimensionality](https://arxiv.org/abs/2407.09286v3) 

Tao Tang, Nan Wu, Xiuyuan Cheng, David Dunson (2024)

arXiv preprint; Annals of Statistics (to appear)

📍 arXiv v3 (2024), Section 6 (Discussion), first paragraph beginning "It would be interesting to develop RKHS approximation analysis on a more general low-dimensional domain X..." (p. 14).

Primary source for this problem. Author order follows the cited arXiv/Annals listing; year is the arXiv v3 year (2024), while final journal publication details are pending.

 [Link ↗](https://arxiv.org/abs/2407.09286v3) [arXiv ↗](https://arxiv.org/abs/2407.09286v3)

## Notes / Progress

_Work log goes here._
