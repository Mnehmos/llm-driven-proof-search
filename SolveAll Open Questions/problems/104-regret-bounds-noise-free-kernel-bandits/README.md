# Regret Bounds for Noise-Free Kernel-Based Bandits

**Status:** Partially Resolved  
**Source:** Posed by Sattar Vakili (2022)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #104 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal{X}=[0,1]^d\subset\mathbb{R}^d$ , let $k:\mathcal{X}\times\mathcal{X}\to\mathbb{R}$ be a known positive definite kernel with RKHS $(\mathcal{H}_k,\|\cdot\|_{\mathcal{H}_k})$ , and fix a known radius $C_k>0$ . An unknown deterministic function $f\in\mathcal{H}_k$ satisfies $\|f\|_{\mathcal{H}_k}\le C_k$ . At each round $t=1,2,\dots,N$ , an algorithm (possibly randomized) chooses $x_t\in\mathcal{X}$ measurably as a function of the past and then observes the exact value $y_t=f(x_t)$ (noise-free feedback). Let $x^*\in\arg\max_{x\in\mathcal{X}} f(x)$ and define cumulative regret

$
R_N(A,f)=\sum_{t=1}^N\bigl(f(x^*)-f(x_t)\bigr).
$

Write $\tilde O(\cdot)$ for rates that hide factors polylogarithmic in $N$ .

### Unsolved Problem

 **Problem 2022.** Determine the minimax optimal growth rate

$
\inf_A\sup_{\|f\|_{\mathcal{H}_k}\le C_k} R_N(A,f)
$

as a function of $N$ in the noise-free kernel-based bandit setting, and to give matching algorithmic upper bounds and information-theoretic lower bounds. In particular, when $k$ is a (stationary, isotropic) Matern kernel on $[0,1]^d$ with smoothness parameter $\nu>0$ , determine the smallest exponent $\alpha=\alpha(d,\nu)$ such that some algorithm achieves $\sup_{\|f\|_{\mathcal{H}_k}\le C_k}R_N(A,f)=\tilde O(N^{\alpha})$ , and prove a matching lower bound (up to polylog factors).

More specifically, prove or refute the COLT 2022 conjecture that (up to polylogarithmic factors)

$
\sup_{\|f\|_{\mathcal{H}_k}\le C_k}R_N(A,f)=
\begin{cases}
O\bigl(N^{(d-\nu)/d}\bigr) & \text{if } d>\nu,\\
O(\log N) & \text{if } d=\nu,\\
O(1) & \text{if } d<\nu.
\end{cases}
$

## Significance & Implications

In the noisy RKHS/GP bandit model, regret rates are now characterized (up to log factors) via information-gain-type complexity terms, but Vakili (COLT 2022) highlights that transferring those analyses to exact (noise-free) observations leaves a substantial, kernel-dependent gap and may even fail to guarantee sublinear regret for some kernels. Pinning down the minimax noise-free rate for Matern kernels would (i) identify the true exploration cost when observations are exact, (ii) clarify whether cumulative regret can be bounded by $O(\log N)$ or $O(1)$ once smoothness $\nu$ meets or exceeds dimension $d$ , and (iii) provide a target rate that future deterministic Bayesian-optimization-style algorithms and lower-bound proofs must match.

## Known Partial Results

- Vakili (COLT 2022) formulates the noise-free kernel bandit problem with $f\in\mathcal{H}_k$ , $\|f\|_{\mathcal{H}_k}\le C_k$ , exact observations $y_t=f(x_t)$ , and cumulative regret $R_N=\sum_{t=1}^N(f(x^*)-f(x_t))$ .

- The note contrasts this with the noisy setting, where regret bounds for GP-style methods are often expressed in terms of a maximal information gain quantity (e.g., $\Gamma_{k,\lambda}(N)=\sup_{\{x_i\}_{i=1}^N}\tfrac12\log\det(I+\lambda^{-2}K)$ ), yielding rates of the form $\tilde O(\Gamma_{k,\lambda}(N)\sqrt{N})$ or $\tilde O(\sqrt{\Gamma_{k,\lambda}(N)\,N})$ depending on the analysis.

- The note reports that such noisy-style bounds can be loose in the noise-free regime: for Matern kernels they lead to a regret exponent of the form $\tilde O\bigl(N^{(\nu+d)/(2\nu+d)}\bigr)$ , which the note argues is not order-optimal when observations are exact.

- The note discusses multiple noise-free upper bounds obtained via different strategies (including an explore-then-commit style approach) and emphasizes that, while these bounds can be sublinear, none are proved to match a minimax lower bound for the noise-free problem.

- The note states a conjectured piecewise-optimal rate for Matern kernels, $R_N=\tilde O\bigl(N^{(d-\nu)/d}\bigr)$ for $d>\nu$ , $\tilde O(\log N)$ for $d=\nu$ , and $\tilde O(1)$ for $d<\nu$ , motivated heuristically by controlling sums of GP posterior standard deviations under near-uniform sampling.

- Subsequent 2025 work gives nearly optimal noise-free GP-UCB guarantees in important regimes, but a full minimax characterization across kernels and the boundary case $d=\nu$ remains open.

## References

[1]

 [Open Problem: Regret Bounds for Noise-Free Kernel-Based Bandits](https://proceedings.mlr.press/v178/open-problem-vakili22a.html) 

Sattar Vakili (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-vakili22a.html) [2]

 [Open Problem: Regret Bounds for Noise-Free Kernel-Based Bandits (PDF)](https://proceedings.mlr.press/v178/open-problem-vakili22a/open-problem-vakili22a.pdf) 

Sattar Vakili (2022)

Conference on Learning Theory (COLT), PMLR 178

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v178/open-problem-vakili22a/open-problem-vakili22a.pdf) [3]

 [Convergence rates of efficient global optimization algorithms](https://www.jmlr.org/papers/v12/bull11a.html) 

Adam D. Bull (2011)

Journal of Machine Learning Research

📍 Mentioned in the provided partial results as a source of (near-)optimal simple-regret rates for EI under Matern-type smoothness.

 [Link ↗](https://www.jmlr.org/papers/v12/bull11a.html)

## Notes / Progress

_Work log goes here._
