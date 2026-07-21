# Extension beyond convex differentiable-loss framework

**Status:** Unsolved  
**Source:** Sourced from the work of Takuya Koriyama, Pratik Patil, Jin-Hong Du, Kai Tan, Pierre C. Bellec

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #54 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(x_i,y_i)_{i=1}^n$ be training data with $x_i\in\mathbb R^p$ and $y_i\in\mathbb R$ , and let $p=p_n$ and subsample size $k=k_n$ satisfy proportional asymptotics $p/n\to\delta\in(0,\infty)$ and $k/n\to\kappa\in(0,1]$ . For each subsample index set $S\subseteq[n]$ with $|S|=k$ , define the regularized empirical $M$ -estimator

$
\widehat\beta_S\in\arg\min_{\beta\in\mathbb R^p}\left\{\frac1k\sum_{i\in S}\ell\big(y_i,x_i^\top\beta\big)+\lambda\,\rho(\beta)\right\},
$

where $\ell$ is a loss function, $\rho$ is a regularizer, and $\lambda>0$ is a tuning parameter. The infinite-subagged estimator is

$
\overline\beta_n:=\mathbb E_S\!\left[\widehat\beta_S\mid (x_i,y_i)_{i=1}^n\right],
$

with expectation over uniformly sampled subsamples $S$ .

This setup follows [Koriyama et al. (2025)](#references) .

In the source paper's baseline analyzed regime (Assumption A in [Koriyama et al. (2025)](#references) ), the loss is convex and differentiable and the regularizer is convex (with separable structure in the main development). Under the full assumption set used in the source, the main asymptotic results characterize deterministic limits for overlap/order-parameter quantities of independent subsample estimators and induced risk formulas for the subagged estimator, and provide a risk-estimation theorem under an additional stronger regularity condition.

### Unsolved Problem

Extend this asymptotic framework beyond the convex differentiable-loss setting while keeping the same high-dimensional subagging regime. In particular, determine precise conditions under which analogues of the main deterministic-limit and risk-estimation results remain valid when: (1) the loss is convex but non-differentiable (the paper notes Moreau smoothing as a possible route), (2) the strong-convexity-type assumption on the regularizer used for Theorem 5 is relaxed (the paper notes Gaussian smoothing as a possible route), and (3) the regularizer is non-separable.

## Significance & Implications

This is a direct open-direction item in Section 6 of Koriyama et al., focused on broadening the applicability of their asymptotic subagging framework beyond the currently analyzed smooth-loss setting.

## Known Partial Results

The cited source explicitly presents this as an open direction in Section 6 and does not provide a completed theorem for this extension there. Global resolution beyond this source was not fully verified .

## References

[1]

 [Precise Asymptotics of Bagging Regularized M-estimators](https://arxiv.org/abs/2409.15252) 

Takuya Koriyama, Pratik Patil, Jin-Hong Du, Kai Tan, Pierre C. Bellec (2025)

Annals of Statistics (to appear)

📍 Section 6 ("Extensions and open directions"), open-direction bullet "Assumptions on the loss and reg functions" (p. 28, arXiv v3)

Primary source where this open direction is explicitly listed.

 [Link ↗](https://arxiv.org/abs/2409.15252) [DOI ↗](https://doi.org/10.48550/arXiv.2409.15252) [arXiv ↗](https://arxiv.org/abs/2409.15252)

## Notes / Progress

_Work log goes here._
