# Generalization-error estimation beyond Gaussian designs

**Status:** Unsolved  
**Source:** Sourced from the work of Pierre C Bellec, Kai Tan

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #66 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(x_i,y_i)_{i=1}^n$ be i.i.d. training data with $x_i\in\mathbb R^p$ and

$
y_i=x_i^\top\beta_0+\varepsilon_i,
$

where $\beta_0\in\mathbb R^p$ is deterministic (or independent of the sample), $\mathbb E[\varepsilon_i\mid x_i]=0$ , and $\mathbb E[\varepsilon_i^2\mid x_i]<\infty$ . Write $X\in\mathbb R^{n\times p}$ for the design matrix with rows $x_i^\top$ , and $y=(y_1,\dots,y_n)^\top$ .

Assume a high-dimensional regime $n,p\to\infty$ with $p/n\to\gamma\in(0,\infty)$ under non-Gaussian random designs (e.g., sub-Gaussian or elliptical families with conditions sufficient for asymptotic normality arguments). For fixed iteration index $t\in\mathbb N$ , let $\hat\beta^t=\hat\beta^t(X,y)$ be the $t$ -th iterate of a first-order method (such as GD, proximal GD, or an accelerated variant) applied to least squares, possibly with a proper closed convex penalty. With independent test covariate $x_{\mathrm{new}}\sim x_i$ , define

$
R_t:=\mathbb E\!\left[\left(x_{\mathrm{new}}^\top\hat\beta^t-x_{\mathrm{new}}^\top\beta_0\right)^2\mid X,y\right].
$

### Unsolved Problem

For fixed $t$ , construct a data-driven estimator $\hat R_t$ of $R_t$ that admits a valid $\sqrt n$ -scale limit law under non-Gaussian designs, with finite nondegenerate asymptotic variance and conditions for consistent variance estimation.

## Significance & Implications

The cited work studies uncertainty quantification for fixed-time iterates in high-dimensional linear models under Gaussian-design assumptions. A non-Gaussian extension remains a natural and practically important direction, but the exact scope of what is already proved beyond Gaussian settings should be treated cautiously pending a dedicated 2025-2026 literature check.

## Known Partial Results

Under Gaussian-design assumptions, the cited paper establishes $\sqrt n$ -scale uncertainty quantification for risk estimation at fixed iterate $t$ for several first-order algorithms. Open-status assessment for non-Gaussian designs requires dedicated literature verification.

## References

[1]

 [Uncertainty quantification for iterative algorithms in linear models with application to early stopping](https://arxiv.org/abs/2404.17856v1) 

Pierre C Bellec, Kai Tan (2024)

Annals of Statistics (to appear)

📍 Section 5 (Discussion), exact paragraph citation to be pinned after direct full-text verification of the final published version.

Primary source motivating this formalization; non-Gaussian extension remains an open direction.

 [Link ↗](https://arxiv.org/abs/2404.17856v1) [arXiv ↗](https://arxiv.org/abs/2404.17856v1)

## Notes / Progress

_Work log goes here._
