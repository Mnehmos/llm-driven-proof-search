# Early-stopping optimality without a U-shape risk assumption

**Status:** Unsolved  
**Source:** Sourced from the work of Pierre C Bellec, Kai Tan

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #67 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Consider the high-dimensional linear regression model with i.i.d. training data $D_n=\{(x_i,y_i)\}_{i=1}^n$ , where for each $i$ ,

$
y_i=x_i^\top\beta^\star+\varepsilon_i,\qquad x_i\in\mathbb R^p,\ \beta^\star\in\mathbb R^p,
$

with $x_i\sim N(0,\Sigma)$ for some positive semidefinite $\Sigma\in\mathbb R^{p\times p}$ , $\varepsilon_i\sim N(0,\sigma^2)$ , and $\varepsilon_i$ independent of $x_i$ . Let $p=p_n$ be comparable to $n$ (for example $p_n/n\to\kappa\in(0,\infty)$ ). Let an iterative algorithm (such as gradient descent, proximal gradient descent, or an accelerated variant) produce estimators $\hat\beta^0,\hat\beta^1,\dots,\hat\beta^{T_n}\in\mathbb R^p$ , where each $\hat\beta^t$ is measurable with respect to $D_n$ (and any internal algorithmic randomness), and $T_n\ge 1$ may depend on $n$ .

For each iteration $t\in\{1,\dots,T_n\}$ , define the population prediction risk (generalization error) of $\hat\beta^t$ by

$
R_t:=\mathbb E\!\left[(Y^{\mathrm{new}}-(X^{\mathrm{new}})^\top \hat\beta^t)^2\mid D_n\right],
$

where $(X^{\mathrm{new}},Y^{\mathrm{new}})$ is an independent test pair distributed as $(x_i,y_i)$ . Thus $(R_t)_{t=1}^{T_n}$ is a random sequence induced by $D_n$ .

### Unsolved Problem

Construct a fully data-driven stopping time $\hat t=\hat t(D_n)\in\{1,\dots,T_n\}$ such that, without imposing any structural shape condition on $t\mapsto R_t$ (in particular, without assuming unimodality or a U-shape),

$
R_{\hat t}-\min_{1\le t\le T_n}R_t=o_{\mathbb P}(1)\quad\text{as }n\to\infty,
$

or, preferably, to prove a nonasymptotic oracle inequality of the form

$
\mathbb P\!\left(R_{\hat t}\le \min_{1\le t\le T_n}R_t+\Delta_n\right)\ge 1-\alpha_n,
$

with explicit $\Delta_n\to 0$ and $\alpha_n\to 0$ , under verifiable conditions on $(n,p_n,\Sigma,\beta^\star,\sigma^2)$ and the iterative update rule.

## Significance & Implications

The cited Bellec-Tan guarantee is conditional on a U-shape assumption for the risk trajectory. Removing that assumption would substantially broaden the reliability of data-driven early stopping. Post-2024 results in related inverse-problem settings also indicate that additive adaptation slack can be intrinsic, so identifying the sharp achievable guarantee in this linear-regression setting is practically and theoretically important.

## Known Partial Results

Bellec-Tan provide trajectory risk estimators and, under their U-shape condition, data-driven selection of $\hat t$ is near-oracle up to estimation error. A conservative generic formulation is

$
R_{\hat t}\le \min_{1\le t\le T_n}R_t + 2\sup_{1\le t\le T_n}|\hat R_t-R_t|,
$

where $\hat R_t$ denotes the estimated risk used for selection; hence the guarantee is an approximate oracle inequality with explicit additive slack, not exact attainment of $\min_t R_t$ . In related post-2024 early-stopping theory for inverse problems, explicit non-vanishing remainder terms and necessity phenomena are proved, suggesting that some adaptation slack may be unavoidable without additional structure.

## References

[1]

 [Uncertainty quantification for iterative algorithms in linear models with application to early stopping](https://arxiv.org/abs/2404.17856v1) 

Pierre C Bellec, Kai Tan (2024)

Annals of Statistics (future paper; no volume/DOI listed )

📍 Section 1.3 (Early stopping), unnumbered paragraph in the introduction, p. 4 of arXiv v1; publication status cross-checked against the Annals of Statistics Future Papers page on 2026-02-17.

Primary source where the U-shape-conditional early-stopping claim is stated.

 [Link ↗](https://arxiv.org/abs/2404.17856v1) [arXiv ↗](https://arxiv.org/abs/2404.17856v1) [2]

 [Early stopping for conjugate gradients in statistical inverse problems](https://link.springer.com/article/10.1007/s00211-025-01469-4) 

Laura Hucker, Markus Reiss (2025)

Numerische Mathematik 157 (2025), 1739-1791, doi:10.1007/s00211-025-01469-4

📍 Abstract and Section 3/Theorem 6.8 discussion (notably the explicit additive term and statement that no classical oracle inequality is available in that setting).

Related post-2024 evidence: oracle-type bounds can require explicit additive remainder terms, and a classical exact-oracle form need not hold.

 [Link ↗](https://link.springer.com/article/10.1007/s00211-025-01469-4)

## Notes / Progress

_Work log goes here._
