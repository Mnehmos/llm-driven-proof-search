# Sparsistent Estimation for Constrained Extremal Graphical Lasso

**Status:** Partially Resolved  
**Importance:** Notable
**Source:** Sourced from the work of Sebastian Engelke, Michael Lalancette, Stanislav Volgushev

## Categories

- Mathematical Statistics
- Combinatorics & Graph Theory
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #17 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $X^{(1)},\dots,X^{(n)}\in\mathbb{R}^d$ be i.i.d. observations (with $d=d_n$ allowed to grow) from a distribution in the max-domain of attraction of a $d$ -variate H"usler--Reiss law. Let $\Gamma^\star$ be the extremal variogram and $\widehat\Gamma$ an empirical estimator from extremes. Define

$
\mathcal S_1^d:=\{\Theta\in\mathbb{R}^{d\times d}:\Theta=\Theta^\top,\ \Theta\succeq0,\ \operatorname{rank}(\Theta)=d-1,\ \Theta\mathbf 1=0\},
$

and estimate $\Theta^\star\in\mathcal S_1^d$ via

$
\widehat\Theta\in\arg\min_{\Theta\in\mathcal S_1^d}
\left\{-\log\det^*(\Theta)-\frac12\operatorname{tr}(\widehat\Gamma\Theta)
+\lambda_n\sum_{i\ne j}w_{ij}|\Theta_{ij}|\right\}.
$

The 2021-vintage open question asked whether one can choose $(\lambda_n,w_{ij})$ and explicit scaling/regularity conditions so that

$
\Pr\big(\operatorname{supp}(\widehat\Theta)=\operatorname{supp}(\Theta^\star)\big)\to1
$

in high dimension, for global minimizers of this constrained program.

### Unsolved Problem

Post-2023 literature now gives positive sparsistency/graph-recovery results for related extremal-graph estimators, so the broad "is sparsistency possible at all?" question is no longer the right framing. The narrower unresolved variant is: establish a full high-dimensional support-recovery theorem for the exact constrained objective above (the constrained objective displayed above), with explicit assumptions and rates, and clarify when guarantees hold for all global minimizers under adaptive/weighted penalties.

## Significance & Implications

Historically (2021 context), this was a key gap between extremal graphical modeling and classical Gaussian graphical-lasso sparsistency theory. With later positive results for related extremal estimators, the remaining significance is now methodological precision: determining whether the specific constrained pseudo-likelihood formulation in Eq. (7.1) itself admits sharp, verifiable sparsistency guarantees (rather than relying on alternative estimators/pipelines).

## Known Partial Results

In arXiv v6, the authors still describe Eq. (7.1) as statistically challenging (nonconvex + linear constraints) and connect it to difficult weighted-lasso analysis under constraints. However, the same Section 7 text now cites newer papers with positive consistency/graph-recovery results for related extremal-graph estimators (including Wan and Zhou, 2025, and Engelke and Taeb, 2025). Therefore, the old claim that adaptive/nonconvex ideas are merely "suggested but not analyzed" is stale; progress exists, but a complete sparsistency theory for the exact constrained objective in Eq. (7.1) remains a narrower open direction.

## References

[1]

 [Learning extremal graphical structures in high dimensions](https://arxiv.org/abs/2111.00840v6) 

Sebastian Engelke, Michael Lalancette, Stanislav Volgushev (2021)

Annals of Statistics (to appear; arXiv preprint, revised through v6)

📍 arXiv:2111.00840v6, Section 7 ("Extensions and future work"), discussion around Eq. (7.1), including the sentence anchor beginning "This renders statistical analysis of (7.1) challenging..." and the immediately following lines citing recent related consistency results (Wan and Zhou, 2025; Engelke and Taeb, 2025).

Primary source of the constrained objective and its discussion; later arXiv revisions explicitly note post-2023 related progress.

 [Link ↗](https://arxiv.org/abs/2111.00840v6) [DOI ↗](https://doi.org/10.48550/arXiv.2111.00840) [arXiv ↗](https://arxiv.org/abs/2111.00840v6)

## Notes / Progress

_Work log goes here._
