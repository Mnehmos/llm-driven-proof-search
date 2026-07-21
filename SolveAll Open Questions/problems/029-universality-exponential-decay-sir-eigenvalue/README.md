# Universality of exponential decay of the d-th SIR eigenvalue

**Status:** Unsolved  
**Source:** Sourced from the work of Dongming Huang, Songtao Tian, Qian Lin

## Categories

- Mathematical Statistics
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #29 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $d\in\mathbb N$ and $p\ge d$ . Consider the multiple-index regression model

$
Y=f(PX)+\varepsilon,
$

where $X\in\mathbb R^p$ is Gaussian with law $N(0,I_p)$ , $P\in\mathbb R^{d\times p}$ has orthonormal rows ( $PP^\top=I_d$ ), $f:\mathbb R^d\to\mathbb R$ is measurable, and $\varepsilon\in\mathbb R$ is independent of $X$ with $\mathbb E[\varepsilon]=0$ and $\mathbb E[\varepsilon^2]<\infty$ . Define the SIR population matrix

$
M:=\operatorname{Cov}\!\big(\mathbb E[X\mid Y]\big)\in\mathbb R^{p\times p},
$

and let $\lambda_1(M)\ge\cdots\ge\lambda_p(M)\ge0$ be its eigenvalues. The quantity of interest is the $d$ -th eigenvalue $\lambda_d(M)$ .

This setup follows [Huang et al. (2023)](#references) .

### Unsolved Problem

 **Problem 2.** Characterize the largest class $\mathcal F$ of link functions (or laws of random link functions) such that, for every $d$ (and uniformly over $p\ge d$ , admissible $P$ , and admissible noise laws), there exist constants $C,\beta>0$ independent of $d$ for which

$
\lambda_d\!\big(\operatorname{Cov}(\mathbb E[X\mid Y])\big)\le C e^{-\beta d}.
$

For deterministic $f$ , this is a pointwise bound on $M$ ; for random $f$ , require the bound with high probability over the draw of $f$ (equivalently, specify a probability level tending to $1$ as $d\to\infty$ ). In particular, determine whether this exponential decay of $\lambda_d(M)$ holds beyond Gaussian-process-based random-link settings.

## Significance & Implications

In Huang, Tian, and Lin (arXiv:2305.04340v2), this universality question is explicitly posed as open in the discussion of gSNR decay. Resolving whether exponential decay is universal, rather than tied to specific random-function assumptions, is central to understanding when SIR degrades as structural dimension grows.

## Known Partial Results

In the canonical arXiv v2 source, the universality question is open and no general beyond-model theorem is claimed there. Later manuscript versions report Gaussian-process-specific exponential-decay progress, but this does not resolve universality beyond GP-type assumptions.

## References

[1]

 [On the Structural Dimension of Sliced Inverse Regression](https://arxiv.org/abs/2305.04340v2) 

Dongming Huang, Songtao Tian, Qian Lin (2023)

arXiv preprint

📍 Section 5 (Discussions), paragraph beginning “Our findings raise several open questions,” second open question on exponential decay of gSNR (arXiv v2).

Canonical source version for this problem statement.

 [Link ↗](https://arxiv.org/abs/2305.04340v2) [arXiv ↗](https://arxiv.org/abs/2305.04340v2)

## Notes / Progress

_Work log goes here._
