# Provable Estimation Procedures Under the New Identifiability Criterion

**Status:** Unsolved  
**Source:** Sourced from the work of Daniele Tramontano, Mathias Drton, Jalal Etesami

## Categories

- Mathematical Statistics
- Probability Theory
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #59 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Source-verified identification facts (from the cited paper): consider the acyclic linear non-Gaussian SEM with latent confounding

$
X = B^\top X + h(U) + \varepsilon,
$

where $B$ encodes a DAG over observed variables (up to permutation), $\varepsilon$ has mutually independent non-Gaussian coordinates, $U\perp\!\!\!\perp\varepsilon$ , and $h(U)$ allows general (nonparametric) latent confounding. Under the paper's acyclic identifiability criterion, $B$ is generically identifiable from the observational law $\mathcal L(X)$ . The paper also reports estimation heuristics, but does not claim a full consistency/asymptotic-normality theory for estimation in this fully general nonlinear-confounding setup.

This setup follows [Tramontano et al. (2025)](#references) .

### Unsolved Problem

Given i.i.d. samples $X^{(1)},\dots,X^{(n)}\sim\mathcal L(X)$ and regularity assumptions sufficient for asymptotic analysis (for example, suitable moment/tail conditions and identifiability-margin conditions), construct a computationally explicit estimator $\hat B_n$ such that

$
\hat B_n\xrightarrow{p}B,
$

and ideally

$
\sqrt n\,\mathrm{vec}(\hat B_n-B)\xRightarrow{d}\mathcal N(0,\Sigma),
$

with a consistent covariance estimator and, if possible, finite-sample/nonasymptotic error bounds. The open challenge is to establish such guarantees in the fully general case where $h(U)$ is unrestricted nonlinear latent confounding.

## Significance & Implications

The paper establishes population-level generic identifiability, but reliable data analysis needs estimators with proved statistical guarantees. For the fully general nonlinear-confounding model class, this inference layer remains unresolved in the source framing.

## Known Partial Results

The paper provides identification results and reports estimation heuristics, but does not provide a complete statistical theory with general consistency/asymptotic-normality guarantees under unrestricted nonlinear latent confounding. This direction remains open for the fully general nonlinear-confounding case.

## References

[1]

 [Parameter identification in linear non-Gaussian causal models under general confounding](https://arxiv.org/abs/2405.20856) 

Daniele Tramontano, Mathias Drton, Jalal Etesami (2024)

Annals of Statistics (in press; listed on Future Papers, volume/issue/pages/DOI pending )

📍 Open-problem wording location: Section 9 (Conclusions), first paragraph immediately following Section 8.2 ("Causal Effect Estimation"), where the paper states estimation is heuristic and leaves a full statistical theory (e.g., consistency/asymptotic normality) open.

Primary source paper and publication-status record for this problem; no final volume/issue/pages/DOI were publicly listed at verification time.

 [Link ↗](https://arxiv.org/abs/2405.20856) [arXiv ↗](https://arxiv.org/abs/2405.20856)

## Notes / Progress

_Work log goes here._
