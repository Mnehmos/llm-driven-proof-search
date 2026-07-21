# Multiple Risk Control Beyond Sequential Order: Graph-Structured Dependencies

**Status:** Unsolved  
**Importance:** Major
**Source:** Posed by Joshi, Sun, Hassani, and Dobriban (2025)

## Categories

- Mathematical Statistics
- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #6 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(X,Y,Y^*)$ denote input, model output, and reference output. For $m\ge 1$ constraints, the source paper defines score functions $S_j(X,Y,Y^*)$ and behavior-cost variables $V_j(X,Y,Y^*)\ge 0$ with thresholds $\lambda_j\in\Lambda_j\subset\mathbb R$ . In the sequential formulation (a chain of constraints), the $j$ -th constraint loss is

$
L_j(\lambda_{1:j})=V_j\,\mathbf 1\{S_1\le\lambda_1,\dots,S_{j-1}\le\lambda_{j-1},\ S_j>\lambda_j\},
$

and the objective loss is

$
L_{m+1}(\lambda_{1:m})=V_{m+1}\,\mathbf 1\{S_1\le\lambda_1,\dots,S_m\le\lambda_m\}.
$

The population target is

$
\min_{\lambda_1\in\Lambda_1,\dots,\lambda_m\in\Lambda_m}\ \mathbb E L_{m+1}(\lambda_{1:m})
\quad\text{s.t.}\quad
\mathbb E L_j(\lambda_{1:j})\le \beta_j\ \ (j\in[m]).
$

The paper introduces a dynamic-programming baseline (MRBase) and a finite-sample, distribution-free risk-controlling algorithm (MultiRisk) for this sequential dependence structure.

### Unsolved Problem

Extend finite-sample distribution-free multiple-risk control from the current sequential (totally ordered) dependence to general graph-structured dependence among risks. Formally, let $G=(V,E)$ be a directed acyclic graph on $V=[m]$ , with parent sets $\mathrm{pa}(j)$ . Define graph-triggered events $E_j(\lambda)$ from parent conditions and local score thresholds (the sequential case is the special path graph). Develop an algorithm that, for all $j\in[m]$ , guarantees

$
\mathbb E\big[V_j\mathbf 1\{E_j(\lambda)\}\big]\le \beta_j
$

in finite samples and distribution-free fashion, while keeping the objective risk near-optimal relative to the graph-structured population program, with explicit dependence on graph complexity, sample size, and number of risks.

## Significance & Implications

Real AI safety/quality pipelines often use interacting constraints rather than a strict sequence. Extending MultiRisk to graph-structured dependencies would substantially broaden practical applicability while preserving rigorous risk guarantees.

## Known Partial Results

- [Joshi et al. (2025)](#references) : gives finite-sample distribution-free control for multiple sequential constraints and near-optimality results under stated regularity conditions.

- The same source explicitly identifies extension to more general graph-structured dependence among risks as future work.

- Existing conformal risk-control tools provide ingredients for single or structured constraints, but a full finite-sample graph-structured theory with near-optimal objective guarantees is not yet available.

## References

[1]

 [MultiRisk: Multiple Risk Control via Iterative Score Thresholding](https://arxiv.org/abs/2512.24587) 

Sagar Joshi, Yifan Sun, Hamed Hassani, Edgar Dobriban (2025)

arXiv preprint

📍 Section 2 (problem formulation), Sections 4-5 (MRBase and MultiRisk algorithms and guarantees), and Section 7 (Conclusion: open extension to graph-structured dependencies among risks).

 [arXiv ↗](https://arxiv.org/abs/2512.24587) [2]

 [Conformal Risk Control](https://arxiv.org/abs/2208.02814) 

Anastasios N. Angelopoulos, Stephen Bates, et al. (2024)

arXiv preprint

📍 Distribution-free risk-control methodology motivating single- and multi-constraint conformal calibration.

 [arXiv ↗](https://arxiv.org/abs/2208.02814) [3]

 [Algorithmic Learning in a Random World](https://doi.org/10.1007/b106715) 

Vladimir Vovk, Alexander Gammerman, Glenn Shafer (2005)

Springer

📍 Nested prediction-set and exchangeability principles underlying distribution-free control constructions.

 [DOI ↗](https://doi.org/10.1007/b106715)

## Notes / Progress

_Work log goes here._
