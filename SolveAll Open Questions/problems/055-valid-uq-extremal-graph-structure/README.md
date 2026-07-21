# Valid Uncertainty Quantification for Extremal Graph Structure

**Status:** Unsolved  
**Source:** Sourced from the work of Sebastian Engelke, Michael Lalancette, Stanislav Volgushev

## Categories

- Mathematical Statistics
- Combinatorics & Graph Theory
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #55 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Engelke, Lalancette, and Volgushev (Annals of Statistics, 2025) explicitly identify uncertainty quantification for estimated extremal graphs as an important future direction, beyond graph recovery. The source does not itself state a fully formal high-dimensional simultaneous-inference theorem with explicit uniform size/coverage or FWER/FDR formulas.

This setup follows [Engelke et al. (2025)](#references) .

### Unsolved Problem

Let $d=d_n$ and let $Y^{(1)},\dots,Y^{(n)}$ be i.i.d. observations from a $d$ -variate H"usler--Reiss multivariate Pareto model on $E=\{y\in[0,\infty)^d:\max_{1\le r\le d}y_r>1\}$ with variogram matrix $\Gamma=(\Gamma_{rs})_{1\le r,s\le d}$ . Assume $\Gamma$ is symmetric, $\Gamma_{rr}=0$ , and strictly conditionally negative definite (equivalently: negative definite on $\{x\in\mathbb R^d:\sum_r x_r=0,\ x\neq 0\}$ ), so that for anchor $m=d$ the matrix

$
\Sigma_{ij}=\frac{1}{2}\big(\Gamma_{id}+\Gamma_{jd}-\Gamma_{ij}\big),\qquad i,j\in\{1,\dots,d-1\},
$

is positive definite and hence $\Theta=\Sigma^{-1}$ is well-defined. In this model class, the extremal graph on vertices $\{1,\dots,d-1\}$ has edge $\{i,j\}$ iff $\Theta_{ij}\neq 0$ for $i\neq j$ .

Open problem: construct edge-wise and simultaneous inferential procedures for off-diagonal entries of $\Theta$ that remain valid when both $n\to\infty$ and $d=d_n\to\infty$ . For each pair $i\neq j$ , target tests of

$
H_0^{ij}:\Theta_{ij}=0 \quad\text{versus}\quad H_1^{ij}:\Theta_{ij}\neq 0,
$

and $(1-\alpha)$ confidence intervals $C_{ij}$ with high-dimensional uniform guarantees over suitable classes (e.g., bounded spectrum, sparsity, and admissible growth):

$
\sup_{P\in\mathcal P_n^{ij,0}}\big|\Pr_P(\text{reject }H_0^{ij})-\alpha\big|\to 0,\qquad
\sup_{P\in\mathcal P_n}\big|\Pr_P(\Theta_{ij}\in C_{ij})-(1-\alpha)\big|\to 0.
$

Also target simultaneous error criteria such as asymptotic FWER/FDR control, e.g. $\Pr_P(V\ge 1)\le \alpha+o(1)$ or $\mathbb E_P[V/\max\{R,1\}]\le q+o(1)$ .

## Significance & Implications

The source paper establishes the need for uncertainty quantification in extremal graphical models. Since 2021, related inference developments (including H"usler--Reiss matrix-completion and likelihood-based uncertainty-quantification work in lower- or moderate-dimensional regimes) have improved the toolkit, but they do not yet close the core high-dimensional-uniform inference gap for edge-wise and simultaneous graph uncertainty.

## Known Partial Results

Partially resolved outside the strict open scope: existing results provide concentration guarantees and graph-recovery consistency, and newer post-2021 work gives additional inference machinery in more restricted settings. Still open in the stated sense: high-dimensional, uniform-valid edge-wise and simultaneous inference guarantees for extremal graph structure.

## References

[1]

 [Learning extremal graphical structures in high dimensions](https://doi.org/10.1214/24-AOS2467) 

Sebastian Engelke, Michael Lalancette, Stanislav Volgushev (2025)

Annals of Statistics

📍 Section 7 (Extensions and future work) in the published Annals version, paragraph beginning "Another highly promising direction for future research is uncertainty quantification for the estimated graph..."

Published source paper; the uncertainty-quantification direction is discussed as future work.

 [Link ↗](https://doi.org/10.1214/24-AOS2467) [DOI ↗](https://doi.org/10.1214/24-AOS2467) [arXiv ↗](https://arxiv.org/abs/2111.00840)

## Notes / Progress

_Work log goes here._
