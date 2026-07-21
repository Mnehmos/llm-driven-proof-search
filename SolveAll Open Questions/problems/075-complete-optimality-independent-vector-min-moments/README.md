# Complete optimality characterization in the independent-vector specialization under minimal moments

**Status:** Unsolved  
**Source:** Sourced from the work of Heejong Bong, Arun Kumar Kuchibhotla, Alessandro Rinaldo

## Categories

- Mathematical Statistics
- Probability Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #75 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $n,d\in\mathbb N$ . For each $i\in\{1,\dots,n\}$ , let $X_i=(X_{i1},\dots,X_{id})^\top\in\mathbb R^d$ be independent random vectors with $\mathbb E[X_i]=0$ . Define the normalized sum

$
S_n:=\frac{1}{\sqrt n}\sum_{i=1}^n X_i,
$

its covariance matrix

$
\Sigma_n:=\mathrm{Var}(S_n)=\frac1n\sum_{i=1}^n \mathbb E[X_iX_i^\top],
$

and let $Z_n\sim N(0,\Sigma_n)$ be the centered Gaussian vector with the same covariance. Let $\mathcal H_d$ be the class of axis-aligned hyperrectangles in $\mathbb R^d$ , e.g.

$
\mathcal H_d:=\Big\{\prod_{j=1}^d(-\infty,t_j]:\ t=(t_1,\dots,t_d)\in\mathbb R^d\Big\}.
$

For a given law $P$ of $(X_1,\dots,X_n)$ , define the rectangle Kolmogorov distance

$
\Delta(P):=\sup_{A\in\mathcal H_d}\left|\mathbb P_P(S_n\in A)-\mathbb P(Z_n\in A)\right|.
$

This setup follows [Bong et al. (2025)](#references) .

Assume finite third moments and coordinatewise nondegeneracy: for all $i,j$ , $\mathbb E|X_{ij}|^3<\infty$ , and there is a constant $\underline\sigma>0$ such that $\min_{1\le j\le d}(\Sigma_n)_{jj}\ge \underline\sigma^2$ . For $B<\infty$ , define

$
\mathcal P_{n,d}(\underline\sigma,B):=\left\{P:\ X_1,\dots,X_n\ \text{independent, mean zero},\ \min_j(\Sigma_n)_{jj}\ge \underline\sigma^2,\ \max_j\frac1n\sum_{i=1}^n \mathbb E|X_{ij}|^3\le B\right\},
$

and minimax risk

$
\mathfrak R_{n,d}(\underline\sigma,B):=\sup_{P\in\mathcal P_{n,d}(\underline\sigma,B)}\Delta(P).
$

### Unsolved Problem

Determine, regime by regime, whether the paper's stated independent-case rate for hyperrectangle CLT is minimax-optimal up to logarithmic factors in dimension, and identify regimes where a gap remains between known upper and lower bounds.

## Significance & Implications

The paper reports sharp rates and establishes optimality in some independent-case regimes under weak assumptions. Completing a regime-wise optimality map (up to logarithmic factors) would close the remaining gap in understanding when those rates are fully minimax-sharp.

## Known Partial Results

The paper's independent-vector specialization proves sharp bounds and shows optimality in selected regimes. This direction remains open as posed in arXiv:2306.14299v3.

## References

[1]

 [Dual Induction CLT for High-dimensional m-dependent Data](https://arxiv.org/abs/2306.14299v3) 

Heejong Bong, Arun Kumar Kuchibhotla, Alessandro Rinaldo (2023)

Annals of Statistics (to appear)

📍 Section 3 (Discussion), Open Problem 1: "Characterization of optimality for CLT under independence" (arXiv:2306.14299v3, p. 14).

Source paper where this problem appears (problem wording taken from the arXiv v3 discussion list).

 [Link ↗](https://arxiv.org/abs/2306.14299v3) [arXiv ↗](https://arxiv.org/abs/2306.14299v3)

## Notes / Progress

_Work log goes here._
