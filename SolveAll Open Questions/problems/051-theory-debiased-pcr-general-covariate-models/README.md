# Theory for Debiased PCR Under General Covariate Models

**Status:** Unsolved  
**Source:** Sourced from the work of Yufan Li, Pragya Sur

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #51 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(x_i,y_i)_{i=1}^n$ be independent observations from the linear model

$
y_i=x_i^\top\beta_0+\varepsilon_i,\qquad i=1,\dots,n,
$

where $\beta_0\in\mathbb R^p$ is unknown, $x_i\in\mathbb R^p$ satisfies $\mathbb E[x_i]=0$ and $\mathrm{Cov}(x_i)=\Sigma$ (not assumed to be right-rotationally invariant), and $\varepsilon_i$ is independent of $x_i$ with $\mathbb E[\varepsilon_i]=0$ , $\mathrm{Var}(\varepsilon_i)=\sigma^2\in(0,\infty)$ . Write $X\in\mathbb R^{n\times p}$ for the design matrix (rows $x_i^\top$ ) and $y\in\mathbb R^n$ for the response vector.

Let the singular value decomposition of $X$ be $X=UDV^\top$ , with rank $r$ , singular values $d_1\ge\cdots\ge d_r>0$ , and right singular vectors $v_1,\dots,v_r$ . For a fixed truncation level $k\le r$ , define $V_k=(v_1,\dots,v_k)$ , $U_k=(u_1,\dots,u_k)$ , $D_k=\mathrm{diag}(d_1,\dots,d_k)$ , and the rank- $k$ principal components regression estimator

$
\hat\beta_k^{\mathrm{PCR}}=V_kD_k^{-1}U_k^\top y,
$

equivalently the least-squares estimator constrained to $\mathrm{span}(V_k)$ .

Consider a spectrum-aware debiased PCR estimator of the form

$
\hat\beta_k^{\mathrm{dPCR}}=\hat\beta_k^{\mathrm{PCR}}+M_k\frac{X^\top(y-X\hat\beta_k^{\mathrm{PCR}})}{n},
$

where $M_k\in\mathbb R^{p\times p}$ is a data-dependent matrix built from the empirical spectrum/eigenstructure of $X$ to correct truncation and regularization bias.

For a contrast vector $a\in\mathbb R^p$ , define the conditional centering and scale

$
\mathrm{Bias}_{a,k,n}:=\mathbb E\!\left[a^\top(\hat\beta_k^{\mathrm{dPCR}}-\beta_0)\mid X\right],\qquad
\mathrm{SE}_{a,k,n}^2:=\mathrm{Var}\!\left(a^\top\hat\beta_k^{\mathrm{dPCR}}\mid X\right).
$

The

### Unsolved Problem

Give sharp, verifiable conditions on $(\Sigma,\beta_0,\varepsilon_i)$ , dimension growth $(p,n,k)$ , and contrast classes $a$ (for example, deterministic or random $a$ with bounded norm/sparsity) under which, for general non-rotationally-invariant designs,

$
\frac{a^\top(\hat\beta_k^{\mathrm{dPCR}}-\beta_0)-\mathrm{Bias}_{a,k,n}}{\mathrm{SE}_{a,k,n}}
\Rightarrow \mathcal N(0,1),
$

and to construct plug-in estimators $\widehat{\mathrm{SE}}_{a,k,n}$ (and, if needed, $\widehat{\mathrm{Bias}}_{a,k,n}$ ) that are consistent so that asymptotically valid confidence intervals for $a^\top\beta_0$ follow uniformly over the stated contrast class.

## Significance & Implications

PCR is widely used in low-rank/high-collinearity settings; inference is often the bottleneck. A general theory would convert debiased PCR from a first construction into a robust inference tool across modern correlated designs. See [Li & Sur (2023)](#references) for details.

## Known Partial Results

The problem remains open in the cited source. The abstract claims the first debiased PCR estimator in high dimensions as a by-product of spectrum-aware debiasing.

## References

[1]

 [Spectrum-Aware Debiasing: A Modern Inference Framework with Applications to Principal Components Regression](https://arxiv.org/abs/2309.07810v6) 

Yufan Li, Pragya Sur (2023)

Annals of Statistics (to appear)

📍 Appendix I (Conjectures for general covariate models), Conjecture I.1

Source paper where this open problem is discussed.

 [Link ↗](https://arxiv.org/abs/2309.07810v6) [arXiv ↗](https://arxiv.org/abs/2309.07810v6)

## Notes / Progress

_Work log goes here._
