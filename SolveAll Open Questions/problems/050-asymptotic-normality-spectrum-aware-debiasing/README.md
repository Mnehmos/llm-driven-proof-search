# Asymptotic Normality of Spectrum-Aware Debiasing Beyond Right-Rotationally Invariant Designs

**Status:** Unsolved  
**Source:** Sourced from the work of Yufan Li, Pragya Sur

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #50 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

For each $n$ , observe $(y,X)$ from the high-dimensional linear model

$
y=X\beta_0+\varepsilon,\qquad X\in\mathbb R^{n\times p},\ y\in\mathbb R^n,\ \beta_0\in\mathbb R^p,\ \varepsilon\in\mathbb R^n,
$

with proportional asymptotics $p=p_n$ , $p_n/n\to\gamma\in(0,\infty)$ . Let

$
S_n:=\frac1nX^\top X=V_n\,\mathrm{diag}(\lambda_{1,n},\dots,\lambda_{p,n})\,V_n^\top
$

be the spectral decomposition of the sample covariance.

Fully explicit definition of the operator $\mathcal P_n$ : for any measurable scalar transfer function $\wp_n:[0,\infty)\to\mathbb R$ , define the spectral-functional operator

$
\mathcal P_n(S_n):=V_n\,\mathrm{diag}\!\big(\wp_n(\lambda_{1,n}),\dots,\wp_n(\lambda_{p,n})\big)\,V_n^\top\in\mathbb R^{p\times p}.
$

Equivalently, $\mathcal P_n$ applies $\wp_n$ to each eigenvalue of $S_n$ and keeps the same eigenvectors (standard matrix functional calculus).

Given an initial estimator $\hat\beta^{\mathrm{init}}$ , define the one-step spectrum-aware debiased estimator by

$
\hat\beta^{\mathrm{SAD}}=\hat\beta^{\mathrm{init}}+\eta_n\,\mathcal P_n\!\left(S_n\right)\frac1nX^\top\!\left(y-X\hat\beta^{\mathrm{init}}\right).
$

In the baseline right-rotationally invariant SAD formula of [Li & Sur (2025)](#references) , this reduces to a scalar-rescaled gradient correction (the paper's spectrum-aware adjustment), i.e. a special case of the above with scalar preconditioning.

This setup follows [Li & Sur (2025)](#references) .

Detailed known theorem under right-rotationally invariant designs (source Theorem 3.1/Corollary 3.2/Theorem 6.2, notation of arXiv v6): assume

- 

Right-rotationally invariant design $X=Q^\top D O$ with $O\sim\mathrm{Haar}(\mathcal O(p))$ , $O\perp\varepsilon$ , empirical singular-value distribution converging in $W_2$ , and bounded operator norm of $X^\top X$ .

- 

Gaussian noise $\varepsilon\sim N(0,\sigma^2 I_n)$ and signal regularity as in the source (deterministic or random-independent with empirical $W_2$ limit).

- 

Convex penalty regularity and fixed-point existence assumptions of the source.

- 

(If $\sigma^2$ is unknown) the source's nondegeneracy condition enabling consistent noise-level estimation.

Then the paper proves:

- Empirical-distribution CLT:

$
\hat\tau_{*,n}^{-1/2}\big(\hat\beta^{\mathrm{SAD}}-\beta_0\big)\ \xrightarrow[W_2]{}\ \mathcal N(0,1)
$

a.s. as $n,p\to\infty$ .

- Finite-dimensional (hence coordinatewise) CLT under the source exchangeability condition on $\beta_0$ : for any fixed finite index set $\mathcal I$ ,

$
\frac{\hat\beta^{\mathrm{SAD}}_{\mathcal I}-\beta_{0,\mathcal I}}{\sqrt{\hat\tau_{*,n}}}
\Rightarrow
\mathcal N\!\big(0,I_{|\mathcal I|}\big),
$

so in particular for fixed coordinate $j$ ,

$
\frac{\hat\beta^{\mathrm{SAD}}_j-\beta_{0,j}}{\sqrt{\hat\tau_{*,n}}}\Rightarrow\mathcal N(0,1).
$

- Consistent estimation of centering/scale quantities used by the inference procedure (including the asymptotic variance):

$
\hat\gamma_n\to\gamma_*,\quad \hat\eta_n\to\eta_*,\quad \hat\tau_{*,n}\to\tau_*,\quad \hat\tau_{**,n}\to\tau_{**},
$

and (when unknown) $\hat\sigma_n^2\to\sigma^2$ , a.s.

### Unsolved Problem

The documented open extension (Appendix D, Conjecture D.1) asks whether an analogous coordinatewise CLT and consistent variance estimation continue to hold for the paper's ellipsoidal design model class.

Precisely, for the ellipsoidal models in Conjecture D.1, define the design as

$
X=Q_n^\top D_n O_n\Sigma_n^{1/2},
$

where $\Sigma_n\in\mathbb R^{p\times p}$ is observed and nonsingular, $Q_n\in\mathbb R^{n\times n}$ and $O_n\in\mathbb R^{p\times p}$ are orthogonal, $D_n\in\mathbb R^{n\times p}$ is diagonal (rectangular), and $O_n\sim\mathrm{Haar}(\mathcal O(p))$ is independent of $(\varepsilon,Q_n,D_n)$ .

Allow a (possibly non-separable) proper closed convex penalty $\mathcal H_n:\mathbb R^p\to\mathbb R\cup\{+\infty\}$ and initial estimator

$
\hat\beta^{\mathrm{init}}\in\arg\min_{b\in\mathbb R^p}\ \frac12\|y-Xb\|_2^2+\mathcal H_n(b).
$

The ellipsoidal SAD correction considered in Appendix D is

$
\hat\beta^{\mathrm{ell}}=\hat\beta^{\mathrm{init}}+\frac1{\alpha_n}\,\Sigma_n^{-1}X^\top\!\left(y-X\hat\beta^{\mathrm{init}}\right),
$

where $\alpha_n$ solves the fixed-point equation

$
\frac1p\sum_{i=1}^p\frac{1}{\frac{d_{i,n}^2-\alpha_n}{p}\,\mathrm{Tr}\!\left(\alpha_n I_p+\Sigma_n^{-1}\nabla^2\mathcal H_n(\hat\beta^{\mathrm{init}})\right)^{-1}+1}=1,
$

with $d_{i,n}^2$ the eigenvalues of $X^\top X$ (and with the same extension convention for non-smooth penalties used in the source).

Question: prove or disprove that for each fixed coordinate $j$ there exist a centering term $b_{j,n}$ and a consistent variance estimator $\hat\tau_{j,n}^2$ such that

$
\frac{\hat\beta^{\mathrm{ell}}_j-\beta_{0,j}-b_{j,n}}{\hat\tau_{j,n}}\ \xRightarrow[n,p\to\infty]{}\ \mathcal N(0,1),
\qquad
\hat\tau_{j,n}^2/\tau_{j,n}^2\overset{p}\to 1,
$

with nondegenerate limit scale $\tau_{j,n}^2$ , without right-rotational invariance.

## Significance & Implications

Appendix D records this as an explicit open extension (ellipsoidal models). Resolving it would determine whether the proven right-rotationally-invariant CLT extends at least to that specific non-RRI class.

## Known Partial Results

The paper proves asymptotic normality (with proper centering/scaling) and consistent variance estimation for right-rotationally invariant designs; Appendix D states Conjecture D.1 for ellipsoidal models as open. No definitive published proof or counterexample resolving Conjecture D.1 is identified in the cited sources.

## References

[1]

 [Spectrum-Aware Debiasing: A Modern Inference Framework with Applications to Principal Components Regression](https://doi.org/10.1214/24-AOS2482) 

Yufan Li, Pragya Sur (2025)

Annals of Statistics

Published journal citation.

 [Link ↗](https://doi.org/10.1214/24-AOS2482) [DOI ↗](https://doi.org/10.1214/24-AOS2482) [2]

 [Spectrum-Aware Debiasing: A Modern Inference Framework with Applications to Principal Components Regression](https://arxiv.org/abs/2309.07810v6) 

Yufan Li, Pragya Sur (2023)

📍 Appendix D (Conjectures for Ellipsoidal Models), Conjecture D.1, with the immediately following sentence: "We leave the proof of Conjecture D.1 as an open problem"; pp. 56-57 (arXiv v6).

Preprint version used for exact appendix citation.

 [Link ↗](https://arxiv.org/abs/2309.07810v6) [arXiv ↗](https://arxiv.org/abs/2309.07810v6)

## Notes / Progress

_Work log goes here._
