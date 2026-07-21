# Goodness-of-Fit Test for the Husler-Reiss Domain of Attraction

**Status:** Unsolved  
**Importance:** Notable
**Source:** Sourced from the work of Sebastian Engelke, Michael Lalancette, Stanislav Volgushev

## Categories

- Mathematical Statistics
- Combinatorics & Graph Theory
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #18 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $X_1,\dots,X_n$ be i.i.d. random vectors in $\mathbb R^d$ with joint distribution function $F$ and continuous univariate margins $F_1,\dots,F_d$ . Define the marginally standardized variables

$
U_{i,j}=\frac{1}{1-F_j(X_{i,j})},\qquad i=1,\dots,n,\ j=1,\dots,d,
$

so each $U_{i,j}$ is standard Pareto, and write $U_i=(U_{i,1},\dots,U_{i,d})$ .

This setup follows [Engelke et al. (2021)](#references) .

For a symmetric matrix $\Gamma=(\Gamma_{ab})_{a,b=1}^d$ with $\Gamma_{aa}=0$ and conditionally negative definite (equivalently, a valid Gaussian variogram matrix), define the $d$ -variate H"usler--Reiss max-stable distribution with unit Fr'echet margins by

$
G_\Gamma(z)=\exp\{-V_\Gamma(z)\},\qquad z\in(0,\infty)^d,
$

where

$
V_\Gamma(z)=\sum_{m=1}^d \frac{1}{z_m}\,\Phi_{d-1}\!\left(\log\!\frac{z_{-m}}{z_m}+\frac{\Gamma_{-m,m}}{2};\,\Sigma^{(m)}\right),
$

 $\Phi_{d-1}(\cdot;\Sigma^{(m)})$ is the $(d-1)$ -variate centered Gaussian cdf with covariance matrix $\Sigma^{(m)}$ , $z_{-m}$ is $z$ with coordinate $m$ removed, $\Gamma_{-m,m}$ is the vector $(\Gamma_{jm})_{j\neq m}$ , and for $i,j\neq m$ ,

$
\Sigma^{(m)}_{ij}=\frac{\Gamma_{im}+\Gamma_{jm}-\Gamma_{ij}}{2}.
$

Define the H"usler--Reiss domain-of-attraction class

$
\mathcal D_{\mathrm{HR}}=\bigcup_{\Gamma} \mathcal D(G_\Gamma),
$

where $F\in\mathcal D(G_\Gamma)$ means that there exist normalizing constants $a_{n,j}>0$ , $b_{n,j}\in\mathbb R$ such that, for all continuity points $x\in\mathbb R^d$ ,

$
\Pr\!\left(\max_{1\le i\le n}\frac{X_{i,j}-b_{n,j}}{a_{n,j}}\le x_j,\ j=1,\dots,d\right)\to G_\Gamma(x).
$

(Equivalently after marginal standardization, maxima converge to $G_\Gamma$ with unit Fr'echet margins.)

The source paper explicitly identifies the construction of a principled goodness-of-fit test for membership in the H"usler--Reiss domain of attraction as an important future research direction, and states that such a principled test is not known there.

### Unsolved Problem

Construct a test $\phi_n\in\{0,1\}$ for

$
H_0:\ F\in\mathcal D_{\mathrm{HR}}
\qquad\text{vs}\qquad
H_1:\ F\notin\mathcal D_{\mathrm{HR}},
$

with unknown nuisance variogram $\Gamma$ (and unknown margins), based on threshold exceedances. For $k_n\to\infty$ and $k_n/n\to0$ , let $r_n=n/k_n$ , define $R_i=\max_{1\le j\le d}U_{i,j}$ , and use $\{U_i:R_i>r_n\}$ . Desired guarantees include asymptotic size control

$
\sup_{F\in H_0}\limsup_{n\to\infty}\Pr_F(\phi_n=1)\le \alpha
$

for prescribed $\alpha\in(0,1)$ , plus nontrivial power under $H_1$ (ideally consistency against fixed alternatives).

## Significance & Implications

The theory in the source paper is developed under H"usler--Reiss domain-of-attraction assumptions; without a dedicated GOF test for this assumption, applicability on real data is hard to validate.

## Known Partial Results

Focused post-2021 audit (2022-2025) of literature explicitly centered on H"usler--Reiss graphical/extremal modeling found advances in estimation, structure learning, latent-variable recovery, and model-comparison diagnostics, but no explicit hypothesis test with null $H_0:F\in\mathcal D_{\mathrm{HR}}$ (unknown margins and nuisance variogram) and corresponding asymptotic size guarantees. This supports retaining the problem label as open.

## References

[1]

 [Learning extremal graphical structures in high dimensions](https://arxiv.org/abs/2111.00840v6) 

Sebastian Engelke, Michael Lalancette, Stanislav Volgushev (2021)

Annals of Statistics (to appear/in press; issue details not yet fixed in cited public records)

📍 Section 7 (Extensions and future work), open-problem discussion on GOF testing for the H\"usler--Reiss domain of attraction, including the statement that this is an important future direction and that no principled test was known to the authors.

Primary source of the open problem. Year=2021 follows arXiv posting/version convention; final journal publication year may differ once issue metadata is assigned.

 [Link ↗](https://arxiv.org/abs/2111.00840v6) [arXiv ↗](https://arxiv.org/abs/2111.00840v6) [2]

 [Statistical Inference for H\"usler-Reiss Graphical Models Through Matrix Completions](https://arxiv.org/abs/2210.14292) 

Manuel Hentschel, Sebastian Engelke, Johan Segers (2022)

arXiv preprint

📍 Abstract and methodology focus on inference for sparse H\"usler--Reiss models via matrix completion.

Post-2021 HR literature relevant to the audit: focuses on parameter/graph inference, not a GOF test for $F\in\mathcal D_{\mathrm{HR}}$.

 [Link ↗](https://arxiv.org/abs/2210.14292) [arXiv ↗](https://arxiv.org/abs/2210.14292) [3]

 [Graphical models for multivariate extremes](https://arxiv.org/abs/2402.02187) 

Sebastian Engelke, Manuel Hentschel, Micha\"el Lalancette, Frank R\"ottger (2024)

arXiv preprint

📍 Survey sections on model properties, inference, and structure learning for extremal graphical models.

Post-2021 review/audit source: surveys graphical-extremes methodology; does not provide a dedicated GOF test for HR domain-of-attraction membership.

 [Link ↗](https://arxiv.org/abs/2402.02187) [arXiv ↗](https://arxiv.org/abs/2402.02187) [4]

 [Extremal graphical modeling with latent variables via convex optimization](https://arxiv.org/abs/2403.09604) 

Sebastian Engelke, Abbas Taeb (2024)

arXiv preprint

📍 Abstract and main results center on convex-program-based graph/latent recovery guarantees.

Post-2021 HR-focused development: latent-variable structure learning for HR graphical models; not a GOF test of $\mathcal D_{\mathrm{HR}}$.

 [Link ↗](https://arxiv.org/abs/2403.09604) [arXiv ↗](https://arxiv.org/abs/2403.09604)

## Notes / Progress

_Work log goes here._
