# Sharp dynamic emergence thresholds for XOR/multilayer GMM classification

**Status:** Unsolved  
**Source:** Sourced from the work of Gerard Ben Arous, Reza Gheissari, Jiaoyang Huang, Aukosh Jagannath

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #80 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $u,v\in\mathbb R^d$ be orthonormal unit vectors, let $m>0$ , and sample a hidden sign pair $S=(s_1,s_2)\in\{\pm1\}^2$ uniformly. Define

$
\mu_S=m(s_1u+s_2v),\qquad X=\mu_S+\beta^{-1/2}Z,\qquad Z\sim\mathcal N(0,I_d).
$

The observed class label is the XOR label $Y=s_1s_2\in\{\pm1\}$ (equivalently, one class has $s_1=s_2$ and the other has $s_1\ne s_2$ ). Work in proportional asymptotics $n,d\to\infty$ with $n/d\to\phi\in(0,\infty)$ .

Use a two-layer classifier with fixed hidden width $K=O(1)$ and activation $g$ :

$
s_c(x)=v^c\cdot g(W^cx),\qquad L((W,v);(y,x))=-\sum_{c=1}^{\mathcal C} y_c s_c(x)+\log\sum_{c=1}^{\mathcal C}e^{s_c(x)}.
$

Train by online SGD with step size $\eta$ on fresh samples. The role of fixed width is that $K$ does not scale with $d,n$ , so the summary-statistic dimension remains finite; this is exactly what allows a finite-dimensional effective spectral description in the high-dimensional limit.

Let $G(x)$ be the summary-statistic Gram matrix built from first-layer weights and class means, and define the effective trajectory

$
G_t=\lim_{d\to\infty}G\!\left(x_{\lfloor t/\eta\rfloor}\right).
$

As shown in [Ben Arous et al. (2025)](#references) , $G_t$ solves a finite-dimensional autonomous ODE $dG_t/dt=\mathsf F(G_t)$ , and the first-layer Hessian/Gradient spectra at time $t$ are approximated by deterministic objects depending only on $(G_t,\beta)$ .

For the Hessian block under study, let $\nu_{G_t,\beta}^H$ be the effective bulk measure (defined via its Stieltjes fixed-point equation) and define its right spectral edge by

$
\lambda_+(t,\beta):=\sup\operatorname{supp}(\nu_{G_t,\beta}^H).
$

Effective outliers are then the real roots outside the bulk of the finite-dimensional equation

$
\det\!\big(\lambda I_q-F^H(\lambda;G_t,\beta)\big)=0,\qquad \lambda>\lambda_+(t,\beta),
$

where $q=K+k$ in the source corollary notation and $F^H$ is an explicit $q\times q$ matrix-valued function defined by Gaussian expectations. Equivalently, with

$
M(\lambda;G_t,\beta):=\lambda I_q-F^H(\lambda;G_t,\beta),
$

outliers solve $\det M(\lambda;G_t,\beta)=0$ for $\lambda>\lambda_+(t,\beta)$ .

### Unsolved Problem

Define the effective right-outlier count

$
N_{\mathrm{out}}(t,\beta):=\#\left\{\lambda>\lambda_+(t,\beta):\det\!\big(\lambda I_q-F^H(\lambda;G_t,\beta)\big)=0\right\},
$

counting multiplicity, and define the first-emergence curve

$
t_*(\beta):=\inf\{t\ge 0:N_{\mathrm{out}}(t,\beta)\ge 1\}.
$

Obtain a sharp characterization of dynamic emergence/splitting thresholds in this XOR/multilayer setting, including explicit critical curves such as $t_*(\beta)$ (or equivalently $\beta_*(t)$ ), and conditions for uniqueness versus multiple/non-monotone transition events.

Motivation for this open direction: the source already proves the effective finite-dimensional equations and large-SNR/post-burn-in outlier-based success/failure phenomena, and explicitly identifies sharp SNR/time emergence thresholds in the XOR case as a remaining open objective. The unresolved part is the sharp analysis of these explicit finite-dimensional equations along the effective dynamics trajectory.

## Significance & Implications

This links trainability/success-failure regimes to geometric phase transitions during optimization and could make spectral diagnostics operational for predicting when informative directions appear during training in nonlinearly separable tasks.

## Known Partial Results

In this paper itself, the authors establish effective spectral machinery and prove large-SNR, post-burn-in outlier/success-failure results in their analyzed regimes. However, the sharp XOR/multilayer dynamic threshold and exact transition-point characterization posed here is left open in the cited source.

## References

[1]

 [Local geometry of high-dimensional mixture models: Effective spectral theory and dynamical transitions](https://arxiv.org/abs/2502.15655) 

Gerard Ben Arous, Reza Gheissari, Jiaoyang Huang, Aukosh Jagannath (2025)

arXiv preprint; Annals of Statistics (to appear)

📍 Section 1.5.1 (Multi-layer GMM classification), paragraph after Corollary 1.13 (Introduction), which states that understanding sharp SNR thresholds and emergence points of effective outliers is of interest.

Primary source for this problem statement. Year denotes the arXiv preprint year (2025), not a final journal publication year.

 [Link ↗](https://arxiv.org/abs/2502.15655) [arXiv ↗](https://arxiv.org/abs/2502.15655)

## Notes / Progress

_Work log goes here._
