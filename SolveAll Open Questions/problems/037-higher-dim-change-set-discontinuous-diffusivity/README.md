# Higher-dimensional change-set (interface) estimation for discontinuous diffusivity

**Status:** Partially Resolved  
**Source:** Sourced from the work of Markus Reiss, Claudia Strauch, Lukas Trottner

## Categories

- Mathematical Statistics
- Probability Theory
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #37 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $d\ge 2$ , let $D\subset\mathbb R^d$ be a bounded domain with $C^2$ boundary, fix $T>0$ , and fix known constants $\vartheta_1,\vartheta_2$ with $0<\vartheta_1\neq \vartheta_2<\infty$ . For an unknown measurable set $G\subset D$ , define the diffusivity

$
\vartheta_G(x)=\vartheta_1\mathbf 1_G(x)+\vartheta_2\mathbf 1_{D\setminus G}(x),\qquad x\in D.
$

Consider the stochastic parabolic equation (in weak/mild sense)

$
du_t(x)=\nabla\!\cdot\!\big(\vartheta_G(x)\nabla u_t(x)\big)\,dt + B\,dW_t(x),\qquad (t,x)\in(0,T]\times D,
$

with boundary condition $u_t(x)=0$ for $x\in\partial D$ , initial condition $u_0\in L^2(D)$ known, $W$ a cylindrical Wiener process on $L^2(D)$ , and $B$ a known linear noise operator chosen so the equation is well posed.

This setup follows [Reiß et al. (2025)](#references) .

For each spatial resolution $\delta>0$ , assume one observes the locally averaged field

$
Y_\delta(t,x)=\int_D K_\delta(x-z)u_t(z)\,dz,\qquad (t,x)\in[0,T]\times D_\delta,
$

where $K_\delta(z)=\delta^{-d}K(z/\delta)$ for a known compactly supported kernel $K$ with $\int_{\mathbb R^d}K=1$ , and $D_\delta=\{x\in D:\operatorname{dist}(x,\partial D)>\delta\,\operatorname{rad}(\operatorname{supp}K)\}$ . Thus $\delta\to 0$ corresponds to increasingly local spatial measurements over fixed time horizon $[0,T]$ .

### Unsolved Problem

Assume $G$ belongs to a geometric class $\mathcal G$ (for example, sets whose interface $\partial G$ is a compact embedded $C^\beta$ hypersurface with uniformly bounded curvature/reach and $\operatorname{dist}(\partial G,\partial D)\ge r_0>0$ ). The problem is to construct estimators $\widehat G_\delta=\widehat G_\delta(Y_\delta)$ (equivalently $\widehat{\partial G}_\delta$ ) and determine asymptotic inference limits as $\delta\to 0$ , including:

$
\inf_{\widehat G_\delta}\sup_{G\in\mathcal G}\mathbb E_G\!\left[d_H\!\big(\partial\widehat G_\delta,\partial G\big)\right],
\qquad
\inf_{\widehat G_\delta}\sup_{G\in\mathcal G}\mathbb E_G\!\left[\,|\widehat G_\delta\triangle G|\,\right],
$

where $d_H$ is Hausdorff distance and $\triangle$ is symmetric difference; rates, possible limit distributions of scaled local interface errors, and minimax lower bounds over $\mathcal G$ under explicit regularity assumptions.

## Significance & Implications

The one-dimensional unknown jump location is the simplest instance of a geometric inverse problem. Extending to unknown interfaces broadens applicability and connects SPDE inference with nonparametric boundary estimation in higher dimensions. See Reiß, Strauch, and Trottner (Annals of Statistics, 2025) and subsequent multivariate follow-up work.

## Known Partial Results

Reiß-Strauch-Trottner (Annals of Statistics, 2025) provide the full technical treatment for the 1D single-discontinuity setting. A multivariate follow-up (arXiv:2504.18023; SPA, 2026) gives additional higher-dimensional/interface results under specific assumptions. A fully sharp, fully general minimax and limit-theory characterization across broad geometric classes remains only partially resolved.

## References

[1]

 [Change Point Estimation for a Stochastic Heat Equation](https://doi.org/10.1214/24-AOS2462) 

Markus Reiß, Claudia Strauch, Lukas Trottner (2025)

Annals of Statistics 53(3):1540-1572

📍 Section 4 (Discussion), "Perspectives" paragraph on estimating a higher-dimensional change domain/interface.

Published source paper; preprint available at https://arxiv.org/abs/2307.10960.

 [Link ↗](https://doi.org/10.1214/24-AOS2462) [DOI ↗](https://doi.org/10.1214/24-AOS2462) [arXiv ↗](https://arxiv.org/abs/2307.10960) [2]

 [Multivariate follow-up on change-set/interface estimation for stochastic heat equations](https://arxiv.org/abs/2504.18023) 

Unknown (2026)

Stochastic Processes and their Applications (2026)

Post-2023 progress with multivariate/interface results; cited for scoped status update.

 [Link ↗](https://arxiv.org/abs/2504.18023) [arXiv ↗](https://arxiv.org/abs/2504.18023)

## Notes / Progress

_Work log goes here._
