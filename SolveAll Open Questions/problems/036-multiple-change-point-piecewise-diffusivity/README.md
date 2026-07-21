# Multiple change-point inference for piecewise constant diffusivity

**Status:** Unsolved  
**Source:** Sourced from the work of Markus Reiss, Claudia Strauch, Lukas Trottner

## Categories

- Mathematical Statistics
- Probability Theory
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #36 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Consider a one-dimensional stochastic heat equation with multiple change points in piecewise-constant diffusivity and local spatial measurements at resolution $\delta\to 0$ . Let $(\Omega,\mathcal F,(\mathcal F_t)_{0\le t\le T},\mathbb P)$ be a filtered probability space, $T\in(0,\infty)$ fixed, and let $W$ be a cylindrical Wiener process on $L^2(0,1)$ . Consider

$
\begin{cases}
dX(t,x)=\partial_x\!\big(\vartheta(x)\partial_x X(t,x)\big)\,dt+dW(t,x), & (t,x)\in(0,T]\times(0,1),\\
X(0,x)=0, & x\in(0,1),\\
X(t,0)=X(t,1)=0, & t\in[0,T],
\end{cases}
$

with piecewise-constant diffusivity

$
\vartheta(x)=\sum_{j=1}^{m+1}\vartheta_j\,\mathbf 1_{(\tau_{j-1},\tau_j]}(x),\qquad
0=\tau_0<\tau_1<\cdots<\tau_m<\tau_{m+1}=1,
$

where $m\in\mathbb N_0$ , jump locations $(\tau_j)_{j=1}^m$ , and levels $(\vartheta_j)_{j=1}^{m+1}$ are unknown, subject to $0<\underline\vartheta\le\vartheta_j\le\overline\vartheta<\infty$ .

For $\delta=1/n\to0$ , let $x_k=k\delta$ and $K\in H^2(\mathbb R)$ be compactly supported, with $K_{\delta,k}(x)=\delta^{-1/2}K((x-x_k)/\delta)$ . In line with the single-jump setup, use both local measurements

$
Y_{\delta,k}(t)=\langle X(t,\cdot),K_{\delta,k}\rangle_{L^2(0,1)},\qquad
Z_{\delta,k}(t)=\langle X(t,\cdot),\Delta K_{\delta,k}\rangle_{L^2(0,1)},\qquad 0\le t\le T,
$

for admissible $k$ (with support inside $(0,1)$ ), where in 1D $\Delta=\partial_{xx}$ .

### Unsolved Problem

Under explicit minimal-spacing and minimal-jump conditions, e.g.

$
\min_{1\le j\le m+1}(\tau_j-\tau_{j-1})\ge s_\delta,\qquad
\min_{1\le j\le m}|\vartheta_{j+1}-\vartheta_j|\ge a_\delta,
$

construct estimators of $(m,\tau_1,\dots,\tau_m,\vartheta_1,\dots,\vartheta_{m+1})$ that are jointly consistent and characterize achievable rates and (where feasible) limit laws for location/level errors.

## Significance & Implications

The cited work analyzes a one-jump baseline model. Treating multiple jumps is a natural but nontrivial extension relevant for heterogeneous media and for connecting SPDE inverse problems with change-point/segmentation theory.

## Known Partial Results

Available results in the cited preprint cover the one-jump case (including rates and a faint-signal limit theorem in a restricted setting). No claim is made here that optimal 1D multi-jump theory is currently unresolved without dedicated, up-to-date verification.

## References

[1]

 [Change Point Estimation for a Stochastic Heat Equation](https://arxiv.org/abs/2307.10960v2) 

Markus Reiß, Claudia Strauch, Lukas Trottner (2023)

arXiv preprint

📍 Abstract (first paragraph) and introductory setup for one unknown jump.

Primary accessible source for the single-jump model and results; multiple jumps are not formulated there as a numbered open problem.

 [Link ↗](https://arxiv.org/abs/2307.10960v2) [arXiv ↗](https://arxiv.org/abs/2307.10960v2) [2]

 [Change Point Estimation for a Stochastic Heat Equation](https://arxiv.org/abs/2307.10960v2) 

Markus Reiß, Claudia Strauch, Lukas Trottner (2026)

Annals of Statistics (forthcoming/in press; final bibliographic details pending)

📍 Bibliographic publication-status record; not tied to a separate multi-jump theorem statement.

Journal-status record kept separate from preprint metadata; add DOI, volume, issue, and page range once finalized.

 [Link ↗](https://arxiv.org/abs/2307.10960v2)

## Notes / Progress

_Work log goes here._
