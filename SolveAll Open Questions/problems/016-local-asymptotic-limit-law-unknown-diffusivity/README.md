# Local-asymptotic limit law with unknown diffusivity levels under vanishing jump

**Status:** Unsolved  
**Importance:** Notable
**Source:** Sourced from the work of Markus Reiss, Claudia Strauch, Lukas Trottner

## Categories

- Mathematical Statistics
- Probability Theory
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #16 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(\Omega,\mathcal F,(\mathcal F_t)_{t\in[0,T]},\mathbb P)$ carry a cylindrical Wiener process $W$ on $L^2(0,1)$ , fix $T>0$ , and consider the stochastic heat equation in weighted-Laplacian form

$
dX_t=\Delta_{\vartheta}X_t\,dt+dW_t,\qquad \Delta_{\vartheta}f:=\partial_x\big(\vartheta(x)\partial_x f\big),
$

on $(0,1)$ with Dirichlet boundary conditions and deterministic initial condition. Assume a one-change parametrization

$
\vartheta(x)=\vartheta^{\circ}+h\,\mathbf 1_{[\tau,1]}(x),\qquad \tau\in(\varepsilon,1-\varepsilon),\ \vartheta^{\circ}\in[\underline\vartheta,\overline\vartheta],\ \vartheta^{\circ}+h\in[\underline\vartheta,\overline\vartheta].
$

This setup follows [Reiß et al. (2023)](#references) .

For localization scale $\delta\downarrow0$ , let $K_{\delta,x_0}$ be the local measurement kernel(s) used in the source model and observe continuously in time the localized process

$
X_{\delta,x_0}(t):=\langle X_t,K_{\delta,x_0}\rangle,
$

together with the associated localized Laplacian term

$
X^{\Delta}_{\delta,x_0}(t):=\langle X_t,\Delta K_{\delta,x_0}\rangle
$

(and analogously for the finite collection of observation points/kernels in the experiment).

In the vanishing-jump regime $h=h_\delta\to0$ , under contiguous scaling where an oracle limit law is available when nuisance parameters are fixed, define the simultaneous M-estimator

$
(\hat\tau_\delta,\hat h_\delta,\hat\vartheta^{\circ}_\delta)
$

as any measurable maximizer of the source contrast (equivalently Gaussian quasi-likelihood) built from the local kernel observations and their $X^{\Delta}$ regressors.

### Unsolved Problem

Determine deterministic normalizations and a nondegenerate explicit joint weak limit law for the centered/scaled vector

$
\big(\hat\tau_\delta-\tau,\ \hat h_\delta-h_\delta,\ \hat\vartheta^{\circ}_\delta-\vartheta^{\circ}\big)
$

in this contiguous vanishing-jump regime, and quantify the efficiency loss (if any) of the change-point coordinate relative to the oracle benchmark with nuisance parameters known.

## Significance & Implications

The discussion in [Reiß et al. (2023)](#references) establishes the faint-signal limit theorem under a simplifying known-diffusivity setup; the simultaneous unknown-nuisance regime is therefore an important remaining inferential regime near detectability. Resolving it would quantify the cost of nuisance estimation at change-point scale and sharpen the local asymptotic theory for this observation model.

## Known Partial Results

The source paper derives consistency and rates for simultaneous M-estimation (including a nuisance baseline diffusivity parameter) and proves a vanishing-jump limit theorem in a simplified oracle setting with known diffusivity components.

## References

[1]

 [Change Point Estimation for a Stochastic Heat Equation](https://arxiv.org/abs/2307.10960v2) 

Markus Reiß, Claudia Strauch, Lukas Trottner (2023)

arXiv preprint (journal publication in Annals of Statistics reported separately; publication year not encoded here)

📍 arXiv:2307.10960v2, Section 4 (Discussion), Perspectives paragraph on the vanishing-jump regime with known diffusivity constants; PDF page 21 (printed page 22 in manuscript pagination).

Primary source for the model, estimators, and discussion of the vanishing-jump regime.

 [Link ↗](https://arxiv.org/abs/2307.10960v2) [arXiv ↗](https://arxiv.org/abs/2307.10960v2)

## Notes / Progress

_Work log goes here._
