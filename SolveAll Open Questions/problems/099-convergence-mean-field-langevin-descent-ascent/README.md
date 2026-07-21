# Convergence of single-timescale mean-field Langevin descent-ascent for two-player zero-sum games

**Status:** Partially Resolved  
**Source:** Posed by Guillaume Wang et al. (2024)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #99 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $T^d=(\mathbb{R}/\mathbb{Z})^d$ be the flat $d$ -torus with Lebesgue measure, and let $\mathcal{P}(T^d)$ be the set of Borel probability measures on $T^d$ . Fix $\beta>0$ and a smooth payoff $f\in C^\infty(T^d\times T^d)$ . Define, for $(\mu,\nu)\in\mathcal{P}(T^d)\times\mathcal{P}(T^d)$ ,

$
F_\beta(\mu,\nu)=\iint f(x,y)\,d\mu(x)\,d\nu(y)+\beta^{-1}H(\mu)-\beta^{-1}H(\nu),
$

where $H(\rho)=\int_{T^d} r\log r$ if $\rho$ has density $r$ w.r.t. Lebesgue measure and $H(\rho)=+\infty$ otherwise. In this setting $F_\beta$ has a unique saddle point $(\mu^\star,\nu^\star)$ (the entropy-regularized mixed Nash equilibrium).

Consider the single-timescale Wasserstein gradient descent-ascent (GDA) flow associated with $F_\beta$ : $\mu_t$ follows the Wasserstein gradient flow that decreases $\mu\mapsto F_\beta(\mu,\nu_t)$ while $\nu_t$ follows the Wasserstein gradient flow that increases $\nu\mapsto F_\beta(\mu_t,\nu)$ , using the same time parameter $t$ . For instance, when $\mu_t=m_t\,dx$ and $\nu_t=n_t\,dy$ have smooth positive densities, writing $\Phi_{\nu}(x)=\int f(x,y)\,d\nu(y)$ and $\Psi_{\mu}(y)=\int f(x,y)\,d\mu(x)$ , the formal PDE system is

$
\partial_t m_t=\nabla\cdot\big(m_t\nabla\Phi_{\nu_t}\big)+\beta^{-1}\Delta m_t,\qquad
\partial_t n_t=-\nabla\cdot\big(n_t\nabla\Psi_{\mu_t}\big)+\beta^{-1}\Delta n_t,
$

with gradients and Laplacians on $T^d$ .

### Unsolved Problem

For every smooth $f$ and every $\beta>0$ , do trajectories $(\mu_t,\nu_t)$ of this single-timescale Wasserstein GDA flow converge as $t\to\infty$ (e.g. weakly in $\mathcal{P}(T^d)$ for each marginal) to the unique saddle point $(\mu^\star,\nu^\star)$ ?

## Significance & Implications

This asks for a qualitative long-time convergence result for a coupled descent-ascent flow in Wasserstein space that models the mean-field (infinite-particle) limit of Langevin descent-ascent in entropy-regularized two-player zero-sum games. A proof (or a counterexample) would clarify whether the natural single-timescale min-max dynamics is intrinsically stabilizing at the PDE/measure level, beyond regimes where one can enforce convergence by separating ascent and descent timescales.

## Known Partial Results

- The functional $F_\beta$ is entropy-regularized (via $\beta^{-1}H(\mu)$ and $-\beta^{-1}H(\nu)$ ) and admits a unique saddle point $(\mu^\star,\nu^\star)$ , interpreted as the entropy-regularized mixed Nash equilibrium.

- The associated Wasserstein gradient descent-ascent flow $(\mu_t,\nu_t)$ corresponds to the mean-field limit of a Langevin descent-ascent particle dynamics.

- Convergence can be ensured by using different timescales for descent and ascent (a timescale-separated variant), but the single-timescale convergence question remains open for general smooth $f$ and $\beta>0$ .

- Seo, Shin, Monmarche, and Choi (arXiv 2602.01564, February 2, 2026) prove local exponential stability near equilibrium, giving partial progress, but global convergence from arbitrary initialization remains open.

## References

[1]

 [Open problem: Convergence of single-timescale mean-field Langevin descent-ascent for two-player zero-sum games](https://proceedings.mlr.press/v247/wang24c.html) 

Guillaume Wang, LÃ©naÃ¯c Chizat (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/wang24c.html) [2]

 [Open problem: Convergence of single-timescale mean-field Langevin descent-ascent for two-player zero-sum games (PDF)](https://proceedings.mlr.press/v247/wang24c/wang24c.pdf) 

Guillaume Wang, LÃ©naÃ¯c Chizat (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/wang24c/wang24c.pdf)

## Notes / Progress

_Work log goes here._
