# Bernstein-von Mises validity for the linearized Bayesian construction in nonlinear inverse problems

**Status:** Unsolved  
**Source:** Sourced from the work of Geerten Koers, Botond Szabo, Aad van der Vaart

## Categories

- Mathematical Statistics
- Analysis & PDEs

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #85 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal O\subset\mathbb R^d$ be a domain and let $f:\mathcal O\to\mathbb R$ be unknown. Suppose $u_f$ solves the nonlinear PDE

$
Lu_f=c(f,u_f)\quad\text{on }\mathcal O,\qquad u_f=g\quad\text{on }\Gamma\subset\partial\mathcal O,
$

where $L$ is a linear differential operator and there is a reconstruction map $e$ such that

$
f=e(Lu_f).
$

Observe

$
Y_n=u_f+n^{-1/2}W,
$

in the Gaussian white-noise model (or the discrete-design analogue treated in the paper). The source paper constructs a posterior for the linear inverse problem of recovering $Lu_f$ and then pushes that posterior forward through $e$ to obtain a posterior on $f$ .

### Unsolved Problem

Prove or refute a Bernstein-von Mises theorem for this induced posterior, strong enough to justify asymptotically correct frequentist coverage for credible intervals of smooth functionals $T(f)$ and for credible balls in weak norms under the paper's main linearized construction.

## Significance & Implications

A positive result would turn the paper's computationally attractive two-step linearization into a fully calibrated uncertainty-quantification method for nonlinear PDE inverse problems, connecting Bayesian computation with semiparametric frequentist coverage for scientifically meaningful functionals.

## Known Partial Results

- The source paper proves optimal recovery rates, adaptive contraction results, and frequentist coverage guarantees for certain credible sets under its linearized method.

- [Nickl (2018)] proves Bernstein-von Mises theorems for a Schrödinger inverse-problem setting.

- [Monard, Nickl & Paternain (2021)] establish Bayesian uncertainty-quantification guarantees for nonlinear inverse problems with Gaussian process priors.

- What remains unresolved in the source paper is whether comparable Bernstein-von Mises coverage for smooth functionals and weak-norm credible balls holds for its general two-step linearized construction.

## References

[1]

 [Linear methods for non-linear inverse problems](https://arxiv.org/abs/2411.19797v1) 

Geerten Koers, Botond Szabo, Aad van der Vaart (2024)

Annals of Statistics (to appear)

📍 Introduction, p. 4, paragraph beginning "The coverage of credible intervals for smooth functionals..." in arXiv v1.

Source paper where the Bernstein-von Mises question is posed for the paper's main linearized construction.

 [Link ↗](https://arxiv.org/abs/2411.19797v1) [DOI ↗](https://doi.org/10.48550/arXiv.2411.19797) [arXiv ↗](https://arxiv.org/abs/2411.19797v1) [2]

 [Bernstein-von Mises Theorems for statistical inverse problems I: Schrodinger Equation](https://scholar.google.com/scholar?q=Bernstein-von%20Mises%20Theorems%20for%20statistical%20inverse%20problems%20I%3A%20Schrodinger%20Equation) 

Richard Nickl (2018)

Journal of the European Mathematical Society

Special-case Bernstein-von Mises results for an inverse-problem setting cited by the source paper.

[3]

 [Statistical guarantees for Bayesian uncertainty quantification in nonlinear inverse problems with Gaussian process priors](https://scholar.google.com/scholar?q=Statistical%20guarantees%20for%20Bayesian%20uncertainty%20quantification%20in%20nonlinear%20inverse%20problems%20with%20Gaussian%20process%20priors) 

François Monard, Richard Nickl, Gabriel P. Paternain (2021)

Annals of Statistics

Provides nonlinear-inverse-problem Bayesian UQ guarantees in a different Gaussian-process-prior framework, giving relevant partial progress.

## Notes / Progress

_Work log goes here._
