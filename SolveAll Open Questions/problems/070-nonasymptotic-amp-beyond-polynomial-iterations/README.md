# Non-asymptotic AMP distributional theory beyond polynomially many iterations

**Status:** Unsolved  
**Source:** Sourced from the work of Gen Li, Yuting Wei

## Categories

- Mathematical Statistics
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #70 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix integers $n,p\ge 1$ and let $X\in\mathbb{R}^{n\times p}$ have independent entries $X_{ij}\sim N(0,1/n)$ . Let $\delta=p/n$ . Consider two high-dimensional regression models with unknown signal $\beta_0\in\mathbb{R}^p$ and response $y\in\mathbb{R}^n$ .

This setup follows [Li & Wei (2024)](#references) .

In the sparse linear model, $y=X\beta_0+w$ , where $w\in\mathbb{R}^n$ has independent mean-zero sub-Gaussian coordinates (often Gaussian). One AMP convention is

$
r^t=y-X\beta^t+b_t r^{t-1},\qquad 
\beta^{t+1}=\eta_t(\beta^t+X^\top r^t),\qquad t\ge 0,
$

with $\beta^0$ (typically $0$ ), $r^{-1}=0$ , and coordinatewise denoiser $\eta_t$ . In this convention, the Onsager term uses the previous denoiser derivative,

$
b_t=\frac{1}{n}\sum_{j=1}^p \eta_{t-1}'\big((\beta^{t-1}+X^\top r^{t-1})_j\big),\qquad t\ge 1,
$

(with $b_0=0$ ), while equivalent index-shifted conventions also appear in the literature.

In robust linear regression, one estimates $\beta_0$ by an $M$ -estimator based on a convex loss $\rho$ with score $\psi=\rho'$ . A corresponding AMP scheme has the form

$
z^t=y-X\beta^t+c_t z^{t-1},\qquad 
\beta^{t+1}=\beta^t+\kappa_t X^\top \psi_t(z^t),\qquad t\ge 0,
$

where $\psi_t$ are iteration-dependent Lipschitz score maps (possibly regularized/proximal versions of $\psi$ ), $\kappa_t$ is a deterministic scaling, and $c_t$ is the Onsager correction determined by the average divergence of the nonlinear update.

Existing non-asymptotic results in this sparse/robust regression AMP framework establish finite-sample Gaussian/state-evolution approximation guarantees up to polynomial-length horizons under stated assumptions (model class, moments, and regularity of nonlinearities), with explicit high-probability error bounds depending on $n,p,t$ . These results should not be interpreted as uniform guarantees for arbitrary pseudo-Lipschitz observables at all polynomial horizons without the paper's explicit conditions.

### Unsolved Problem

Under explicit regularity assumptions on the signal/noise distributions and AMP nonlinearities (e.g., bounded moments, Lipschitz derivatives, well-posed Onsager terms), prove analogous finite-sample non-asymptotic distributional guarantees for horizons beyond $O\!\left(n/\operatorname{poly}(\log n)\right)$ , ideally up to data-dependent algorithmic convergence time. The goal is explicit, non-vacuous error bounds $\varepsilon(n,p,t)$ and tail probabilities that remain controlled uniformly over such longer horizons for both sparse-regression AMP and robust-regression AMP.

## Significance & Implications

Many inferential and optimization questions depend on late-iteration behavior, especially near convergence. Extending guarantees beyond currently proved polynomial-length regimes in this setting would narrow the gap between finite-time theory and practical AMP usage, and sharpen distributional understanding of downstream estimators. See [Li & Wei (2024)](#references) for details.

## Known Partial Results

In the sparse/robust regression AMP context, earlier asymptotic analyses typically covered only relatively short iteration windows (e.g., $t=o(\log n/\log\log n)$ in certain settings). This paper provides a finite-sample non-asymptotic distributional theory for sparse- and robust-regression AMP over polynomially many iterations under its stated assumptions.

## References

[1]

 [A non-asymptotic distributional theory of approximate message passing for sparse and robust regression](https://arxiv.org/abs/2401.03923) 

Gen Li, Yuting Wei (2024)

Annals of Statistics (accepted; to appear)

📍 Section 4 (Discussion), bullet point on guarantees for polynomially many iterations and the challenge of extending beyond that regime (p. 18 in arXiv version).

Source paper where this problem appears.

 [Link ↗](https://arxiv.org/abs/2401.03923) [arXiv ↗](https://arxiv.org/abs/2401.03923)

## Notes / Progress

_Work log goes here._
