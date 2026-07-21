# Quantify and characterize the efficiency gap induced by convex-loss restriction for non-log-concave errors

**Status:** Unsolved  
**Source:** Sourced from the work of Oliver Y. Feng, Yu-Chun Kao, Min Xu, Richard J. Samworth

## Categories

- Mathematical Statistics
- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #40 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $p \in \mathbb{N}$ be fixed, and suppose we observe i.i.d. pairs $(X_i,Y_i) \in \mathbb{R}^p \times \mathbb{R}$ , $i=1,\dots,n$ , from the linear model

$
Y_i = X_i^\top \beta_0 + \varepsilon_i,
$

where $\beta_0 \in \mathbb{R}^p$ is unknown, $X_i$ is independent of $\varepsilon_i$ , $\Sigma_X := \mathbb{E}[X_iX_i^\top]$ is positive definite, and $\varepsilon_i$ has density $f$ on $\mathbb{R}$ . Assume regularity conditions ensuring standard $M$ -estimation asymptotics (e.g., $\mathbb{E}\|X_i\|^{2+\delta}<\infty$ for some $\delta>0$ , integrability and stochastic equicontinuity conditions, and nondegeneracy of curvature terms).

For a convex loss $\rho:\mathbb{R}\to\mathbb{R}$ , write $\psi=\rho'$ . Assume $\psi$ is absolutely continuous (so $\psi'$ exists a.e.), $\mathbb{E}[\psi'(\varepsilon_i)]\in(0,\infty)$ , and $\mathbb{E}[\psi(\varepsilon_i)^2]<\infty$ . For Fisher consistency/identification, assume $\mathbb{E}[\psi(\varepsilon_i)]=0$ and that $\beta_0$ is the unique root of $\mathbb{E}[\psi(Y-X^\top b)X]=0$ . Define the convex $M$ -estimator

$
\hat\beta_\rho \in \arg\min_{b\in\mathbb{R}^p}\sum_{i=1}^n \rho(Y_i-X_i^\top b).
$

Its asymptotic covariance matrix is

$
\operatorname{Avar}(\hat\beta_\rho)
=
\frac{\mathbb{E}[\psi(\varepsilon)^2]}{\mathbb{E}[\psi'(\varepsilon)]^2}\,\Sigma_X^{-1}.
$

Assume $f$ is known. Let $s_f(u):=\frac{d}{du}\log f(u)$ and $I_f:=\mathbb{E}[s_f(\varepsilon)^2]$ (finite, positive Fisher information for location). The oracle maximum-likelihood estimator

$
\hat\beta_{\mathrm{MLE},f}\in \arg\min_{b\in\mathbb{R}^p}\sum_{i=1}^n \bigl(-\log f(Y_i-X_i^\top b)\bigr)
$

has asymptotic covariance

$
\operatorname{Avar}(\hat\beta_{\mathrm{MLE},f}) = I_f^{-1}\Sigma_X^{-1}.
$

For the class $\mathcal{C}_{\mathrm{cvx}}(f)$ of convex losses $\rho$ satisfying the above conditions, define the best convex relative efficiency

$
\mathcal{E}_{\mathrm{cvx}}(f)
:=
\sup_{\rho\in\mathcal{C}_{\mathrm{cvx}}(f)}
\frac{\operatorname{Avar}(\hat\beta_{\mathrm{MLE},f})}{\operatorname{Avar}(\hat\beta_\rho)}
=
\sup_{\rho\in\mathcal{C}_{\mathrm{cvx}}(f)}
\frac{\mathbb{E}[\psi'(\varepsilon)]^2}{I_f\,\mathbb{E}[\psi(\varepsilon)^2]},
$

which, when $\rho$ is twice differentiable with integrable $\rho''$ , is equivalently

$
\frac{\mathbb{E}[\rho''(\varepsilon)]^2}{I_f\,\mathbb{E}[\rho'(\varepsilon)^2]}.
$

The matrix ratio is interpreted in Loewner order (equivalently here as a scalar ratio since both covariances are multiples of $\Sigma_X^{-1}$ ).

### Unsolved Problem

For non-log-concave $f$ (so $-\log f$ is not convex), determine and characterize $\mathcal{E}_{\mathrm{cvx}}(f)$ : compute or bound it for broad classes of such $f$ , characterize exactly when $\mathcal{E}_{\mathrm{cvx}}(f)=1$ , and establish nontrivial distribution-free lower bounds on $\mathcal{E}_{\mathrm{cvx}}(f)$ under explicit regularity assumptions on $f$ (e.g., smoothness, tail, and Fisher-information conditions).

## Significance & Implications

The abstract gives one non-log-concave example (Cauchy) with efficiency above $0.87$ , suggesting convex estimators can remain highly competitive. A general theory of the efficiency gap would clarify when convexity is effectively free and when it is statistically costly. This directly informs robustness-computation-efficiency tradeoffs in practice. See [Feng et al. (2024)](#references) for details.

## Known Partial Results

The paper derives the optimal convex loss via a score-matching/log-concave-projection principle and proves asymptotic optimality within convex $M$ -estimators. It provides the Cauchy case as evidence of high efficiency (>0.87) but does not claim a full characterization across error distributions.

## References

[1]

 [Optimal Convex $M$-Estimation via Score Matching](https://arxiv.org/abs/2403.16688v2) 

Oliver Y. Feng, Yu-Chun Kao, Min Xu, Richard J. Samworth (2024)

arXiv preprint

📍 arXiv:2403.16688v2, Section 5 (Discussion), paragraph beginning "A particularly interesting question concerns the magnitude of $\\eta_f$", PDF p. 19.

Primary preprint source where the efficiency-gap discussion is posed.

 [Link ↗](https://arxiv.org/abs/2403.16688v2) [arXiv ↗](https://arxiv.org/abs/2403.16688v2) [2]

 [Optimal Convex $M$-Estimation via Score Matching](https://www.repository.cam.ac.uk/handle/1810/389606) 

Oliver Y. Feng, Yu-Chun Kao, Min Xu, Richard J. Samworth

Annals of Statistics (to appear)

📍 Cambridge Apollo metadata record (accepted version), journal field listed as Annals of Statistics.

Journal-publication metadata kept separate from preprint metadata; journal publication year to be filled once finalized.

 [Link ↗](https://www.repository.cam.ac.uk/handle/1810/389606)

## Notes / Progress

_Work log goes here._
