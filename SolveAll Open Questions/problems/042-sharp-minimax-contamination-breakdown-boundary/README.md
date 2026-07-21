# Sharp minimax behavior as contamination approaches the breakdown boundary (epsilon up to 1/2)

**Status:** Unsolved  
**Source:** Sourced from the work of Akshay Prasadan, Matey Neykov

## Categories

- Mathematical Statistics
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #42 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $d,N\in\mathbb N$ , let $K\subseteq\mathbb R^d$ be a nonempty star-shaped set with respect to some center $c\in K$ (that is, for every $x\in K$ and $t\in[0,1]$ , $c+t(x-c)\in K$ ; the origin-centered condition is the special case $c=0$ used in the cited paper), and let $\epsilon\in [Prasadan & Neykov (2024)](#references) .

The clean sample is $Y_1,\dots,Y_N$ with $Y_i\overset{i.i.d.}{\sim}\mathcal N(\mu,I_d)$ , where $I_d$ is the $d\times d$ identity matrix. An adversary is allowed to choose a (possibly data-dependent and randomized) index set $\mathcal O\subseteq\{1,\dots,N\}$ with $|\mathcal O|\le \epsilon N$ and replace $\{Y_i:i\in\mathcal O\}$ by arbitrary vectors in $\mathbb R^d$ , producing observed data $X_1,\dots,X_N$ . An estimator is any measurable map $\hat\mu:(\mathbb R^d)^N\to\mathbb R^d$ . The squared-error minimax risk is

$
\mathcal R_N(\epsilon,K)
:=
\inf_{\hat\mu}
\sup_{\mu\in K}
\sup_{\text{adversaries }A:\,|\mathcal O_A|\le \epsilon N}
\mathbb E_{\mu,A}\!\left[\|\hat\mu(X_1,\dots,X_N)-\mu\|_2^2\right].
$

### Unsolved Problem

For multivariate constrained classes $K$ , determine the sharp asymptotic behavior of $\mathcal R_N(\epsilon,K)$ as $\epsilon\uparrow 1/2$ . In particular, obtain matching (up to universal constants, and ideally exact) upper and lower bounds that identify the correct dependence on the boundary parameter $1-2\epsilon$ , and characterize how this boundary dependence interacts with local metric-entropy geometry of $K$ (for example through covering numbers of localized sets $K\cap B_2(\mu,r)$ ).

See [Prasadan & Neykov (2024)](#references) , discussion around the boundary-contamination regime, for context.

## Significance & Implications

Open as of June 12, 2025: the cited work proves sharp rates under separation from the boundary ( $\epsilon\le 1/2-\kappa$ for fixed $\kappa>0$ ), but does not establish the sharp multivariate constrained behavior as $\epsilon\uparrow 1/2$ . Resolving this would pin down robustness limits near maximal contamination and clarify constrained-geometry effects in the hardest regime.

## Known Partial Results

The paper gives sharp rates for fixed separation from $1/2$ (i.e., $\epsilon\le 1/2-\kappa$ ). In discussion, the authors reference prior one-dimensional boundary-regime results and indicate possible extensions to multivariate constrained settings, but do not establish the sharp $1-2\epsilon$ boundary behavior for those classes.

## References

[1]

 [Information Theoretic Limits of Robust Sub-Gaussian Mean Estimation Under Star-Shaped Constraints](https://arxiv.org/abs/2412.03832v2) 

Akshay Prasadan, Matey Neykov (2025)

Annals of Statistics (to appear; as listed in arXiv v2 metadata)

📍 Problem context: Section 6 (Discussion and Future Work), paragraph beginning “We now comment on the i.i.d. Gaussian case…”, p. 27. Publication-status metadata (“Annals of Statistics, to appear”) is taken from the arXiv v2 abstract/metadata page.

Primary source where this open problem is discussed. Year convention: 2025 corresponds to the cited arXiv version (v2); initial posting was in 2024 (identifier 2412).

 [Link ↗](https://arxiv.org/abs/2412.03832v2) [arXiv ↗](https://arxiv.org/abs/2412.03832v2)

## Notes / Progress

_Work log goes here._
