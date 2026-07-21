# Does the score-matched optimal convex estimator attain the full semiparametric efficiency bound?

**Status:** Unsolved  
**Source:** Sourced from the work of Oliver Y. Feng, Yu-Chun Kao, Min Xu, Richard J. Samworth

## Categories

- Mathematical Statistics
- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #39 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $p\in\mathbb{N}$ be fixed. Observe i.i.d. pairs $(X_i,Y_i)_{i=1}^n$ from the linear model

$
Y_i=X_i^\top\beta_0+\varepsilon_i,
$

where $\beta_0\in\mathbb{R}^p$ , $X_i\in\mathbb{R}^p$ , $\varepsilon_i\perp X_i$ , and the conditional density is

$
y\mapsto p_0(y-x^\top\beta_0)
$

for unknown error density $p_0$ . Assume the regularity conditions in [Feng et al. (2024)](#references) guaranteeing root- $n$ asymptotic normality for convex $M$ -estimators.

For a convex loss $\rho$ , write $\psi=\rho'$ . Under this parameterization, convexity corresponds to monotonicity of $\psi$ ; equivalently, the source works with an antitone class $\Psi_\downarrow(p_0)$ after a sign convention. For $\psi\in\Psi_\downarrow(p_0)$ , define

$
V_{p_0}(\psi):=\frac{\int \psi^2\,dP_0}{\left(\int_{S_0} p_0\,d\psi\right)^2},
$

where $P_0$ is the law of $\varepsilon$ and $S_0=\{x:p_0(x)>0\}$ . Then regular convex $M$ -estimators satisfy

$
\sqrt n\,(\hat\beta_\psi-\beta_0)\Rightarrow N\!\bigl(0,\,V_{p_0}(\psi)\,\Sigma_X^{-1}\bigr),\qquad \Sigma_X:=\mathbb E[XX^\top].
$

The score-matching objective is

$
D_{p_0}(\psi):=\int \psi^2\,dP_0+2\int_{S_0} p_0\,d\psi,
$

and it is linked to asymptotic variance by

$
\inf_{c\ge 0}D_{p_0}(c\psi)=-\frac{1}{V_{p_0}(\psi)}.
$

Hence minimizing $D_{p_0}$ is equivalent to minimizing $V_{p_0}$ .

Population optimizer in the source: let $F_0$ be the CDF of $p_0$ , define density-quantile $J_0:=p_0\circ F_0^{-1}$ on $(0,1)$ , let $\widehat J_0$ be the least concave majorant of $J_0$ , and set

$
\psi_0^\star:=\widehat J_0^{(R)}\circ F_0,
$

where $\widehat J_0^{(R)}$ is the right derivative. This achieves

$
V_{p_0}(\psi_0^\star)=\inf_{\psi\in\Psi_\downarrow(p_0)}V_{p_0}(\psi).
$

Sample score-matching constructor for $\hat\beta_{\mathrm{cvx}}$ in [Feng et al. (2024)](#references) :

- 

Split the sample into folds and compute pilot estimator(s) on auxiliary folds.

- 

Form residuals from the pilot fit and estimate $p_0$ on each fold (kernel density estimate with truncation used in the source).

- 

Build a preliminary score estimate from the density estimate.

- 

Project this preliminary score onto the monotone cone (implemented via isotonic regression/PAVA in the source), then antisymmetrize in the symmetric-error construction.

- 

Define a convex loss by integrating the projected score:

$
\hat\ell_{n,j}^{\mathrm{sym}}(z)=-\int_0^z \hat\psi_{n,j}^{\mathrm{anti}}(t)\,dt.
$

- Compute fold-wise convex $M$ -estimators and cross-fit/average them to obtain $\hat\beta_{\mathrm{cvx}}$ .

Precise meaning of "asymptotically optimal within convex $M$ -estimators": for any regular convex $M$ -estimator $\tilde\beta$ in the same model class,

$
\operatorname{Avar}(\hat\beta_{\mathrm{cvx}})\preceq \operatorname{Avar}(\tilde\beta)
$

in Loewner order; equivalently, $V_{p_0}(\psi_0^\star)\le V_{p_0}(\psi)$ for all admissible convex-score choices $\psi$ , with equality only for positive scalar multiples of $\psi_0^\star$ .

### Unsolved Problem

Does this convex-class optimum already coincide with the full semiparametric efficiency bound for unknown $p_0$ ? Equivalently, can any regular estimator outside convex $M$ -estimation achieve strictly smaller asymptotic covariance?

## Significance & Implications

[Feng et al. (2024)](#references) establishes optimality only over convex $M\text{-estimators}$ (under its regularity assumptions). Resolving whether any regular estimator can improve on that benchmark would clarify whether convexity causes a fundamental efficiency gap in this semiparametric regression problem.

## Known Partial Results

Under the source assumptions, [Feng et al. (2024)](#references) proves that the score-projected estimator $\hat\beta_{\mathrm{cvx}}$ attains

$
\inf\{\operatorname{Avar}(\hat\beta_\psi):\hat\beta_\psi\ \text{is a regular convex }M\text{-estimator}\}
$

(in Loewner order, equivalently via minimizing the scalar factor $V_{p_0}(\psi)$ ). Equality characterization is up to positive rescaling of the optimal projected score. The paper also reports high relative efficiency (e.g., above $0.87$ for Cauchy errors) versus the oracle MLE with known error law, but this does not settle full semiparametric optimality over all regular estimators.

## References

[1]

 [Optimal Convex $M$-Estimation via Score Matching](https://arxiv.org/abs/2403.16688v2) 

Oliver Y. Feng, Yu-Chun Kao, Min Xu, Richard J. Samworth (2024)

Annals of Statistics (accepted; listed on Future Papers, final volume/issue/pages pending)

📍 arXiv v2: Section 3.4 (linear regression discussion), paragraph around Eq. (40) immediately before Theorem 14; publication-status metadata cross-checked against the Annals of Statistics Future Papers listing.

Primary source of the conjecture; Annals of Statistics publication is in the accepted/future-papers stage.

 [Link ↗](https://arxiv.org/abs/2403.16688v2) [arXiv ↗](https://arxiv.org/abs/2403.16688v2)

## Notes / Progress

_Work log goes here._
