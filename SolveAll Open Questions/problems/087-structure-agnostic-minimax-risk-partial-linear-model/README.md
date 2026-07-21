# Structure-Agnostic Minimax Risk for Partial Linear Model

**Status:** Partially Resolved  
**Source:** Posed by Yihong Gu (2025)

## Categories

- Learning Theory
- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #87 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(Y_i,T_i,X_i)_{i=1}^n$ be i.i.d., with $Y,T\in\mathbb{R}$ and $X$ taking values in a measurable space $\mathcal{X}$ . Assume the partial linear model

$
Y = \theta_0 T + f_0(X) + \epsilon,\qquad \mathbb{E}[\epsilon\mid X,T]=0,
$

where $\theta_0\in\mathbb{R}$ is the target and $f_0:\mathcal{X}\to\mathbb{R}$ is an unknown nuisance. Define

$
g_0(x):=\mathbb{E}[T\mid X=x],\qquad m_0(x):=\mathbb{E}[Y\mid X=x]=\theta_0 g_0(x)+f_0(x),
$

and the residualized treatment $U:=T-g_0(X)$ . Assume finite second moments and a nondegeneracy/conditioning bound

$
\mathbb{E}[Y^2]<\infty,\ \mathbb{E}[T^2]<\infty,\qquad 0<\sigma_{\mathrm{lower}}^2\le \mathbb{E}[U^2]\le \sigma_{\mathrm{upper}}^2<\infty.
$

A cross-fitted DML estimator is: split indices into folds; for each $i$ , fit nuisance predictors $\widehat m^{(-i)}$ and $\widehat g^{(-i)}$ using data excluding $i$ (or excluding $i$ 's fold), evaluate them at $X_i$ , and compute

$
\widehat\theta_{\mathrm{DML}}:=\frac{\sum_{i=1}^n (T_i-\widehat g^{(-i)}(X_i))(Y_i-\widehat m^{(-i)}(X_i))}{\sum_{i=1}^n (T_i-\widehat g^{(-i)}(X_i))^2}.
$

Structure-agnostic learnability assumption: there exist such cross-fitted predictors $(\widehat m^{(-i)},\widehat g^{(-i)})$ constructed from the $n$ samples for which, for an independent draw $X\sim P_X$ (independent of the training sample),

$
\mathbb{E}\big[(\widehat m(X)-m_0(X))^2\big]\le \delta_m^2,\qquad \mathbb{E}\big[(\widehat g(X)-g_0(X))^2\big]\le \delta_g^2,
$

where the expectation averages over the sample and any algorithmic randomness.

Let $\mathcal{P}_n(\delta_m,\delta_g;\sigma_{\mathrm{lower}},\sigma_{\mathrm{upper}})$ be the set of all distributions $P$ over $(Y,T,X)$ satisfying the model, the moment and $\mathbb{E}[U^2]$ bounds above, and for which there exist cross-fitted predictors achieving the stated $L_2(P_X)$ errors $(\delta_m,\delta_g)$ from $n$ samples. Define the structure-agnostic minimax mean-squared error

$
R^*(n,\delta_m,\delta_g;\sigma_{\mathrm{lower}},\sigma_{\mathrm{upper}}):=\inf_{\widehat\theta}\ \sup_{P\in\mathcal{P}_n(\delta_m,\delta_g;\sigma_{\mathrm{lower}},\sigma_{\mathrm{upper}})}\ \mathbb{E}_P\big[(\widehat\theta-\theta_0)^2\big],
$

where the infimum is over all estimators measurable w.r.t. the sample.

### Unsolved Problem

Characterize $R^*(n,\delta_m,\delta_g;\sigma_{\mathrm{lower}},\sigma_{\mathrm{upper}})$ sharply (up to universal constants and, if unavoidable, logarithmic factors) as a function of $(n,\delta_m,\delta_g,\sigma_{\mathrm{lower}},\sigma_{\mathrm{upper}})$ . In particular, determine whether $\widehat\theta_{\mathrm{DML}}$ attains the minimax rate uniformly over all regimes of $(\delta_m,\delta_g)$ under only the structure-agnostic learnability assumption; if not, determine the minimax rate and exhibit an estimator achieving it, clarifying how variance/conditioning through $U$ constrains what is achievable without additional structural assumptions on $m_0$ or $g_0$ .

## Significance & Implications

The problem asks for an information-theoretic benchmark for estimating the scalar coefficient $\theta_0$ in a partial linear model when the only quantitative control on nuisance learning is out-of-sample mean-squared prediction error bounds $(\delta_m,\delta_g)$ , with no smoothness/sparsity/parametric structure assumed. A sharp characterization of $R^*$ would pin down the best possible tradeoff between sample size, nuisance prediction accuracy, and treatment-residual conditioning $\mathbb{E}[U^2]$ , and would decide whether cross-fitted orthogonal/DML estimation is uniformly rate-optimal in this purely structure-agnostic regime. This directly impacts when black-box prediction guarantees alone justify the commonly used residualization-and-regression pipeline for semiparametric/causal effect estimation, versus when additional assumptions are necessary to control variance-driven limitations tied to the residualized treatment.

## Known Partial Results

- The orthogonal estimating equation underlying DML is first-order insensitive to nuisance errors, so analyses typically reduce MSE control for $\widehat\theta_{\mathrm{DML}}$ to bounding higher-order remainder terms involving the nuisance estimation errors.

- In many standard DML analyses, achieving $n^{-1/2}$ -type accuracy (or sharper bounds on $\mathbb{E}[(\widehat\theta-\theta_0)^2]$ ) requires product-rate conditions on nuisance estimation (informally, that the combined effect of $\widehat m-m_0$ and $\widehat g-g_0$ is small enough) together with nondegeneracy of the residualized treatment.

- The COLT 2025 note (Gu, 2025) highlights a specific gap for structure-agnostic minimax lower bounds in this model: existing techniques do not cleanly capture how variance/conditioning, as reflected by $U=T-\mathbb{E}[T\mid X]$ and its second moment bounds, may limit (or allow) improvements beyond generic DML rates, leaving the sharp minimax risk characterization open even for estimating $\theta_0$ .

- Jin, Mackey, and Syrgkanis (arXiv 2507.02275; NeurIPS 2025) show that DML is minimax-rate optimal for Gaussian treatment noise but suboptimal for independent non-Gaussian treatment noise, giving substantial partial resolution while leaving the fully general structure-agnostic characterization open.

## References

[1]

 [Open Problem: Structure-Agnostic Minimax Risk for Partial Linear Model](https://proceedings.mlr.press/v291/gu25b.html) 

Yihong Gu (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v291/gu25b.html) [2]

 [Open Problem: Structure-Agnostic Minimax Risk for Partial Linear Model (PDF)](https://raw.githubusercontent.com/mlresearch/v291/main/assets/gu25b/gu25b.pdf) 

Yihong Gu (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Proceedings PDF.

 [Link ↗](https://raw.githubusercontent.com/mlresearch/v291/main/assets/gu25b/gu25b.pdf) [3]

 [Root-N-Consistent Semiparametric Regression](https://doi.org/10.2307/1912705) 

Peter M. Robinson (1988)

Econometrica

📍 Classical partially linear model results (root-n estimation under regularity conditions).

 [Link ↗](https://doi.org/10.2307/1912705) [DOI ↗](https://doi.org/10.2307/1912705) [4]

 [Double/debiased machine learning for treatment and structural parameters](https://doi.org/10.1111/ectj.12097) 

Victor Chernozhukov, Denis Chetverikov, Mert Demirer, Esther Duflo, Christian Hansen, Whitney Newey, James Robins (2018)

The Econometrics Journal

📍 Canonical DML framework with orthogonal scores and cross-fitting.

 [Link ↗](https://doi.org/10.1111/ectj.12097) [DOI ↗](https://doi.org/10.1111/ectj.12097)

## Notes / Progress

_Work log goes here._
