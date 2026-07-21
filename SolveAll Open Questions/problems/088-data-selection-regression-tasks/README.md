# Data Selection for Regression Tasks

**Status:** Unsolved  
**Source:** Posed by Steve Hanneke et al. (2025)

## Categories

- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #88 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\mathcal{Z}=\mathcal{X}\times\mathbb{R}$ and let $P$ be an unknown distribution on $\mathcal{Z}$ . Draw a pooled dataset $S=((x_i,y_i))_{i=1}^N\sim P^N$ i.i.d. A (possibly randomized) selection rule $\mathrm{Sel}$ observes the entire labeled pool $S$ and outputs an index set $I=\mathrm{Sel}(S)\subseteq\{1,\ldots,N\}$ with $|I|=n$ (with $1\le n\le N$ ); write $S_I=((x_i,y_i))_{i\in I}$ for the selected sub-sample. Fix a learning rule $\mathcal{A}$ that maps any labeled sample to a predictor $\hat f=\mathcal{A}(\cdot):\mathcal{X}\to\mathbb{R}$ . Evaluate predictors by squared loss and population risk

$
\ell(f,(x,y))=(f(x)-y)^2,\qquad L_P(f)=\mathbb{E}_{(X,Y)\sim P}[(f(X)-Y)^2].
$

Fix a hypothesis class $\mathcal{F}\subseteq\{f:\mathcal{X}\to\mathbb{R}\}$ and a family of distributions $\mathcal{P}$ . Define the minimax excess risk (over $\mathcal{P}$ ) achievable by first selecting $n$ points from an i.i.d. pool of size $N$ and then running the fixed learner $\mathcal{A}$ :

$
\mathfrak{R}_{\mathcal{A}}(n,N;\mathcal{P})
:= \sup_{P\in\mathcal{P}}\ \inf_{\mathrm{Sel}}\ \mathbb{E}\Big[ L_P\big(\mathcal{A}(S_{\mathrm{Sel}(S)})\big) - \inf_{f\in\mathcal{F}} L_P(f) \Big],
$

where the expectation is over $S\sim P^N$ and any internal randomness of $\mathrm{Sel}$ (and of $\mathcal{A}$ , if randomized).

### Unsolved Problem

For natural fixed regression learning rules $\mathcal{A}$ , determine tight (up to constants and/or logarithmic factors) upper and lower bounds on $\mathfrak{R}_{\mathcal{A}}(n,N;\mathcal{P})$ as a function of $n$ and $N$ in basic regression settings, and characterize when selecting $n\ll N$ points can achieve excess risk comparable to using all $N$ points.

Two concrete testbeds emphasized in the COLT open-problem note are:

- Mean estimation: $\mathcal{X}$ is a singleton, $\mathcal{F}=\{f_\mu: f_\mu(x)\equiv \mu\}$ , and $\mathcal{A}$ returns the empirical mean on the selected labels, $\hat\mu=\frac{1}{n}\sum_{i\in I} y_i$ . For a moment-bounded family such as $\mathcal{P}=\{P: \mathbb{E}[Y^2]\le 1\}$ , determine the optimal rate of

$
\sup_{P\in\mathcal{P}}\ \inf_{\mathrm{Sel}}\ \mathbb{E}[(\hat\mu-\mathbb{E}Y)^2]
$

as a function of $n$ and $N$ .

- Linear regression: $\mathcal{X}\subseteq\mathbb{R}^d$ , $\mathcal{F}=\{x\mapsto\langle w,x\rangle: w\in\mathbb{R}^d\}$ , and $\mathcal{A}$ is a standard fixed rule such as ordinary least squares (squared-loss ERM) applied to $S_I$ . For a moment-bounded family such as $\mathcal{P}=\{P: \mathbb{E}[\|X\|_2^2]\le 1,\ \mathbb{E}[Y^2]\le 1\}$ , determine the optimal dependence of $\mathfrak{R}_{\mathcal{A}}(n,N;\mathcal{P})$ on $n,N,$ and $d$ , and identify regimes where $n\ll N$ suffices to match (up to constants/log factors) the excess risk achievable from the full pool.

## Significance & Implications

This problem isolates the algorithm-dependent limits of regression data curation: when the training rule $\mathcal{A}$ is fixed in advance, how much of the population-risk performance (measured by excess squared loss relative to $\inf_{f\in\mathcal{F}} L_P(f)$ ) can be preserved by selecting only $n$ labeled examples from an available i.i.d. pool of size $N$ ? Tight minimax characterizations of $\mathfrak{R}_{\mathcal{A}}(n,N;\mathcal{P})$ would precisely quantify when subset selection can be statistically near-lossless versus when it necessarily incurs a penalty, and would make explicit how this depends on the selection budget $n$ , pool size $N$ , and (for linear regression) dimension $d$ under concrete moment conditions.

## Known Partial Results

- The COLT 2025 open-problem note (Hanneke, Moran, Shlimovich, Yehudayoff, 2025) formulates the general data-selection question for regression with a fixed learning rule $\mathcal{A}$ and a selection budget $n$ from a pool of size $N$ , evaluated by population squared loss/excess risk.

- The note highlights mean estimation and linear regression as basic settings where one seeks tight (up to constants/log factors) upper and lower bounds on the best achievable excess risk when training $\mathcal{A}$ only on the selected sub-sample.

## References

[1]

 [Open Problem: Data Selection for Regression Tasks](https://proceedings.mlr.press/v291/hanneke25e.html) 

Steve Hanneke, Shay Moran, Alexander Shlimovich, Amir Yehudayoff (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v291/hanneke25e.html) [2]

 [Open Problem: Data Selection for Regression Tasks (PDF)](https://raw.githubusercontent.com/mlresearch/v291/main/assets/hanneke25e/hanneke25e.pdf) 

Steve Hanneke, Shay Moran, Alexander Shlimovich, Amir Yehudayoff (2025)

Conference on Learning Theory (COLT), PMLR 291

📍 Proceedings PDF.

 [Link ↗](https://raw.githubusercontent.com/mlresearch/v291/main/assets/hanneke25e/hanneke25e.pdf)

## Notes / Progress

_Work log goes here._
