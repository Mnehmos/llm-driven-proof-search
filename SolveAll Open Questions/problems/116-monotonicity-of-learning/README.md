# Monotonicity of Learning

**Status:** Partially Resolved  
**Source:** Posed by Tom Viering et al. (2019)

## Categories

- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #116 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(Z,\mathcal{Z})$ be a measurable space and let $D$ be an unknown probability distribution on $Z$ . For each $n\in\mathbb{N}$ , let $S_n=(z_1,\dots,z_n)\sim D^n$ be an i.i.d. sample. Fix a hypothesis class $H$ and a measurable loss $L:H\times Z\to\mathbb{R}$ . Define the population (true) risk $L_D(h)=\mathbb{E}_{z\sim D}[L(h,z)]$ .

An empirical risk minimization (ERM) learner is a deterministic rule $A$ such that for every sample $S_n$ ,

$
A(S_n)\in\arg\min_{h\in H}\;\frac{1}{n}\sum_{i=1}^n L(h,z_i),
$

with a fixed tie-breaking rule so that $A(S_n)$ is single-valued.

Define the expected population risk at sample size $n$ by

$
R_n(D):=\mathbb{E}_{S_n\sim D^n}\big[L_D(A(S_n))\big].
$

(Here the expectations for $n$ and $n+1$ are over fresh i.i.d. samples from $D^n$ and $D^{n+1}$ , respectively.)

The learner $A$ is (locally) risk-monotone at $(D,n)$ if $R_{n+1}(D)\le R_n(D)$ . Call $A$ $Z$ -monotone if this inequality holds for all $n\in\mathbb{N}$ and all distributions $D$ on $Z$ . Call $A$ weakly $Z$ -monotone if there exists an integer $N$ (independent of $D$ ) such that $R_{n+1}(D)\le R_n(D)$ holds for all $n\ge N$ and all distributions $D$ on $Z$ .

For normal variance estimation, conditions for $Z$ -monotonicity have been established in [Sellke and Yin (2025)](#references) .

### Unsolved Problem

For ERM learners, determine conditions on $(Z,H,L)$ and/or on restrictions on $D$ (e.g., well-specification/realizability assumptions) that are sufficient and/or necessary for $Z$ -monotonicity or weak $Z$ -monotonicity.

In particular, resolve $Z$ -monotonicity and weak $Z$ -monotonicity (existence of such an $N$ , and if it exists, the smallest valid $N$ ) for univariate linear regression: $Z=X\times Y$ with $X\subseteq[-1,1]$ and $Y\subseteq[0,1]$ , $H=\{h_w(x)=wx:w\in\mathbb{R}\}$ , and $L(h_w,(x,y))=(wx-y)^2$ ; ERM minimizes empirical mean squared error over $w$ .

## Significance & Implications

This problem asks for distribution-free (or assumption-qualified) guarantees that the expected population risk of ERM does not increase when the sample size grows by one. Such a guarantee is strictly finer than standard generalization or PAC-style statements because it constrains the entire learning curve $n\mapsto R_n(D)$ , not just asymptotic consistency or rates. Pinning down when monotonicity holds (or must fail) clarifies when non-monotone learning curves are an unavoidable consequence of ERM + finite samples versus an artifact of modeling choices (loss, hypothesis class, tie-breaking) or missing distributional assumptions.

## Known Partial Results

- Viering, Mey, and Loog (2019) formalize expected risk monotonicity for learning algorithms, including the distribution-free notions of $Z$ -monotonicity and eventual (weak) $Z$ -monotonicity for ERM.

- The same note provides examples showing that risk monotonicity can hold in some ERM settings and fail in others, even when monotonicity is evaluated in expectation over the random training sample.

- The note relates risk monotonicity to PAC-learnability, emphasizing that standard learnability/generalization guarantees (which improve with $n$ in typical bounds) do not automatically imply that $R_{n+1}(D)\le R_n(D)$ for every $n$ and every $D$ .

## References

[1]

 [Open Problem: Monotonicity of Learning](https://proceedings.mlr.press/v99/viering19a.html) 

Tom Viering, Alexander Mey, Marco Loog (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v99/viering19a.html) [2]

 [Open Problem: Monotonicity of Learning (PDF)](http://proceedings.mlr.press/v99/viering19a/viering19a.pdf) 

Tom Viering, Alexander Mey, Marco Loog (2019)

Conference on Learning Theory (COLT), PMLR 99

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v99/viering19a/viering19a.pdf)

## Notes / Progress

_Work log goes here._
