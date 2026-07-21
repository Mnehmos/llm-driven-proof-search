# Learning sparse linear concepts by priming the features

**Status:** Unsolved  
**Source:** Posed by Manfred K. Warmuth et al. (2023)

## Categories

- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #100 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Online linear regression with squared loss in dimension $n$ . For rounds $t=1,2,\dots,T$ : the learner observes $x_t\in\mathbb{R}^n$ , predicts $\hat y_t=\langle w_t,x_t\rangle$ , then observes $y_t\in\mathbb{R}$ and incurs loss $\ell_t(w_t)=(\hat y_t-y_t)^2$ . Assume coordinatewise bounded instances $\|x_t\|_\infty\le X$ and bounded outcomes $|y_t|\le Y$ for all $t$ .

Let $X_{t-1}\in\mathbb{R}^{(t-1)\times n}$ be the design matrix with rows $x_1^\top,\dots,x_{t-1}^\top$ and $y_{t-1}=(y_1,\dots,y_{t-1})^\top$ . For a matrix $A$ , let $A^\dagger$ denote the Moore-Penrose pseudoinverse, and for $p\in\mathbb{R}^n$ let $\mathrm{diag}(p)$ be the diagonal matrix with $p$ on the diagonal.

A one-stage feature-priming least-squares predictor is specified by a closed-form rule that maps past data to a priming vector $p_{t-1}=p(X_{t-1},y_{t-1})\in\mathbb{R}^n$ , forms primed design $X'_{t-1}:=X_{t-1}\,\mathrm{diag}(p_{t-1})$ , computes primed least-squares coefficients $v_{t-1}:=(X'_{t-1})^\dagger y_{t-1}$ , and sets

$
w_t := \mathrm{diag}(p_{t-1})\,v_{t-1} = \mathrm{diag}(p_{t-1})\,(X_{t-1}\,\mathrm{diag}(p_{t-1}))^\dagger y_{t-1}.
$

The COLT 2023 note highlights concrete closed-form priming rules motivated by sparsity, including (i) per-coordinate 1D least squares $p_{t-1,i}:=\langle X_{t-1}(:,i),y_{t-1}\rangle/\|X_{t-1}(:,i)\|_2^2$ when $\|X_{t-1}(:,i)\|_2\neq 0$ (and e.g. $0$ otherwise), (ii) correlation-style scores between column $i$ and $y_{t-1}$ , and (iii) the two-pass rule $p_{t-1}:=w^{\mathrm{LLS}}_{t-1}$ where $w^{\mathrm{LLS}}_{t-1}:=X_{t-1}^\dagger y_{t-1}$ is the minimum-norm least-squares fit on unprimed features.

### Unsolved Problem

For at least one of these priming rules, does the resulting online algorithm satisfy a regret bound with only logarithmic dependence on $n$ against sparse (or $\ell_1$ -bounded) linear comparators? Namely, is there a bound of the form

$
\mathrm{Regret}_T := \sum_{t=1}^T (\langle w_t,x_t\rangle-y_t)^2 - \min_{\|w\|_1\le W_1}\sum_{t=1}^T (\langle w,x_t\rangle-y_t)^2 \le \mathrm{poly}(W_1,X,Y)\cdot \log n
$

(or more finely $\le \mathrm{poly}(W_1,X,Y)\cdot k\log(n/k)$ when competing with $k$ -sparse comparators), uniformly over all sequences with $\|x_t\|_\infty\le X$ and $|y_t|\le Y$ ? The question remains open even in noise-free realizable settings $y_t=\langle w^*,x_t\rangle$ with sparse $w^*$ .

## Significance & Implications

For squared-loss online prediction, multiplicative-update methods can exploit sparsity to obtain regret bounds whose dimension dependence is logarithmic in $n$ under $\ell_1$ / $\ell_\infty$ type conditions, but their updates are not least-squares closed forms. In contrast, least-squares-style (Euclidean/second-order) updates are closed-form but typically do not yield sparsity-adaptive dimension dependence. Feature priming is a concrete, computationally simple way to bias a second least-squares fit toward a small set of coordinates using only the past data. Proving (or refuting) a worst-case $\log n$ -type regret guarantee for such priming would clarify whether closed-form least-squares predictors can match sparsity-adaptive guarantees without switching to multiplicative updates, and would delineate the limits of coordinate-sensitive preconditioning schemes in online regression.

## Known Partial Results

- The COLT 2023 note observes that sparse linear problems are learned well by online multiplicative updates, motivating the search for closed-form least-squares-style alternatives.

- The proposed priming family is fully specified by closed-form functions of past data followed by pseudoinverse least squares on a diagonally rescaled (coordinate-primed) design.

- Experiments reported in the note indicate that several priming rules (notably using $p_{t-1}=X_{t-1}^\dagger y_{t-1}$ and variants such as per-feature 1D least squares or correlation-based scores) can identify sparse relevant features faster than vanilla least squares while behaving similarly to least squares on dense targets.

- No worst-case online regret bound is currently given for these priming-based closed-form updates, and the existence of sparsity-adaptive (e.g., $\log n$ or $k\log(n/k)$ ) regret bounds remains open.

## References

[1]

 [Open Problem: Learning sparse linear concepts by priming the features](https://proceedings.mlr.press/v195/warmuth23a.html) 

Manfred K. Warmuth, Ehsan Amid (2023)

Conference on Learning Theory (COLT), PMLR 195

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v195/warmuth23a.html) [2]

 [Open Problem: Learning sparse linear concepts by priming the features (PDF)](https://proceedings.mlr.press/v195/warmuth23a/warmuth23a.pdf) 

Manfred K. Warmuth, Ehsan Amid (2023)

Conference on Learning Theory (COLT), PMLR 195

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v195/warmuth23a/warmuth23a.pdf)

## Notes / Progress

_Work log goes here._
