# Sharp characterization of misspecification robustness for debiased GD inference

**Status:** Unsolved  
**Source:** Sourced from the work of Qiyang Han, Xiaocong Xu

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #61 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $Z_i=(X_i,Y_i)$ , $i=1,\dots,n$ , be i.i.d. observations from an unknown distribution $P$ on $\mathcal Z=\mathcal X\times\mathcal Y$ . Let $\Theta\subseteq\mathbb R^d$ be the parameter space, and let $\ell:\Theta\times\mathcal Z\to\mathbb R$ be a twice continuously differentiable loss in $\theta$ . Define the population and empirical risks by

$
L_P(\theta)=\mathbb E_P[\ell(\theta;Z)],\qquad L_n(\theta)=\frac1n\sum_{i=1}^n \ell(\theta;Z_i).
$

Assume the population minimizer

$
\theta_P^\star\in\arg\min_{\theta\in\Theta} L_P(\theta)
$

exists and is unique (possibly with $P$ outside the working model class used to motivate $\ell$ , i.e., misspecification is allowed).

Starting from $\theta^0\in\Theta$ , define gradient-descent iterates

$
\theta^{s+1}=\theta^s-\eta_s\nabla L_n(\theta^s),\qquad s=0,1,\dots,
$

with step sizes $\eta_s>0$ . For each iteration index $t$ , let $\widetilde\theta^t$ denote the debiased estimator constructed from past GD iterates $\{\theta^s\}_{s\le t}$ by the debiasing scheme of interest. For a fixed nonzero contrast vector $a\in\mathbb R^d$ , consider the studentized statistic

$
T_{n,t}(a)=\frac{a^\top(\widetilde\theta^t-\theta_P^\star)}{\widehat\sigma_t(a)},
$

where $\widehat\sigma_t(a)$ estimates the asymptotic standard deviation of $a^\top(\widetilde\theta^t-\theta_P^\star)$ .

### Unsolved Problem

Characterize, as sharply as possible, the class of misspecification regimes and loss/design structures under which asymptotically valid normal inference holds despite misspecification, e.g.

$
\sup_{0\le t\le T_n}\sup_{x\in\mathbb R}\left|\mathbb P_P\!\left(T_{n,t}(a)\le x\right)-\Phi(x)\right|\to0\quad\text{as }n\to\infty,
$

for each fixed $a$ , and to identify where this uniform asymptotic normality must fail.

## Significance & Implications

For arXiv:2412.09498v3, the misspecification-robustness wording is supported by the introduction discussion (not as an abstract quote): Section 1.4 (after Eq. (1.11)) points to robustness under limited misspecification and refers to Appendix C.2. The paper does not provide a sharp necessary-and-sufficient boundary for the maximal validity class.

## Known Partial Results

The paper proves debiased-GD inferential validity in its theorem-specific/model-specific framework and reports additional simulation evidence of robustness, but it does not establish a sharp maximal-class characterization of misspecification robustness. Status remains open.

## References

[1]

 [Gradient descent inference in empirical risk minimization](https://arxiv.org/abs/2412.09498v3) 

Qiyang Han, Xiaocong Xu (2024)

Annals of Statistics (to appear)

📍 arXiv:2412.09498v3, Section 1.4 (paragraph immediately after Eq. (1.11), misspecification-robustness discussion) and Appendix C.2 (simulation evidence under misspecification).

Primary source motivating this synthesized open direction.

 [Link ↗](https://arxiv.org/abs/2412.09498v3) [arXiv ↗](https://arxiv.org/abs/2412.09498v3)

## Notes / Progress

_Work log goes here._
