# Tight Online Confidence Intervals for RKHS Elements

**Status:** Unsolved  
**Source:** Posed by Sattar Vakili et al. (2021)

## Categories

- Learning Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #109 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $(\mathcal X,k)$ be a nonempty set with a positive semidefinite kernel $k:\mathcal X\times\mathcal X\to\mathbb R$ , and let $\mathcal H_k$ be the associated RKHS with norm $\|\cdot\|_{\mathcal H_k}$ . Assume the diagonal is bounded: $\kappa^2:=\sup_{x\in\mathcal X} k(x,x)<\infty$ . An unknown target function $f\in\mathcal H_k$ satisfies $\|f\|_{\mathcal H_k}\le B$ .

An online algorithm interacts for rounds $t=1,2,\dots$ . Let $\mathcal F_t:=\sigma(x_1,y_1,\dots,x_t,y_t)$ . At round $t$ , the algorithm chooses $x_t\in\mathcal X$ that is $\mathcal F_{t-1}$ -measurable and observes

$
y_t=f(x_t)+\eta_t,
$

where $(\eta_t)$ is conditionally mean-zero and $R$ -sub-Gaussian: for all $\lambda\in\mathbb R$ ,

$
\mathbb E\big[\exp(\lambda\eta_t)\mid \mathcal F_{t-1}\big]\le \exp\Big(\tfrac{\lambda^2R^2}{2}\Big).
$

Given data up to time $t$ and regularization $\lambda>0$ , define the kernel ridge regression estimator

$
\hat f_t\in\arg\min_{g\in\mathcal H_k}\ \sum_{s=1}^t (y_s-g(x_s))^2+\lambda\|g\|_{\mathcal H_k}^2.
$

Let $K_t\in\mathbb R^{t\times t}$ with $(K_t)_{ij}=k(x_i,x_j)$ , let $y_{1:t}=(y_1,\dots,y_t)^\top$ , and for $x\in\mathcal X$ let $k_t(x)=(k(x_1,x),\dots,k(x_t,x))^\top$ . By the representer theorem, one may take

$
\hat f_t(x)=k_t(x)^\top (K_t+\lambda I)^{-1}y_{1:t}.
$

Define the associated (regularized) predictive standard deviation proxy

$
s_t(x)=\sqrt{k(x,x)-k_t(x)^\top (K_t+\lambda I)^{-1}k_t(x)}.
$

### Unsolved Problem

Characterize, up to the correct order and with explicit dependence on $B,R,\lambda,\delta$ , and suitable kernel-complexity quantities, the smallest achievable sequence $(\beta_t)_{t\ge 1}$ such that for every (possibly adaptive) sampling rule $(x_t)$ ,

$
\mathbb P\Big(\forall t\ge 1,\ \forall x\in\mathcal X:\ |f(x)-\hat f_t(x)|\le \beta_t\, s_t(x)\Big)\ge 1-\delta.
$

In particular, determine whether the existing sequential (adaptive-design) RKHS confidence bounds used in kernelized bandits/RL can be substantially tightened, or whether their time/kernel-complexity dependence is information-theoretically necessary for uniform-in- $(t,x)$ guarantees.

## Significance & Implications

Uniform-in-time, high-probability bounds of the form $|f(x)-\hat f_t(x)|\le \beta_t s_t(x)$ are the key step that turns kernel regression error control into exploration guarantees in kernelized bandits and reinforcement learning. If $\beta_t$ is overly conservative in the adaptive (online) design setting, regret analyses inherit this looseness and may fail to certify sublinear regret for standard kernelized algorithms. Tight characterizations of the best possible online $\beta_t$ would therefore (i) sharpen regret guarantees when possible and (ii) clarify whether currently weak bounds arise from analysis artifacts or from a genuine limitation of existing algorithms under adaptive sampling.

## Known Partial Results

- The COLT 2021 open-problem note isolates the difficulty of constructing confidence sequences for RKHS-valued estimation when the design points $x_t$ are chosen sequentially based on past observations.

- The note surveys confidence bounds currently used in analyses of kernelized bandit and RL methods and argues that their resulting confidence widths can be overly loose in the online/adaptive setting.

- A key obstacle emphasized is that standard (non-adaptive or fixed-design) concentration arguments do not directly yield uniform-in-time guarantees when $x_t$ depends on past noise.

- The note highlights that, with current tools, regret analyses for algorithms such as GP-UCB and GP-TS can become too weak to even prove sublinear regret in general, motivating tighter online RKHS confidence intervals.

## References

[1]

 [Open Problem: Tight Online Confidence Intervals for RKHS Elements](https://proceedings.mlr.press/v134/open-problem-vakili21a.html) 

Sattar Vakili, Jonathan Scarlett, Tara Javidi (2021)

Conference on Learning Theory (COLT), PMLR 134

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v134/open-problem-vakili21a.html) [2]

 [Open Problem: Tight Online Confidence Intervals for RKHS Elements (PDF)](http://proceedings.mlr.press/v134/vakili21a/vakili21a.pdf) 

Sattar Vakili, Jonathan Scarlett, Tara Javidi (2021)

Conference on Learning Theory (COLT), PMLR 134

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v134/vakili21a/vakili21a.pdf) [3]

 [On Kernelized Multi-armed Bandits](https://proceedings.mlr.press/v70/chowdhury17a.html) 

Sayak Ray Chowdhury, Aditya Gopalan (2017)

International Conference on Machine Learning (ICML), PMLR 70

📍 Representative kernel bandit analysis relying on RKHS confidence bounds under sequentially chosen points.

 [Link ↗](https://proceedings.mlr.press/v70/chowdhury17a.html)

## Notes / Progress

_Work log goes here._
