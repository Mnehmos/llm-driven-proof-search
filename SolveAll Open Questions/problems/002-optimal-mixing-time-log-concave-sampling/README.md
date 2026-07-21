# Optimal Mixing Time for Log-Concave Sampling

**Status:** Unsolved  
**Importance:** Major

## Categories

- Mathematical Statistics
- Probability Theory
- Optimization & Variational Methods

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #2 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $n \ge 1$ , let $V:\mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable, and define the target probability measure

$
\pi(dx)=\frac{1}{Z}e^{-V(x)}\,dx,\qquad Z=\int_{\mathbb{R}^n}e^{-V(x)}dx<\infty.
$

Assume $V$ is $\mu$ -strongly convex and $L$ -smooth, meaning

$
\mu I_n \preceq \nabla^2 V(x)\preceq L I_n\quad\text{for all }x\in\mathbb{R}^n,
$

with condition number $\kappa:=L/\mu$ . For $\varepsilon\in(0,1)$ , define total-variation mixing time of a Markov process $(X_t)$ with invariant law $\pi$ by

$
t_{\mathrm{mix}}(\varepsilon):=\inf\Big\{t\ge 0:\sup_{x\in\mathbb{R}^n}\| \mathcal{L}(X_t\mid X_0=x)-\pi\|_{\mathrm{TV}}\le \varepsilon\Big\}.
$

The study of MCMC mixing for log-concave targets goes back to [Dyer et al. (1991)](#references) ; non-asymptotic guarantees for the (overdamped) Langevin algorithm were obtained by [Dalalyan (2017)](#references) . For the underdamped Langevin diffusion on $(X_t,V_t)\in\mathbb{R}^n\times\mathbb{R}^n$ ,

$
dX_t=V_t\,dt,\qquad dV_t=-\gamma V_t\,dt-\nabla V(X_t)\,dt+\sqrt{2\gamma}\,dB_t,
$

where $\gamma>0$ and $(B_t)$ is standard $n$ -dimensional Brownian motion, the invariant law on phase space is proportional to $e^{-V(x)-\|v\|^2/2}$ , whose $x$ -marginal is $\pi$ .

### Unsolved Problem

Determine the optimal worst-case dependence on $(n,\kappa,\varepsilon)$ of the mixing time (or, for time-discretizations such as Langevin Monte Carlo, the number of gradient evaluations) needed to obtain $\varepsilon$ -accuracy in total variation for sampling from this class of targets. In particular, is it possible to achieve, up to polylogarithmic factors,

$
t_{\mathrm{mix}}(\varepsilon)\lesssim \sqrt{\kappa}\,n^{1/2}\,\log(1/\varepsilon)
$

for general strongly log-concave targets? Existing lower bounds are metric- and model-dependent (continuous-time diffusion vs discretized chains), so precise matching minimax TV scaling remains unresolved. See also [Chen et al. (2022)](#references) and the closely related [KLS conjecture](/problem/kls-conjecture) .

## Significance & Implications

Sampling from log-concave distributions is a fundamental primitive in statistics, machine learning, and Bayesian inference. A sharp complexity theory should distinguish clearly between (i) continuous-time diffusion contraction rates, (ii) discretization error, and (iii) the chosen metric (TV, KL, or $W_2$ ). For example, [Vempala & Wibisono (2019)](#references) analyze discretized overdamped Langevin (ULA) in KL/Renyi-type divergences under functional-inequality assumptions (with linear condition-number dependence in their regime, up to logarithmic factors and bias terms), while [Cheng et al. (2018)](#references) give non-asymptotic bounds for a discretized underdamped method in $W_2$ (not TV). This problem asks for the optimal TV complexity dependence on $(n,\kappa,\varepsilon)$ , which is still unresolved.

## Known Partial Results

- Overdamped Langevin: distinguish diffusion vs discretization. Continuous-time diffusion has exponential convergence under strong log-concavity/LSI (typically shown in KL or $W_2$ ), while discretized ULA bounds such as [Vempala & Wibisono (2019)](#references) are stated in divergence metrics (KL/Renyi-type) and include discretization-bias considerations.

- Underdamped Langevin (discretized): [Cheng et al. (2018)](#references) provide non-asymptotic guarantees in $W_2$ ; their headline bound is for $W_2$ accuracy, not TV.

- [Chen et al. (2022)](#references) explicitly notes an open discretization-analysis gap (at the time) for obtaining linear condition-number dependence under $\alpha$ -LSI/ $\alpha$ -PI.

- The [KLS conjecture](/problem/kls-conjecture) is widely expected to improve dimension dependence for isotropic log-concave sampling/mixing bounds, but the exact implied exponent and algorithm/metric dependence should be stated with theorem-specific citations when used.

- Status: open.

## References

[1]

 [Improved analysis for a proximal algorithm for sampling](https://proceedings.mlr.press/v178/chen22c.html) 

Yongxin Chen, Sinho Chewi, Adil Salim, Andre Wibisono (2022)

Proceedings of Thirty Fifth Conference on Learning Theory (PMLR 178)

📍 Section 4.2 (Applications), numbered list item 2, p. 8 (PMLR PDF): discussion that linear-in-condition-number discretization analysis for Langevin under $\alpha$-LSI/$\alpha$-PI was not known at that time.

 [Link ↗](https://proceedings.mlr.press/v178/chen22c.html) [arXiv ↗](https://arxiv.org/abs/2202.06386) [2]

 [Rapid Convergence of the Unadjusted Langevin Algorithm: Isoperimetry Suffices](https://arxiv.org/abs/1903.08568) 

Santosh Vempala, Andre Wibisono (2019)

 [arXiv ↗](https://arxiv.org/abs/1903.08568) [3]

 [Underdamped Langevin MCMC: A non-asymptotic analysis](https://arxiv.org/abs/1707.03663) 

Xiang Cheng, Niladri S. Chatterji, Peter L. Bartlett, Michael I. Jordan (2018)

 [arXiv ↗](https://arxiv.org/abs/1707.03663) [4]

 [A random polynomial-time algorithm for approximating the volume of convex bodies](https://doi.org/10.1145/102782.102783) 

Martin Dyer, Alan Frieze, Ravi Kannan (1991)

Journal of the ACM

📍 Section 3 (Random walks on convex bodies), Theorem 3.1 (rapid mixing of the ball walk via conductance), pp. 8-10.

 [DOI ↗](https://doi.org/10.1145/102782.102783) [5]

 [Theoretical guarantees for approximate sampling from smooth and log-concave density](https://doi.org/10.1111/rssb.12183) 

Arnak S. Dalalyan (2017)

Journal of the Royal Statistical Society Series B

📍 Section 3 (Main results), Theorem 1 (non-asymptotic convergence bound for unadjusted Langevin algorithm in TV distance), p. 658.

 [DOI ↗](https://doi.org/10.1111/rssb.12183)

## Notes / Progress

_Work log goes here._
