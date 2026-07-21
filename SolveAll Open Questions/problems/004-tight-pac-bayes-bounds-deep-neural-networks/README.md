# Tight PAC-Bayes Bounds for Deep Neural Networks

**Status:** Unsolved  
**Importance:** Major

## Categories

- Learning Theory
- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #4 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Setup: Let $\mathcal{X}$ be an input space, let $\mathcal{Y}=\{1,\dots,C\}$ be a finite label set, and let $\mathcal{D}$ be an unknown distribution on $\mathcal{X}\times\mathcal{Y}$ . Draw an i.i.d. training sample $S=((x_1,y_1),\dots,(x_n,y_n))\sim\mathcal{D}^n$ . Fix a deep neural-network architecture with parameters $\theta\in\mathbb{R}^p$ (typically $p\gg n$ ), classifier $h_\theta:\mathcal{X}\to\mathcal{Y}$ , and bounded loss $\ell:\mathcal{Y}\times\mathcal{Y}\to[0,1]$ (especially $0$ - $1$ loss). Define

$
L_{\mathcal D}(h_\theta)=\mathbb E_{(x,y)\sim\mathcal D}[\ell(h_\theta(x),y)],
\qquad
\hat L_S(h_\theta)=\frac1n\sum_{i=1}^n\ell(h_\theta(x_i),y_i).
$

For a posterior distribution $Q$ over parameters (the Gibbs predictor) and a prior $P$ independent of $S$ , define

$
L_{\mathcal D}(Q):=\mathbb E_{\theta\sim Q}[L_{\mathcal D}(h_\theta)],
\qquad
\hat L_S(Q):=\mathbb E_{\theta\sim Q}[\hat L_S(h_\theta)].
$

A common PAC-Bayes form for bounded losses is

$
\mathrm{kl}(\hat L_S(Q)\,\|\,L_{\mathcal D}(Q))
\le
\frac{\mathrm{KL}(Q\|P)+\ln\!\big((2\sqrt n)/\delta\big)}{n},
$

which yields an explicit risk certificate after inverting binary KL. Foundational sources are [Shawe-Taylor & Williamson (1997)](#references) , [McAllester (1998)](#references) , [McAllester (1999)](#references) , and [McAllester (2003)](#references) ; see [Guedj (2019)](#references) for an overview.

### Unsolved Problem

Determine whether there exists a PAC-Bayes pipeline (choice of prior/posterior family, optimization procedure, and certificate computation) that simultaneously satisfies all three goals below for modern deep-learning practice:

- 

Non-vacuity at realistic scale: on standard trained high-capacity models (including ImageNet-scale settings), certify $0$ - $1$ upper bounds $B(S,\delta)<1$ with confidence $1-\delta$ .

- 

Polynomial-time certifiability: compute the bound (including optimization/selection of $Q$ and numerical certification of all terms) in time polynomial in natural parameters such as $n$ , $p$ , and $\log(1/\delta)$ .

- 

Predictive tightness across choices: over a family of training pipelines or hyperparameters $\Lambda$ , the values $\{B_\lambda(S,\delta):\lambda\in\Lambda\}$ should strongly track true test risks (for example, high rank correlation), not merely be non-vacuous.

As of March 10, 2026, major partial progress exists, including non-vacuous deep-network certificates [Dziugaite & Roy (2017)](#references) , ImageNet-scale compression/PAC-Bayes guarantees [Zhou et al. (2019)](#references) , tighter compression certificates [Lotfi et al. (2022)](#references) , and recent large-scale preprints [Than & Phan (2025)](#references) . A single broadly applicable framework meeting all three goals remains open.

## Significance & Implications

Understanding why deep neural networks generalize despite massive overparameterization is one of the central mysteries of modern machine learning theory. Classical bounds (VC dimension, Rademacher complexity) are typically vacuous for practical networks. PAC-Bayes and compression-based analyses provide some of the strongest available guarantees, but obtaining broadly tight, computationally practical, and consistently informative bounds for modern large-scale pipelines remains open.

## Known Partial Results

- [Dziugaite & Roy (2017)](#references) : first explicit non-vacuous PAC-Bayes certificates for deep stochastic networks in the modern overparameterized regime (MNIST-scale data, millions of parameters).

- [Perez-Ortiz et al. (2021)](#references) : tighter PAC-Bayes risk certificates on MNIST/CIFAR-10 for deep fully connected/CNN settings.

- [Arora et al. (2018)](#references) : stronger compression-based bounds, highlighting compression as a route to much tighter guarantees.

- [Zhou et al. (2019)](#references) : non-vacuous ImageNet-scale guarantees via PAC-Bayesian compression.

- [Lotfi et al. (2022)](#references) : substantially tighter compression/PAC-Bayes certificates, in some cases close to observed test error.

- [Than & Phan (2025)](#references) : recent large-scale preprint claims with randomly pretrained networks and improved certificates.

- Despite these advances, a single broadly applicable, polynomial-time, and consistently hyperparameter-predictive PAC-Bayes framework for modern deep pipelines is still not established.

## References

[1]

 [A PAC Analysis of a Bayesian Estimator](https://doi.org/10.1145/267460.267531) 

John Shawe-Taylor, Robert C. Williamson (1997)

COLT

📍 Original late-1990s PAC-style Bayesian analysis that introduced key ingredients later used in PAC-Bayes.

 [DOI ↗](https://doi.org/10.1145/267460.267531) [2]

 [Computing nonvacuous generalization bounds for deep (stochastic) neural networks with many more parameters than training data](https://arxiv.org/abs/1703.11008) 

Gintare Karolina Dziugaite, Daniel M. Roy (2017)

UAI

📍 Section 7 (Conclusion and Future Work), discussion of bound-tightening directions and scalability limits.

 [arXiv ↗](https://arxiv.org/abs/1703.11008) [3]

 [PAC-Bayesian stochastic model selection](https://doi.org/10.1023/A:1021840411064) 

David McAllester (2003)

Machine Learning

📍 Section 2 (summary of main results), including the core KL-based PAC-Bayes theorem.

 [DOI ↗](https://doi.org/10.1023/A:1021840411064) [4]

 [A Primer on PAC-Bayesian Learning](https://arxiv.org/abs/1901.05353) 

Benjamin Guedj (2019)

📍 Sections 1-2 for historical overview and later discussion for open directions on tightness/scalability.

 [arXiv ↗](https://arxiv.org/abs/1901.05353) [5]

 [Some PAC-Bayesian Theorems](https://doi.org/10.1145/279943.279989) 

David A. McAllester (1998)

COLT

📍 Foundational COLT-era PAC-Bayesian theorem statements.

 [DOI ↗](https://doi.org/10.1145/279943.279989) [6]

 [PAC-Bayesian Model Averaging](https://doi.org/10.1145/307400.307435) 

David A. McAllester (1999)

COLT

📍 Model-averaging PAC-Bayesian bound development in the main theorem/results sections.

 [DOI ↗](https://doi.org/10.1145/307400.307435) [7]

 [Stronger generalization bounds for deep nets via a compression approach](https://arxiv.org/abs/1802.05296) 

Sanjeev Arora, Rong Ge, Behnam Neyshabur, Yi Zhang (2018)

ICML

📍 Compression-based bound refinements yielding tighter guarantees than earlier compression analyses.

 [arXiv ↗](https://arxiv.org/abs/1802.05296) [8]

 [Non-vacuous Generalization Bounds at the ImageNet Scale: a PAC-Bayesian Compression Approach](https://arxiv.org/abs/1804.05862) 

Wenda Zhou, Victor Veitch, Morgane Austern, Ryan P. Adams, Peter Orbanz (2019)

ICLR

📍 Main theorem plus ImageNet experiments reporting explicit non-vacuous compression-based PAC-Bayes guarantees.

 [arXiv ↗](https://arxiv.org/abs/1804.05862) [9]

 [PAC-Bayes Compression Bounds So Tight That They Can Explain Generalization](https://arxiv.org/abs/2211.13609) 

Sina Lotfi, Marc Finzi, Sanyam Kapoor, Yair Carmon, Andrew Gordon Wilson (2022)

NeurIPS

📍 Main compression/PAC-Bayes theorem and empirical risk-certificate comparisons in modern neural-net settings.

 [arXiv ↗](https://arxiv.org/abs/2211.13609) [10]

 [Certifying Deep Network Risks with PAC-Bayes Bounds and Randomly Pretrained Neural Networks](https://arxiv.org/abs/2503.07325) 

Khoat Than, Dat Phan (2025)

📍 Abstract and experimental sections reporting recent large-scale PAC-Bayes certificates.

 [arXiv ↗](https://arxiv.org/abs/2503.07325)

## Notes / Progress

_Work log goes here._
