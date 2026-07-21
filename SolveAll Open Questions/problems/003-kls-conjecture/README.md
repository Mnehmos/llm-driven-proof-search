# KLS Conjecture (Kannan-Lovasz-Simonovits)

**Status:** Unsolved  
**Importance:** Major
**Source:** Posed by Ravi Kannan, Laszlo Lovasz, Miklos Simonovits (1995)

## Categories

- Probability Theory
- Optimization & Variational Methods
- Analysis & PDEs

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #3 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

For each integer $n \ge 1$ , let $\mu$ be a Borel probability measure on $\mathbb{R}^n$ that is absolutely continuous with respect to Lebesgue measure, with density $f:\mathbb{R}^n \to [0,\infty)$ of the form $f(x)=e^{-V(x)}$ , where $V:\mathbb{R}^n\to(-\infty,\infty]$ is convex; equivalently, $\mu$ is log-concave. Assume $\mu$ is isotropic, meaning

$
\int_{\mathbb{R}^n} x\,d\mu(x)=0 \quad\text{and}\quad \int_{\mathbb{R}^n} x x^\top\, d\mu(x)=I_n,
$

where $I_n$ is the $n\times n$ identity matrix.

For a measurable set $A\subseteq\mathbb{R}^n$ , define its $\varepsilon$ -enlargement by $A_\varepsilon=\{x\in\mathbb{R}^n:\operatorname{dist}(x,A)\le \varepsilon\}$ and its Minkowski boundary measure (with respect to $\mu$ ) by

$
\mu^+(A)=\liminf_{\varepsilon\downarrow 0}\frac{\mu(A_\varepsilon)-\mu(A)}{\varepsilon}.
$

Define the Cheeger (isoperimetric) constant of $\mu$ as

$
\psi_\mu=\inf_{A\ \text{measurable},\ 0<\mu(A)<1}\frac{\mu^+(A)}{\min\{\mu(A),1-\mu(A)\}}.
$

### Unsolved Problem

(Kannan–Lovász–Simonovits conjecture; [Kannan et al. (1995)](#references) ) determine whether there exists a universal constant $c>0$ (independent of $n$ and of $\mu$ ) such that for every dimension $n$ and every isotropic log-concave probability measure $\mu$ on $\mathbb{R}^n$ ,

$
\psi_\mu \ge c.
$

Equivalently, if $C_n$ is the smallest number such that every isotropic log-concave $\mu$ on $\mathbb{R}^n$ satisfies

$
\mu^+(A)\ge \frac{1}{C_n}\min\{\mu(A),1-\mu(A)\}\quad\text{for all measurable }A\subseteq\mathbb{R}^n,
$

the conjecture is that $\sup_{n\ge1} C_n<\infty$ (that is, $C_n=O(1)$ as $n\to\infty$ ). [Eldan (2013)](#references) introduced the stochastic localization approach. The best known general bound is currently $C_n = O(\sqrt{\log n})$ , due to [Klartag (2023)](#references) .

## Significance & Implications

The KLS conjecture remains a central open problem in high-dimensional convex geometry and geometric functional analysis. It would yield a dimension-free Cheeger/Poincaré scale for isotropic log-concave measures, which in turn would sharpen conductance-based guarantees for log-concave sampling algorithms (under standard oracle-model assumptions) by removing current dimension-dependent isoperimetric losses.

Status of closely related problems has changed recently: Bourgain's slicing problem was resolved in 2025 ( [Klartag & Lehec (2025)](#references) ), while the thin-shell conjecture has a 2025 claimed resolution currently available as a preprint ( [Klartag & Lehec (2025)](#references) ).

## Known Partial Results

- [Lee & Vempala (2017)](#references) : proved $\psi_\mu \gtrsim n^{-1/4}$ (equivalently $C_n = O(n^{1/4})$ ), the first major improvement via stochastic localization.

- [Chen (2021)](#references) : improved to an almost-constant regime $\psi_\mu \ge n^{-o(1)}$ (equivalently $C_n = n^{o(1)}$ ), not yet polylogarithmic.

- [Klartag & Lehec (2022)](#references) : obtained a polylogarithmic bound, $C_n \le (\log n)^{O(1)}$ .

- [Klartag (2023)](#references) : improved this to $C_n = O(\sqrt{\log n})$ , the current best known general bound.

- The conjecture is still open in full generality (dimension-free $C_n=O(1)$ remains unproved).

## References

[1]

 [Isoperimetric problems for convex bodies and a localization lemma](https://doi.org/10.1007/BF02574061) 

Ravi Kannan, László Lovász, Miklós Simonovits (1995)

Discrete & Computational Geometry

📍 Section 5, unnumbered conjecture immediately preceding Theorem 5.4, p. 557 (Discrete & Computational Geometry 13 (1995), 541-559).

 [DOI ↗](https://doi.org/10.1007/BF02574061) [2]

 [Thin shell implies spectral gap up to polylog via a stochastic localization scheme](https://doi.org/10.1007/s00039-013-0214-y) 

Ronen Eldan (2013)

Geometric and Functional Analysis

📍 Section 1 (Introduction), Theorem 1.1 (thin-shell width controls Poincare constant up to polylog), p. 533.

 [DOI ↗](https://doi.org/10.1007/s00039-013-0214-y) [3]

 [Eldan's stochastic localization and the KLS hyperplane conjecture: An improved lower bound for expansion](https://doi.org/10.1109/FOCS.2017.96) 

Yin Tat Lee, Santosh S. Vempala (2017)

Proceedings of FOCS 2017

📍 Theorem 1.1 / Introduction: isoperimetric bound corresponding to $C_n = O(n^{1/4})$.

 [DOI ↗](https://doi.org/10.1109/FOCS.2017.96) [arXiv ↗](https://arxiv.org/abs/1612.01507) [4]

 [An almost constant lower bound of the isoperimetric coefficient in the KLS conjecture](https://doi.org/10.1007/s00039-021-00558-4) 

Yuansi Chen (2021)

Geometric and Functional Analysis

📍 Abstract and Theorem 1: improves $d^{-1/4}$-type dependence to $d^{-o_d(1)}$ (equivalently $C_n=n^{o(1)}$).

 [DOI ↗](https://doi.org/10.1007/s00039-021-00558-4) [arXiv ↗](https://arxiv.org/abs/2011.13661) [5]

 [Bourgain's slicing problem and KLS isoperimetry up to polylog](https://doi.org/10.1007/s00039-022-00612-9) 

Bo'az Klartag, Joseph Lehec (2022)

Geometric and Functional Analysis

📍 Abstract: KLS and slicing up to a polylogarithmic factor.

 [DOI ↗](https://doi.org/10.1007/s00039-022-00612-9) [arXiv ↗](https://arxiv.org/abs/2203.15551) [6]

 [Logarithmic bounds for isoperimetry and slices of convex sets](https://doi.org/10.15781/jsjy-0b06) 

Bo'az Klartag (2023)

Ars Inveniendi Analytica

📍 Abstract: KLS and slicing hold up to a $\sqrt{\log n}$ factor.

 [DOI ↗](https://doi.org/10.15781/jsjy-0b06) [arXiv ↗](https://arxiv.org/abs/2303.14938) [7]

 [Affirmative resolution of Bourgain's slicing problem using Guan's bound](https://doi.org/10.1007/s00039-025-00718-w) 

Boaz Klartag, Joseph Lehec (2025)

Geometric and Functional Analysis

📍 Abstract and Theorem 1.1: establishes the slicing conjecture with a universal constant.

 [DOI ↗](https://doi.org/10.1007/s00039-025-00718-w) [8]

 [Thin-shell bounds via parallel coupling](https://arxiv.org/abs/2507.15495) 

Boaz Klartag, Joseph Lehec (2025)

📍 Abstract: states a universal constant thin-shell bound and claims confirmation of the thin-shell conjecture.

 [arXiv ↗](https://arxiv.org/abs/2507.15495)

## Notes / Progress

_Work log goes here._
