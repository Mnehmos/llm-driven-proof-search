# Improper learning of mixtures of Gaussians

**Status:** Unsolved  
**Source:** Posed by Elad Hazan et al. (2018)

## Categories

- Learning Theory
- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #119 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix integers $d\ge 1$ and $k\ge 2$ , an accuracy parameter $\epsilon\in(0,1)$ , and a radius $R>0$ . Let $X:=\{x\in\mathbb{R}^d:\|x\|_2\le R\}$ , and let $D$ be an unknown distribution supported on $X$ (in particular, the motivating case is when $D$ is an overcomplete mixture of $k$ Gaussians with $k>d$ ).

A (deterministic) $b$ -bit pointwise compression scheme is a pair $(f,\rho)$ with encoder $f:X\to\{0,1\}^b$ and decoder $\rho:\{0,1\}^b\to\mathbb{R}^d$ . Its squared reconstruction error on $D$ is

$
\mathcal{R}_D(f,\rho):=\mathbb{E}_{x\sim D}\,\|\rho(f(x))-x\|_2^2.
$

Define the (spherical) $k$ -center quantization class $\mathcal{F}_k$ as follows: for any codebook (centers) $\mu_1,\dots,\mu_k\in X$ , the encoder outputs an index $i(x)\in\arg\min_{i\in[k]}\|x-\mu_i\|_2^2$ (ties broken arbitrarily), represented using $b:=\lceil\log_2 k\rceil$ bits, and the decoder outputs $\mu_{i(x)}$ . The optimal $k$ -center distortion is

$
\mathrm{OPT}_k(D):=\inf_{(f,\rho)\in\mathcal{F}_k}\mathcal{R}_D(f,\rho)=\inf_{\mu_1,\dots,\mu_k\in X}\mathbb{E}_{x\sim D}\Big[\min_{i\in[k]}\|x-\mu_i\|_2^2\Big].
$

An (improper) compression-based learner is an algorithm $A$ that, given $m$ i.i.d. samples from $D$ , outputs a (not necessarily $k$ -center) compression scheme $(g,\rho_g)$ with code length $b'=b'(k,\epsilon)$ such that, with probability at least $2/3$ over the samples,

$
\mathcal{R}_D(g,\rho_g)\le \mathrm{OPT}_k(D)+\epsilon.
$

### Unsolved Problem

 **Problem 2018.** In the overcomplete regime $k>d$ , does there exist a computationally efficient (polynomial-time in $d,k,1/\epsilon$ and the sample size) improper learner achieving the above guarantee while using only

$
b'(k,\epsilon)=\mathrm{poly}(\log k,\log(1/\epsilon))
$

bits per point (i.e., with no polynomial dependence on $d$ in the code length)? Alternatively, can one prove that no such efficient learner exists under this worst-case, compression-based notion of learning?

## Significance & Implications

This problem asks whether allowing improper reconstructions (arbitrary decoders/encoders learned from data) can yield a worst-case additive- $\epsilon$ competitor to the optimal $k$ -center distortion while keeping the per-point description length near $\log k$ (up to polylog factors), even when $k>d$ . A positive result would formalize an efficient, sample-based route to near-optimal quantization error for distributions such as overcomplete Gaussian mixtures without committing to a generative/proper mixture model. A negative result would isolate a concrete barrier showing that, even after relaxing to improper compression schemes, achieving $\mathrm{OPT}_k(D)+\epsilon$ with only polylogarithmic bits is computationally out of reach in the overcomplete setting.

## Known Partial Results

- The COLT 2018 open-problem note motivates the question from unsupervised learning of (overcomplete) mixtures of Gaussians, and explicitly switches to a worst-case, compression-based objective to allow improper learners.

- The benchmark objective $\mathrm{OPT}_k(D)=\inf_{\mu_1,\dots,\mu_k}\mathbb{E}[\min_i\|x-\mu_i\|_2^2]$ is the population $k$ -means/ $k$ -center squared-distortion objective; even the corresponding finite-sample optimization problem is NP-hard in general.

- If the code-length constraint is dropped, trivial worst-case additive- $\epsilon$ reconstruction is possible by quantizing all of $X$ to an $\epsilon$ -net, at the cost of $b'\approx d\log(R/\epsilon)$ bits per point (far larger than $\mathrm{poly}(\log k,\log(1/\epsilon))$ when $d$ is large).

- A different improper relaxation that reconstructs points from low-dimensional linear structure leads to PCA-type algorithms, but representing per-point coefficients to achieve error $\epsilon$ requires code length scaling on the order of the intrinsic dimension times $\log(R/\epsilon)$ , which does not match the desired polylogarithmic dependence on $k$ .

- The note points to bi-criteria approximations for $k$ -means (e.g., allowing more than $k$ centers) and to convex/spectral approaches in the broader comparative/worst-case unsupervised-learning literature as potential starting points, but does not resolve whether polylog-bit improper learning is achievable for $k>d$ .

## References

[1]

 [Open problem: Improper learning of mixtures of Gaussians](https://proceedings.mlr.press/v75/hazan18a.html) 

Elad Hazan, Livni Roi (2018)

Conference on Learning Theory (COLT), PMLR 75

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v75/hazan18a.html) [2]

 [Open problem: Improper learning of mixtures of Gaussians (PDF)](http://proceedings.mlr.press/v75/hazan18a/hazan18a.pdf) 

Elad Hazan, Livni Roi (2018)

Conference on Learning Theory (COLT), PMLR 75

📍 Proceedings PDF.

 [Link ↗](http://proceedings.mlr.press/v75/hazan18a/hazan18a.pdf)

## Notes / Progress

_Work log goes here._
