# Log-factor-free adaptive contraction on general Minkowski-dimensional domains

**Status:** Unsolved  
**Source:** Sourced from the work of Tao Tang, Nan Wu, Xiuyuan Cheng, David Dunson

## Categories

- Mathematical Statistics
- Learning Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #64 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $D\ge 1$ , let $\mathcal X\subset\mathbb R^D$ be compact, and let $N(\mathcal X,r)$ be the covering number by Euclidean balls of radius $r$ . Work under an intrinsic-dimension upper-complexity condition of the form

$
N(\mathcal X,r)\le C\,r^{-d}\quad\text{for sufficiently small }r,
$

for some $d\in(0,D]$ and $C<\infty$ , together with the regression model

$
X_i\sim P_X,\qquad Y_i=f_0(X_i)+\xi_i,\qquad \xi_i\stackrel{iid}{\sim}N(0,\sigma^2),
$

where $P_X$ is supported on $\mathcal X$ .

This setup follows [Tang et al. (2024)](#references) .

What the source proves (self-contained, with notation aligned to the paper):

- Prior class (geometry-agnostic GP): use a centered GP on $\mathcal X$ with squared-exponential kernel

$
h_t(x,x')=\exp\!\left(-\frac{\|x-x'\|^2}{2t}\right),\qquad t>0,
$

and a hierarchical/empirical-Bayes prior $p_n(t)$ on bandwidth $t$ . "Geometry-agnostic" means the prior construction does not take intrinsic dimension as input and does not use manifold charts/atlases or Laplace--Beltrami coordinates; it is built from ambient Euclidean data geometry.

- General assumptions used for the adaptive-rate theorem: (A1) covering-number complexity: for some $\varrho>0$ , $C_{\mathcal X}>0$ , $r_0\in(0,1)$ ,

$
N(r,\mathcal X,\|\cdot\|_\infty)\le C_{\mathcal X}r^{-\varrho},\qquad 0

(A2) RKHS approximation: for some $s>0$ and constants $\epsilon_0,\nu_1,\nu_2>0$ , for every $0<\epsilon<\epsilon_0$ there exists $F^\epsilon\in\mathbb H_\epsilon(\mathcal X)$ such that

$
\sup_{x\in\mathcal X}|F^\epsilon(x)-f_0(x)|\le \nu_1\epsilon^{s/2},
\qquad
\|F^\epsilon\|_{\mathbb H_\epsilon(\mathcal X)}^2\le \nu_2\epsilon^{-\varrho/2};
$

(A3) prior-on-bandwidth condition: $p_n(t)$ places enough mass near $t\asymp n^{-2/(2s+\varrho)}$ and sufficiently little mass at much smaller scales (formal two-sided exponential-tail inequalities in Assumption (A3) of the paper).

- Posterior contraction definition used in the source: for a semimetric $d_n$ , a sequence $\varepsilon_n$ is a contraction rate if

$
\Pi\big(d_n(f,f_0)>\varepsilon_n\mid (X_i,Y_i)_{i=1}^n\big)\to 0
$

in probability.

- Main adaptive-rate conclusion under (A1)--(A3): in fixed design, the paper proves

$
\bar\varepsilon_n
=
C\,n^{-\frac{s}{2s+\varrho}}(\log n)^{\frac{D+1}{2+\varrho/s}+\frac{D+1}{2}}
\lesssim n^{-\frac{s}{2s+\varrho}}(\log n)^{D+1},
$

and in random design (with bounded-signal truncation in the theorem statement) obtains the same polynomial exponent in $L_2(P_X)$ up to logarithmic factors.

- Meaning of "minimax power" and "adaptation": the polynomial exponent is $s/(2s+\varrho)$ (equivalently $\beta/(2\beta+d)$ when writing $s=\beta$ , $\varrho=d$ ), which is the standard nonparametric minimax exponent for $d$ -dimensional smoothness- $\beta$ regression classes; "adaptive" means one prior construction attains this exponent across the paper's class of unknown intrinsic dimensions and smoothness levels, with only logarithmic overhead.

### Unsolved Problem

Determine whether one can remove the logarithmic loss and prove, uniformly over broad classes of $(\mathcal X,P_X,f_0)$ satisfying the source-type assumptions,

$
\Pi\!\left(\|f-f_0\|_{L_2(P_X)}>M n^{-\beta/(2\beta+d)}\,\middle|\,(X_i,Y_i)_{i=1}^n\right)\to 0
$

(in expectation under $f_0$ ) for all sufficiently large $M$ , simultaneously adaptive in unknown $d$ and unknown smoothness.

## Significance & Implications

[Tang et al. (2024)](#references) identify logarithmic factors as the remaining gap in the general low-intrinsic-dimensional setting. Closing this gap would determine whether fully geometry-agnostic GP priors attain the sharp adaptive minimax rate on general supports satisfying covering-number upper bounds.

## Known Partial Results

The paper proves adaptive posterior contraction for low-intrinsic-dimensional supports at minimax-power rates up to logarithmic factors under covering-number upper-complexity assumptions. For the manifold setting treated in the paper (with its regularity assumptions), results are also stated up to logarithmic factors.

## References

[1]

 [Adaptive Bayesian regression on data with low intrinsic dimensionality](https://arxiv.org/abs/2407.09286v3) 

Tao Tang, Nan Wu, Xiuyuan Cheng, David Dunson (2024)

Annals of Statistics (to appear)

📍 arXiv v3, Section 6 (Discussion), first paragraph (RKHS approximation/covering-number dependence for general low-dimensional supports), p. 14

Primary source. Author order follows arXiv v3 metadata; year follows the original arXiv posting year (2024), while arXiv_id points to revision v3.

 [Link ↗](https://arxiv.org/abs/2407.09286v3) [arXiv ↗](https://arxiv.org/abs/2407.09286v3)

## Notes / Progress

_Work log goes here._
