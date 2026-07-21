# Adaptive Minimax Nonparametric Hypothesis Testing

**Status:** Partially Resolved  
**Importance:** Notable

## Categories

- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #14 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix a dimension $d \geq 1$ , constants $L>0$ , $\alpha,\beta \in (0,1)$ , and a known baseline function $f_0 \in L_2([0,1]^d)$ . In the periodic Gaussian white-noise model on $\mathbb{T}^d=[0,1]^d$ ,

$
dY(x)=f(x)\,dx+n^{-1/2}dW(x), \qquad x\in \mathbb{T}^d,
$

let

$
\mathcal W_2^s(L)=\left\{f\in L_2(\mathbb{T}^d):\sum_{k\in\mathbb{Z}^d}(1+\|k\|_2^2)^s |\theta_k(f)|^2\le L^2\right\}, \qquad s>0,
$

and test

$
H_0:f=f_0
\quad\text{vs}\quad
H_1(s,\rho): f\in \mathcal W_2^s(L),\ \|f-f_0\|_{L_2}\ge \rho.
$

For fixed $s$ , the non-adaptive minimax separation radius is known to satisfy

$
\rho_n^*(s)\asymp n^{-2s/(4s+d)}.
$

Classical part (substantially understood): for several compact smoothness-range formulations (typically $s\in[s_-,s_+]$ with $0 in Gaussian sequence/white-noise settings), exact adaptation ( $c_n\equiv 1$ ) is impossible and the optimal adaptive loss is of log-log type; in Spokoiny's normalization this appears as a factor

$
t_\varepsilon=(\log\log \varepsilon^{-2})^{1/4},
$

with $\varepsilon=n^{-1/2}$ (equivalently, a $(\log\log n)^{1/4}$ -type factor in that parametrization).

### Unsolved Problem

Determine the sharp adaptive minimax rate outside those settled classical compact-range cases, especially for genuinely noncompact or otherwise broader regimes (for example $\mathcal S=(0,\infty)$ , higher-dimensional/anisotropic families, or other model variations), and identify the minimal penalty $c_n(s,d,\mathcal S)$ such that one test sequence controls type I/II errors uniformly over all $s\in\mathcal S$ .

## Significance & Implications

Adaptive nonparametric testing is a core question in mathematical statistics: unlike many estimation problems, testing can require a provable adaptation penalty. Classical compact-range Gaussian settings already show unavoidable log-log losses (with model-dependent parametrization), while broader regimes remain unresolved. Clarifying exactly where adaptation is fully characterized versus still open is important for goodness-of-fit, signal detection, and related inference tasks.

## Known Partial Results

- [Spokoiny (1996)](#references) : proves impossibility of full adaptation in the considered wavelet setting and derives a log-log adaptation factor $t_\varepsilon=(\ln\ln\varepsilon^{-2})^{1/4}$ (equivalently $(\log\log n)^{1/4}$ when $\varepsilon=n^{-1/2}$ in that parametrization).

- [Ingster & Suslina (2003)](#references) : develops sharp non-adaptive minimax testing theory for Gaussian models, including Sobolev-type classes.

- Hence classical compact smoothness-range formulations are not a blanket open problem: the main unresolved part is the sharp adaptive frontier in broader regimes (notably noncompact smoothness ranges and related generalizations).

## References

[1]

 [Adaptive hypothesis testing using wavelets](https://doi.org/10.1214/aos/1032181158) 

Vladimir Spokoiny (1996)

Annals of Statistics

📍 Section 2.3 (Adaptive testing), especially Theorems 2.2-2.3; the adaptation factor is stated as $t_\varepsilon=(\ln\ln\varepsilon^{-2})^{1/4}$ (not $\varepsilon^{-1}$), pp. 2481-2482.

 [DOI ↗](https://doi.org/10.1214/aos/1032181158) [2]

 [Nonparametric Goodness-of-Fit Testing Under Gaussian Models](https://doi.org/10.1007/978-0-387-21580-8) 

Yuri Ingster, Irina Suslina (2003)

Springer Series in Statistics (book)

 [DOI ↗](https://doi.org/10.1007/978-0-387-21580-8)

## Notes / Progress

_Work log goes here._
