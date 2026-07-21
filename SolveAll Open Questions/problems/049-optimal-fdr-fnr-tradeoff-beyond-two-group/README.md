# Optimal FDR-FNR tradeoff beyond independent two-group mixtures

**Status:** Unsolved  
**Source:** Sourced from the work of Yutong Nie, Yihong Wu

## Categories

- Mathematical Statistics
- Probability Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #49 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

For each dimension $n\ge 1$ , let $(X^{(n)},H^{(n)})$ be a random pair with $X^{(n)}=(X_1,\dots,X_n)\in\mathcal X^n$ observed and $H^{(n)}=(H_1,\dots,H_n)\in\{0,1\}^n$ latent, where $H_i=0$ means the $i$ -th null hypothesis is true and $H_i=1$ means it is false. No independence is assumed: the coordinates of $H^{(n)}$ may be dependent, and the conditional law of $X^{(n)}$ given $H^{(n)}$ may have arbitrary dependence across coordinates. Let $P_n$ denote the joint law of $(X^{(n)},H^{(n)})$ .

A multiple-testing rule is a measurable map $\delta_n:\mathcal X^n\to\{0,1\}^n$ , with $\delta_{n,i}(X^{(n)})=1$ meaning reject hypothesis $i$ . Define

$
R_n=\sum_{i=1}^n \delta_{n,i},\qquad
V_n=\sum_{i=1}^n (1-H_i)\delta_{n,i},\qquad
U_n=n-R_n,\qquad
W_n=\sum_{i=1}^n H_i(1-\delta_{n,i}).
$

Here $V_n$ is the number of false discoveries and $W_n$ is the number of false non-discoveries. The false discovery rate and false non-discovery rate under $P_n$ are

$
\mathrm{FDR}_{P_n}(\delta_n)=\mathbb E_{P_n}\!\left[\frac{V_n}{R_n\vee 1}\right],\qquad
\mathrm{FNR}_{P_n}(\delta_n)=\mathbb E_{P_n}\!\left[\frac{W_n}{U_n\vee 1}\right].
$

Fix $\alpha\in(0,1)$ . for a dependent model sequence $P=(P_n)_{n\ge1}$ , define

$
\Psi_{\mathrm{dep}}(\alpha;P)
=\liminf_{n\to\infty}\ \inf_{\delta_n:\ \mathrm{FDR}_{P_n}(\delta_n)\le \alpha}\ \mathrm{FNR}_{P_n}(\delta_n).
$

### Unsolved Problem

Characterize $\Psi_{\mathrm{dep}}(\alpha;P)$ for broad classes of dependent high-dimensional models $P$ (beyond independent two-group mixtures), and determine whether there is a strict asymptotic performance gap between compound rules (each $\delta_{n,i}$ may depend on all of $X^{(n)}$ ) and separable rules (each $\delta_{n,i}$ depends only on $X_i$ , possibly with external randomization).

## Significance & Implications

Many practically important large-scale testing settings exhibit substantial dependence across hypotheses. Extending fundamental limit theory to dependent settings is important for understanding whether existing procedures remain near-optimal or can be substantially improved; see [Nie & Wu (2023)](#references) .

## Known Partial Results

The paper resolves the asymptotic frontier for the two-group random mixture model (and fixed non-null proportion extensions), including Gaussian location examples, under the model assumptions studied there. Targeted follow-up check through 2026-02-17 did not find a definitive post-2024 resolution of the strongly dependent-model tradeoff question in this generality.

## References

[1]

 [Large-scale Multiple Testing: Fundamental Limits of False Discovery Rate Control and Compound Oracle](https://arxiv.org/abs/2302.06809v3) 

Yutong Nie, Yihong Wu (2026)

Annals of Statistics (forthcoming; listed as 2026 in author publication records)

📍 arXiv v3, Section 6.3 ("Weakly dependent data"), paragraph immediately preceding Theorem 24: "Characterizing the optimal FDR-FNR tradeoff for models with strongly dependent data is an open problem."

Primary source paper; arXiv v3 is the fixed accessible version used for locator text.

 [Link ↗](https://arxiv.org/abs/2302.06809v3) [DOI ↗](https://doi.org/10.48550/arXiv.2302.06809) [arXiv ↗](https://arxiv.org/abs/2302.06809v3)

## Notes / Progress

_Work log goes here._
