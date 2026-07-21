# Finite-sample optimal FDR-FNR frontier under the two-group model

**Status:** Unsolved  
**Source:** Sourced from the work of Yutong Nie, Yihong Wu

## Categories

- Mathematical Statistics
- Probability Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #48 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix a finite integer $n \ge 1$ . For each $i \in \{1,\dots,n\}$ , let $\theta_i \in \{0,1\}$ be the latent hypothesis state, where $\theta_i=0$ means null and $\theta_i=1$ means non-null. Assume $(\theta_i)_{i=1}^n$ are i.i.d. with $\mathbb P(\theta_i=1)=\pi_1 \in (0,1)$ and $\pi_0=1-\pi_1$ . Conditional on $\theta_i$ , the test statistic $X_i$ takes values in a measurable space $(\mathcal X,\mathcal A)$ and has distribution

$
X_i \mid (\theta_i=0) \sim P_0,\qquad X_i \mid (\theta_i=1) \sim P_1,
$

where $P_0,P_1$ are known and dominated by a common measure (densities $f_0,f_1$ may be used). Assume conditional independence across $i$ : given $(\theta_1,\dots,\theta_n)$ , the variables $X_1,\dots,X_n$ are independent.

This setup follows [Nie & Wu (2023)](#references) .

A (possibly compound, randomized) multiple-testing rule is any measurable map $\delta_n$ that, from $(X_1,\dots,X_n)$ and an auxiliary random seed independent of the data, outputs decisions $D_i \in \{0,1\}$ ( $D_i=1$ means reject $H_i$ ). Define

$
R=\sum_{i=1}^n D_i,\quad
V=\sum_{i=1}^n (1-\theta_i)D_i,\quad
T=\sum_{i=1}^n \theta_i(1-D_i).
$

The false discovery rate and false non-discovery rate are

$
\mathrm{FDR}(\delta_n)=\mathbb E\!\left[\frac{V}{R\vee 1}\right],\qquad
\mathrm{FNR}(\delta_n)=\mathbb E\!\left[\frac{T}{(n-R)\vee 1}\right],
$

where expectations are under the full two-group model (including rule randomization).

For $\alpha\in(0,1)$ , define the finite-sample constrained objective

$
\Psi_n(\alpha)=\inf_{\delta_n:\,\mathrm{FDR}(\delta_n)\le \alpha}\mathrm{FNR}(\delta_n).
$

### Unsolved Problem

Determine $\Psi_n(\alpha)$ exactly (or derive non-asymptotic minimax-sharp upper and lower bounds) as an explicit function of $(n,\alpha,\pi_1,P_0,P_1)$ , and characterize all optimal rules $\delta_n^\star$ that attain (or provably approximate sharply) this infimum, allowing fully compound and randomized procedures.

## Significance & Implications

Nie and Wu's 2023 preprint establishes asymptotic limits as $n\to\infty$ , but does not provide a complete exact finite- $n$ frontier characterization. Treating the finite-sample frontier as an open objective is therefore the conservative reading; resolving it would quantify finite-vs-asymptotic gaps and guide practical procedure design.

## Known Partial Results

The cited work characterizes asymptotically optimal FDR-FNR tradeoffs under the two-group random-mixture model and shows compound rules are necessary for asymptotic optimality (in contrast to mFDR-mFNR). The exact finite-sample frontier characterization is treated as open.

## References

[1]

 [Large-Scale Multiple Testing: Fundamental Limits of False Discovery Rate Control and Compound Oracle](https://arxiv.org/abs/2302.06809v3) 

Yutong Nie, Yihong Wu (2023)

arXiv preprint

📍 arXiv:2302.06809v3 PDF, Section 1.1 (Background and problem formulation), p. 3, immediately after Eq. (2) defining $FNR_n^*(\alpha)$: "it still remains open how to find the optimal decision rule to characterize the finite-sample tradeoff between FDR and FNR."

Primary preprint source for the asymptotic frontier and explicit finite-sample open-direction wording.

 [Link ↗](https://arxiv.org/abs/2302.06809v3) [arXiv ↗](https://arxiv.org/abs/2302.06809v3) [2]

 [Large-Scale Multiple Testing: Fundamental Limits of False Discovery Rate Control and Compound Oracle](https://projecteuclid.org/journals/annals-of-statistics/volume-54/issue-1/Large-Scale-Multiple-Testing-Fundamental-Limits-of-False-Discovery-Rate/10.1214/24-AOS2466.full) 

Yutong Nie, Yihong Wu (2026)

Annals of Statistics 54(1):232-264

📍 Project Euclid article metadata/citation page for Annals of Statistics, Vol. 54, No. 1 (2026), pp. 232-264.

Final journal publication metadata, kept separate from the 2023 preprint record.

 [Link ↗](https://projecteuclid.org/journals/annals-of-statistics/volume-54/issue-1/Large-Scale-Multiple-Testing-Fundamental-Limits-of-False-Discovery-Rate/10.1214/24-AOS2466.full) [DOI ↗](https://doi.org/10.1214/24-AOS2466)

## Notes / Progress

_Work log goes here._
