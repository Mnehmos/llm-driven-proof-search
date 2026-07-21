# Full Multiple-Break Theory for Latent Group Structure and Coefficients

**Status:** Unsolved  
**Source:** Sourced from the work of Degui Li, Bin Peng, Songqiao Tang, Wei Biao Wu

## Categories

- Mathematical Statistics
- Optimization & Variational Methods
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #47 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\{x_t\}_{t=0}^T$ be an $N$ -dimensional time series, $x_t=(x_{1t},\dots,x_{Nt})^\top\in\mathbb R^N$ , with observed $N\times N$ network weight matrices $\{W_t\}_{t=1}^T$ (possibly time-varying), and regressors $z_{it}\in\mathbb R^d$ . Consider

$
x_{it}=z_{it}^\top\theta_i(t/T)+\varepsilon_{it},\qquad i=1,\dots,N,\ t=1,\dots,T,
$

with unknown coefficient functions $\theta_i:[0,1]\to\mathbb R^d$ .

This setup follows [Li et al. (2024)](#references) .

The cited source proves a single-break version of this model and notes multiple breaks as a future direction, but does not provide a formal multiple-break theorem.

Consider the following multiple-break extension: for unknown breaks $1 (with $t_0=0$ , $t_{p+1}=T$ ), each segment $\ell\in\{1,\dots,p+1\}$ has a latent partition

$
\mathcal G^{(\ell)}=\{G_1^{(\ell)},\dots,G_{K^{(\ell)}}^{(\ell)}\},
$

and group-specific coefficient functions $\vartheta_k^{(\ell)}$ such that

$
\theta_i(u)=\vartheta_k^{(\ell)}(u),\quad i\in G_k^{(\ell)},\ u\in(t_{\ell-1}/T,t_\ell/T].
$

Across segments, $\mathcal G^{(\ell)}$ , $K^{(\ell)}$ , and $\vartheta_k^{(\ell)}$ may change.

### Unsolved Problem

Construct a fully data-driven estimator

$
(\hat p,\hat t_1,\dots,\hat t_{\hat p},\hat{\mathcal G}^{(1)},\dots,\hat{\mathcal G}^{(\hat p+1)},\hat K^{(1)},\dots,\hat K^{(\hat p+1)})
$

and prove joint consistency as $N,T\to\infty$ under explicit assumptions and rates (to be stated and verified in the multiple-break setting), including

$
P(\hat p=p)\to1,
$

$
\max_{1\le j\le p}\left|\frac{\hat t_j-t_j}{T}\right|\to_P0,
$

and segment-wise group recovery up to label permutation:

$
P\!\left(\forall\ell\ \exists\ \pi_{\ell}\text{ permutation of }\{1,\dots,K^{(\ell)}\}:\ \hat K^{(\ell)}=K^{(\ell)}\ \text{and}\ \hat G_k^{(\ell)}=G_{\pi_{\ell}(k)}^{(\ell)}\ \forall k\right)\to1.
$

This full multiple-break theorem is not proved in the cited source.

## Significance & Implications

Real network time series often exhibit more than one regime change. A rigorous multiple-break theory would provide guarantees for simultaneous segmentation and latent-group recovery across regimes. The cited work was first posted on arXiv in 2023 and revised as arXiv v2 in 2024; the multiple-break claim there is presented as a plausible extension rather than a proved theorem.

## Known Partial Results

The paper proves one-break results (Theorem 5.1). Remark 5.2(ii) states that multiple breaks may be tractable with minor amendments and recursive/binary-segmentation-style ideas, but does not supply a formal proof. This problem remains open in that source.

## References

[1]

 [Estimation of Grouped Time-Varying Network Vector Autoregressive Models](https://arxiv.org/abs/2303.10117v2) 

Degui Li, Bin Peng, Songqiao Tang, Wei Biao Wu (2024)

arXiv preprint

📍 arXiv:2303.10117v2 (2024 revision), Section 5, Remark 5.2(ii), p. 19

Primary source for the one-break theorem and the multiple-break extension remark.

 [Link ↗](https://arxiv.org/abs/2303.10117v2) [arXiv ↗](https://arxiv.org/abs/2303.10117v2)

## Notes / Progress

_Work log goes here._
