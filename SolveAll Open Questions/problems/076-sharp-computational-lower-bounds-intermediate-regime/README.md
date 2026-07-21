# Sharp computational lower bounds for valid inference in the intermediate regime

**Status:** Unsolved  
**Source:** Sourced from the work of Wanteng Ma, Dong Xia

## Categories

- Mathematical Statistics
- Probability Theory
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #76 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Consider the noisy Tucker tensor completion model with order $m=3$ . For each dimension $d\to\infty$ , let $T^\star\in\mathbb{R}^{d\times d\times d}$ have multilinear rank $(r_1,r_2,r_3)$ with $r_j=O(1)$ , Tucker decomposition $T^\star=C^\star\times_1 U_1^\star\times_2 U_2^\star\times_3 U_3^\star$ , incoherent factor matrices, and bounded condition number $\kappa(T^\star)=\lambda_{\max}/\lambda_{\min}\le \kappa_0$ , where $\lambda_{\min}:=\min_{j\in\{1,2,3\}}\lambda_{r_j}(M_j(T^\star))$ . We observe $n=n(d)$ i.i.d. samples

$
Y_i=\langle T^\star,X_i\rangle+\xi_i,\qquad i=1,\dots,n,
$

where $X_i$ is uniformly distributed on the canonical basis tensors $\{e_a\circ e_b\circ e_c: a,b,c\in[d]\}$ , and $\xi_i$ are i.i.d. mean-zero noise with variance $\sigma^2$ (e.g. Gaussian or uniformly sub-Gaussian). Let $d^\star=d^3$ . For a deterministic indexing tensor $I=I_d\in\mathbb{R}^{d\times d\times d}$ , the inferential target is $\theta^\star=\langle T^\star,I\rangle$ .

This setup follows [Ma & Xia (2024)](#references) .

The cited paper proves Cram'er-Rao-optimal uncertainty quantification in its analyzed settings, including a rank-one regime. In particular, for rank-one (as treated in-source), with $\mathcal{M}_r$ the rank manifold and $P_{T^\star}(I)$ the tangent-space projection, the asymptotic variance benchmark is

$
v^\star(T^\star,I):=\sigma^2\frac{d^\star}{n}\|P_{T^\star}(I)\|_F^2.
$

For general multilinear rank $(r_1,r_2,r_3)$ , taking this same formula as an information-theoretic optimum is a natural extrapolation but is not established in the source; extending CRLB-sharp characterization to full general-rank settings remains open/challenging.

Define a polynomial-time valid inference procedure as a randomized algorithm running in $\mathrm{poly}(d,n)$ time that outputs $(\widehat\theta,\widehat v)$ such that uniformly over a model class $\mathcal{P}_d$ ,

$
\sup_{t\in\mathbb{R}}\left|\mathbb{P}_{P}\!\left(\frac{\widehat\theta-\theta^\star}{\sqrt{\widehat v}}\le t\right)-\Phi(t)\right|\to 0,
\qquad
\widehat v/v^\star(T^\star,I)\xrightarrow{\mathbb{P}_P}1.
$

Using the source?s computational and statistical benchmark scalings in simplified form (absolute constants and polylog factors suppressed), one gets:

$
\text{(computational benchmark, simplified)}\quad n\gg (d^\star)^{1/2}=d^{3/2},\qquad \frac{\lambda_{\min}}{\sigma}\gg \sqrt{\frac{(d^\star)^{3/2}}{n}}=\sqrt{\frac{d^{9/2}}{n}},
$

$
\text{(statistical benchmark, simplified)}\quad n\gg d,\qquad \frac{\lambda_{\min}}{\sigma}\gg \sqrt{\frac{d^\star d}{n}}=\sqrt{\frac{d^4}{n}}.
$

The intermediate regime is where the statistical benchmark holds but the computational benchmark fails (in at least one inequality).

### Unsolved Problem

Characterize the sharp computational boundary for valid inference in this intermediate regime. Further open direction: prove matching algorithmic achievability/impossibility under explicit average-case hardness assumptions (e.g., planted-clique- or low-degree-style hypotheses), up to constants/polylogs.

## Significance & Implications

[Ma & Xia (2024)](#references) identifies statistical/computational phase behavior and explicitly leaves the intermediate-regime computational boundary unresolved.

## Known Partial Results

The paper proves asymptotic normality and variance-optimality guarantees in specific analyzed regimes, and maps statistical-versus-computationally favorable regions (including initialization effects). It does not prove a hardness-based impossibility theorem for the intermediate regime; such lower-bound statements are a reasonable future direction rather than a reported Section 7.1 result.

## References

[1]

 [Statistical Inference in Tensor Completion: Optimal Uncertainty Quantification and Statistical-to-Computational Gaps](https://arxiv.org/abs/2410.11225v2) 

Wanteng Ma, Dong Xia (2024)

Annals of Statistics (future papers list; final volume/issue/pages/DOI not publicly listed as of Feb 16, 2026)

📍 arXiv v2 dated Nov 1, 2024: Section 7.1 opening paragraph (open computational question) and Assumption 5 / Assumption 7 scaling conditions (used here only as simplified benchmarks with constants/polylogs suppressed).

Primary source paper; Annals bibliographic finalization appears pending.

 [Link ↗](https://arxiv.org/abs/2410.11225v2) [arXiv ↗](https://arxiv.org/abs/2410.11225v2)

## Notes / Progress

_Work log goes here._
