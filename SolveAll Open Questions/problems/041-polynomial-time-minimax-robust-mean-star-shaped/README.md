# Polynomial-time minimax robust mean estimation under star-shaped constraints

**Status:** Unsolved  
**Source:** Sourced from the work of Akshay Prasadan, Matey Neykov

## Categories

- Mathematical Statistics
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #41 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix integers $n,N \ge 1$ , a contamination level $\epsilon \in [0,1/2)$ , a scale parameter $\sigma>0$ , and a star-shaped set $K\subseteq\mathbb{R}^n$ (that is, there exists $k^\star\in K$ such that $k^\star+t(x-k^\star)\in K$ for every $x\in K$ and $t\in[0,1]$ ). Let

$
d:=\sup_{u,v\in K}\|u-v\|_2\in[0,\infty].
$

For $\delta>0$ and $A\subseteq\mathbb{R}^n$ , let $\mathcal{M}(\delta,A)$ be the maximal cardinality of a $\delta$ -packing of $A$ in Euclidean norm (pairwise distances $>\delta$ ). For an absolute constant $c>0$ , define the local entropy

$
\mathcal{M}^{\mathrm{loc}}_K(\eta,c):=\sup_{\nu\in K}\mathcal{M}(\eta/c,\;B(\nu,\eta)\cap K),\qquad \eta>0,
$

and define

$
\eta^\star:=\sup\left\{\eta\ge 0:\frac{N\eta^2}{\sigma^2}\le \log \mathcal{M}^{\mathrm{loc}}_K(\eta,c)\right\}.
$

This setup follows [Prasadan & Neykov (2024)](#references) .

Data model: there are unobserved clean samples $\widetilde X_i=\mu+\xi_i$ , $i=1,\dots,N$ , with unknown $\mu\in K$ . An adversary, after seeing all clean samples and the estimation procedure, outputs observed samples $X_1,\dots,X_N$ by changing at most $\epsilon N$ coordinates arbitrarily. Denote by $\mathfrak C_\epsilon$ the class of all such contamination mechanisms. The estimator $\widehat\mu$ is any measurable function of $(X_1,\dots,X_N)$ .

Noise regimes:

- 

Gaussian: $\xi_i\stackrel{iid}{\sim}N(0,\sigma^2 I_n)$ .

- 

Known-or-sign-symmetric sub-Gaussian: $\xi_i$ are iid mean-zero sub-Gaussian vectors with parameter at most $\sigma$ , and either the full noise law is known or $\xi_i\stackrel{d}{=}-\xi_i$ .

### Unsolved Problem

- Unknown sub-Gaussian: $\xi_i$ are iid mean-zero sub-Gaussian vectors with parameter at most $\sigma$ , with otherwise unknown law.

For each regime, the minimax risk is

$
\inf_{\widehat\mu}\sup_{\mu\in K}\sup_{\text{allowed noise laws}}\sup_{C\in\mathfrak C_\epsilon}\mathbb E\|\widehat\mu(X_1,\dots,X_N)-\mu\|_2^2.
$

Information-theoretic rates are proved up to universal constants in a small-contamination regime (i.e., for sufficiently small absolute-constant contamination levels, rather than uniformly for all $\epsilon\in [Prasadan & Neykov (2024)](#references) establishes statistical optimality but with algorithms that are not computationally practical. Closing this statistical-computational gap is central for turning the theory into usable robust procedures in high dimensions. A positive result would unify optimal robustness and tractability under very general geometric constraints.

## Known Partial Results

This paper proves the above minimax rates information-theoretically and gives matching (but computationally hard) procedures in the stated small-contamination regime. Prior efficient methods either need stronger assumptions (e.g., symmetry/known structure) or are rate-suboptimal in general unknown-noise settings.

## References

[1]

 [Information Theoretic Limits of Robust Sub-Gaussian Mean Estimation Under Star-Shaped Constraints](https://arxiv.org/abs/2412.03832v2) 

Akshay Prasadan, Matey Neykov (2024)

Annals of Statistics (to appear)

📍 Section 6 (Discussion and Future Work), first paragraph, which asks for "computationally efficient algorithms achieving the same performance under various constraints for the mean".

Primary source for this problem. Year convention here uses the initial arXiv preprint year (2024), not a later revision/acceptance publication year.

 [Link ↗](https://arxiv.org/abs/2412.03832v2) [arXiv ↗](https://arxiv.org/abs/2412.03832v2)

## Notes / Progress

_Work log goes here._
