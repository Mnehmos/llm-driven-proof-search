# Beyond smooth finite-dimensional targets in unified semiparametric data fusion

**Status:** Unsolved  
**Source:** Sourced from the work of Ellen Sandra Graham, Marco Carone, Andrea Rotnitzky

## Categories

- Mathematical Statistics
- Learning Theory
- Information Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #69 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $X\in\mathcal X$ denote an unobserved full-data random element with unknown law $P$ in a statistical model $\mathcal P_0$ . There are $K\ge 2$ independent data sources. Source $k$ contains i.i.d. observations $W_{k,1},\dots,W_{k,n_k}$ from law $Q_k$ , where each $W_k$ takes values in $\mathcal W_k$ and is generated from $X$ through a known observation operator $T_k$ (possibly many-to-one, corresponding to missingness/coarsening/measurement error), so that $Q_k=T_k(P)$ . The analyst observes only $\{W_{k,i}:1\le i\le n_k,\,1\le k\le K\}$ , not $X$ .

This setup follows [Graham et al. (2024)](#references) .

Assume the fusion model is defined by known alignment restrictions linking the source laws to a common target law $P$ , for example conditional or marginal equalities expressible as

$
\mathcal A(P)=\{Q_1,\dots,Q_K\},
$

with $\mathcal A$ known. The observed-data model is thus

$
\mathcal Q=\{(Q_1,\dots,Q_K): \exists P\in\mathcal P_0 \text{ such that } \mathcal A(P)=\{Q_1,\dots,Q_K\}\}.
$

Let $\Psi:\mathcal P_0\to\Theta$ be the target functional, where $\Theta$ may be infinite-dimensional (for example a function space such as $L^2$ or $\ell^\infty$ ), and $\Psi$ may be nonregular (not pathwise differentiable at some or all $P$ ).

### Unsolved Problem

Formulate a general multi-source semiparametric fusion theory beyond smooth finite-dimensional targets that clarifies, under explicit conditions on $\mathcal A$ , $\mathcal P_0$ , and $\Psi$ , (i) identification (point or set) of $\Psi(P)$ from $(Q_1,\dots,Q_K)$ , (ii) observed-data tangent/cone geometry and canonical gradients when they exist, and (iii) sharp efficiency bounds for regular components together with appropriate local asymptotic minimax lower bounds and rates when regular estimation fails.

This framing extends the baseline paper's stated scope limitation.

## Significance & Implications

The baseline paper [Graham et al. (2024)](#references) states scope for smooth finite-dimensional parameters. Many practically important fusion targets (e.g., function-valued, boundary, or otherwise nonregular functionals) fall outside that class, so extending the framework could materially broaden applicability. As a direction rather than an author-posed conjecture, this appears open as of February 16, 2026, with uncertainty about very recent or parallel unpublished progress.

## Known Partial Results

The paper gives influence-function and efficient-influence-function theory for smooth finite-dimensional pathwise differentiable parameters under generalized alignment structures.

## References

[1]

 [Towards a Unified Theory for Semiparametric Data Fusion with Individual-Level Data](https://arxiv.org/abs/2409.09973) 

Ellen Sandra Graham, Marco Carone, Andrea Rotnitzky (2024)

Annals of Statistics (to appear)

📍 Abstract scope statement (smooth finite-dimensional parameter); used as motivation rather than as an explicit open-problem statement.

Baseline source motivating this extension; the exact problem wording here is a formalized extension.

 [Link ↗](https://arxiv.org/abs/2409.09973) [arXiv ↗](https://arxiv.org/abs/2409.09973)

## Notes / Progress

_Work log goes here._
