# Complete Generic Identifiability in Cyclic LiNGAM with General Confounding

**Status:** Unsolved  
**Source:** Sourced from the work of Daniele Tramontano, Jalal Etesami, Mathias Drton

## Categories

- Mathematical Statistics
- Probability Theory
- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #57 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $V=\{1,\dots,p\}$ index observed variables $X=(X_1,\dots,X_p)^\top\in\mathbb{R}^p$ . Consider the linear structural equation model with feedback

$
X=B^\top X+U,
$

equivalently $X_i=\sum_{j\in V\setminus\{i\}}\beta_{ij}X_j+U_i$ for each $i$ , where $B=(\beta_{ij})_{i,j=1}^p$ has zero diagonal and $I-B^\top$ is invertible (so $X=(I-B^\top)^{-1}U$ is well defined). Directed cycles in the observed graph are allowed: define $G_{\mathrm{dir}}$ on $V$ by $j\to i$ iff $\beta_{ij}\neq 0$ .

This setup follows [Tramontano et al. (2025)](#references) .

Assume the disturbance vector $U=(U_1,\dots,U_p)^\top$ is generated from latent exogenous noise as follows: there exist independent non-Gaussian random variables $\varepsilon_1,\dots,\varepsilon_m$ and measurable functions $g_i:\mathbb{R}^m\to\mathbb{R}$ such that

$
U_i=g_i(\varepsilon_1,\dots,\varepsilon_m),\qquad i=1,\dots,p.
$

Hence the joint law of $U$ may have arbitrary dependence (including higher-order confounding) induced by shared latent exogenous sources and nonlinear mixing. The observational input is only the joint law $\mathcal{L}(X)$ .

Fix a graphical model class $\mathcal{M}(\mathcal{G})$ specified by: which directed coefficients $\beta_{ij}$ are structurally allowed/nonzero (the directed part), and which latent confounding patterns are structurally allowed (e.g., via latent nodes pointing to subsets of observed nodes, equivalently a latent-projection/hyperedge specification). For a directed edge parameter $\beta_{ij}$ , say $\beta_{ij}$ is generically identifiable in $\mathcal{M}(\mathcal{G})$ if there exists an exceptional set of parameter values of measure zero in the finite-dimensional structural parameters (at least the directed coefficients, and any finite-dimensional confounding-structure parameters if present) such that, outside that set, equality of observational laws implies equality of that coefficient: if $\mathcal{L}_\theta(X)=\mathcal{L}_{\theta'}(X)$ then $\beta_{ij}(\theta)=\beta_{ij}(\theta')$ .

### Unsolved Problem

Determine necessary and sufficient purely graphical conditions on $\mathcal{G}$ under which each direct effect $\beta_{ij}$ is generically identifiable from $\mathcal{L}(X)$ in this cyclic, non-Gaussian, generally confounded model class, and construct a decision procedure that, given $\mathcal{G}$ and $(i,j)$ , decides identifiability of $\beta_{ij}$ in time polynomial in the graph size.

## Significance & Implications

The paper's main theorem is for acyclic models; extending this to feedback systems would cover many equilibrium and dynamical applications. A full criterion would close a central gap between DAG-based identification and realistic systems with cycles. See [Tramontano et al. (2025)](#references) for details.

## Known Partial Results

This paper proves a necessary-and-sufficient criterion (with polynomial-time algorithm) for generic identifiability of direct effects in the acyclic case, and only explores a generalization to feedback loops.

## References

[1]

 [Parameter identification in linear non-Gaussian causal models under general confounding](https://arxiv.org/abs/2405.20856) 

Daniele Tramontano, Jalal Etesami, Mathias Drton (2025)

Annals of Statistics (to appear)

📍 arXiv:2405.20856, Section 7 ("Cyclic Graphs"), concluding discussion on extending identifiability to feedback loops.

Source paper where this problem appears.

 [Link ↗](https://arxiv.org/abs/2405.20856) [arXiv ↗](https://arxiv.org/abs/2405.20856)

## Notes / Progress

_Work log goes here._
