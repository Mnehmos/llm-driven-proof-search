# Statistical Identification of Primary Adjustment Sets From Data

**Status:** Unsolved  
**Source:** Sourced from the work of F. Richard Guo, Qingyuan Zhao

## Categories

- Information Theory
- Combinatorics & Graph Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #45 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $V$ be a finite set of observed variables, and let $G=(V,E_{\to},E_{\leftrightarrow})$ be an acyclic directed mixed graph (ADMG): $E_{\to}$ contains directed edges $A\to B$ , $E_{\leftrightarrow}$ contains bidirected edges $A\leftrightarrow B$ , and there is no directed cycle. For $A\in V$ , let $\mathrm{de}_G(A)$ be its descendants and $\mathrm{an}_G(A)$ its ancestors; extend to sets by unions.

A path is called a confounding arc between distinct $A,B\in V$ if it has no collider and has an arrowhead at both endpoints. Given $C\subseteq V\setminus\{A,B\}$ , such a confounding arc is unblocked given $C$ if none of its non-endpoint vertices belongs to $C$ . Write $A \not\!\perp\!\!\!\perp_{\mathrm{arc}} B\mid C$ if there exists an unblocked confounding arc between $A$ and $B$ given $C$ , and write $A \perp\!\!\!\perp_{\mathrm{arc}} B\mid C$ otherwise.

For distinct $A,B\in V$ , a set $C\subseteq V\setminus\{A,B\}$ is an adjustment set for $(A,B)$ if $C\cap(\mathrm{de}_G(A)\cup \mathrm{de}_G(B))=\varnothing$ . Given a baseline set $S\subseteq V\setminus\{A,B\}$ , an adjustment set $C$ is primary for $(A,B)$ relative to $S$ if

$
A \perp\!\!\!\perp_{\mathrm{arc}} B \mid S\cup C.
$

It is minimal primary if no proper subset of $C$ is primary relative to $S$ .

Define

$
\mathcal M_G(A,B;S):=\{C:\ C\text{ is minimal primary for }(A,B)\text{ relative to }S\},
$

fix a deterministic selector $\mathfrak t$ on nonempty finite sets, and define

$
P^\star_G(A,B;S):=\begin{cases}
\mathfrak t\big(\mathcal M_G(A,B;S)\big), & \mathcal M_G(A,B;S)\neq\varnothing,\\
\bot, & \mathcal M_G(A,B;S)=\varnothing,
\end{cases}
$

where $\bot$ is a convention meaning "no minimal primary adjustment set exists." For the target pair $(X,Y)$ , let $P^\star(X,Y;G):=P^\star_G(X,Y;\varnothing)$ .

Data are generated from an unknown causal model whose latent projection on $V$ is $G$ . Let $\mathbb P$ denote either (i) the observational distribution on $V$ , or (ii) a specified family of interventional distributions $\{\mathbb P^{do(I=i)}: i\in\mathcal I\}$ for a known intervention set $\mathcal I$ . Let $\mathcal G(\mathbb P)$ be the class of ADMGs compatible with the available distribution(s).

### Unsolved Problem

Characterize conditions under which $P^\star(X,Y;G)$ is identifiable from $\mathbb P$ over $\mathcal G(\mathbb P)$ , i.e. whether all compatible graphs agree on this target (including possible value $\bot$ ). Equivalently, ask whether there exists a functional $\phi$ such that for every admissible $G$ ,

$
\phi(\mathbb P)=P^\star(X,Y;G).
$

Under such conditions, construct estimators $\widehat P_n=\widehat P_n(\mathbb P_n)$ from $n$ samples (or pooled interventional samples) that are consistent for this discrete target, i.e. $\Pr(\widehat P_n=P^\star(X,Y;G))\to 1$ as $n\to\infty$ .

## Significance & Implications

The method is interactive and relies on elicited structural information rather than full graph specification. Understanding when primary sets are data-identifiable would reduce reliance on subjective input and connect the framework to statistical learning. It would also clarify limits of what can be identified without complete causal-graph knowledge.

## Known Partial Results

The paper provides a procedural framework and correctness guarantees conditional on correctly provided primary adjustment sets, but does not claim these sets are statistically identifiable from observed/interventional data alone. This direction remains open in the source paper.

## References

[1]

 [Confounder Selection via Iterative Graph Expansion](https://arxiv.org/abs/2309.06053v3) 

F. Richard Guo, Qingyuan Zhao (2025)

Annals of Statistics (to appear)

📍 Section 5.4 (Finding primary adjustment sets): source paper raises the learnability/identifiability question for primary adjustment sets. The selector-based $P^\star_G$ / $\phi$ formulation is an explicit formalization layer.

Primary source paper. Citation-year convention used here: first arXiv submission in 2023, cited version is arXiv v3 (2025 revision).

 [Link ↗](https://arxiv.org/abs/2309.06053v3) [arXiv ↗](https://arxiv.org/abs/2309.06053v3)

## Notes / Progress

_Work log goes here._
