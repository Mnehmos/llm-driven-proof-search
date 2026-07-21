# Biologically Stable Maximum-Likelihood Phylogenetic Inference under Floating-Point Perturbations

**Status:** Unsolved  
**Importance:** Notable
**Source:** Posed by Lukas Huebner et al. (2026)

## Categories

- Computational Biology
- Numerical Analysis & Scientific Computing
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #23 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\Sigma$ be a finite nucleotide or amino-acid alphabet, and let $X \in \Sigma^{n \times L}$ be a multiple-sequence alignment of $n$ taxa across $L$ homologous sites. Let $\mathcal{T}_n$ denote the set of candidate tree topologies on those taxa. For a topology $\tau \in \mathcal{T}_n$ , let $b \in \mathbb{R}_{>0}^{E(\tau)}$ denote its branch lengths and let $\eta$ denote any additional substitution-model parameters, such as equilibrium frequencies, exchangeabilities, or rate-heterogeneity parameters.

Under a standard site-independent maximum-likelihood model, write

$
\ell(\tau,b,\eta;X):=\sum_{s=1}^L \log p(X_{\cdot s}\mid \tau,b,\eta)
$

for the log-likelihood of the aligned data, where $X_{\cdot s}$ is the $s$ th alignment column.

In practical maximum-likelihood (ML) phylogenetic inference, heuristic search procedures repeatedly compare candidate trees by summing sitewise likelihood contributions in floating-point arithmetic. If the reduction order depends on processor count or communication topology, then numerically distinct likelihood values can be produced even when the alignment, code, and search settings are otherwise unchanged. Let

$
\widehat{\tau}_{p}(X)
$

denote the topology returned by a fixed ML heuristic when executed with parallel configuration $p$ .

### Unsolved Problem

Develop theory and algorithms that explain or control the downstream biological instability of the family $\{\widehat{\tau}_p(X)\}_p$ . Concretely, characterize when floating-point perturbations can change only numerically negligible details versus when they can alter clades or biological conclusions, and design inference procedures that are both computationally efficient and stable across hardware or parallelism choices. A strong form would provide bit-reproducible or otherwise perturbation-robust ML inference together with principled bounds relating low-level likelihood perturbations to topological or inferential changes.

## Significance & Implications

Large-scale phylogenetics is now routinely run on parallel hardware, so numerical non-associativity is not a corner case but part of the standard inference pipeline. If hardware-level differences can change the returned topology or downstream biological interpretation, then reproducibility, benchmarking, and meta-analysis are all at risk. Resolving this problem would connect numerical analysis, parallel algorithms, and evolutionary inference in a way that directly affects practical phylogenomics.

## Known Partial Results

- [Stelz, Huebner, and Stamatakis (2026)](#references) report that varying the degree of parallelism causes divergent ML tree searches on 31% of 10,179 empirical datasets.

- Within those divergent cases, the paper reports that 8% yield trees that are statistically significantly worse than the best-known ML tree under the AU test.

- The same paper introduces a bit-reproducible variant of RAxML-NG using the ReproRed reduction algorithm, with only modest slowdown on up to 768 cores.

- What remains unresolved is the higher-level inference question: when do such low-level numerical deviations materially change the biological conclusions drawn from the resulting trees?

## References

[1]

 [Bit-reproducible parallel phylogenetic tree inference](https://academic.oup.com/bioinformatics/advance-article/doi/10.1093/bioinformatics/btag044/8445285) 

Christoph Stelz, Lukas Huebner, Alexandros Stamatakis (2026)

Bioinformatics

📍 Abstract and Introduction, especially the discussion that varying core counts can induce different topologies and that whether these numerical deviations affect biological interpretation remains open.

Primary source; quantifies topology divergence induced by floating-point non-associativity and explicitly states that the effect on biological interpretation remains open.

 [Link ↗](https://academic.oup.com/bioinformatics/advance-article/doi/10.1093/bioinformatics/btag044/8445285) [DOI ↗](https://doi.org/10.1093/bioinformatics/btag044)

## Notes / Progress

_Work log goes here._
