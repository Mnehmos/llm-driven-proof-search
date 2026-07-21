# Distinguishing Adaptive Evolution from Ecological Turnover in Longitudinal Metagenomics

**Status:** Unsolved  
**Importance:** Notable
**Source:** Posed by Barbara Moguel et al. (2026)

## Categories

- Computational Biology
- Mathematical Statistics
- Probability Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #24 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Consider a microbial community observed by longitudinal metagenomic sequencing at times $t=1,\dots,T$ . Let $\mathcal{G}$ be a latent collection of lineages, strains, or haplotypes. At time $t$ , lineage $g \in \mathcal{G}$ has relative abundance $\pi_t(g) \ge 0$ with $\sum_{g \in \mathcal{G}} \pi_t(g)=1$ . For each genomic marker $k$ (for example a gene, allele, SNP, or k-mer feature), let $a_t(g,k)$ denote the expected contribution of lineage $g$ to that marker at time $t$ .

Metagenomic sequencing does not directly reveal the latent objects $\pi_t(g)$ and $a_t(g,k)$ ; instead, one observes noisy aggregate read counts or coverages

$
Y_{t,k},
$

whose expectation is approximately determined by the community mixture, for example

$
\mathbb{E}[Y_{t,k}] \approx N_t \sum_{g \in \mathcal{G}} \pi_t(g)a_t(g,k),
$

where $N_t$ is the sequencing depth of sample $t$ . Temporal changes in the observed genomic profile can arise from at least two qualitatively different mechanisms:

- 

within-lineage adaptive evolution, where $a_t(g,k)$ changes over time inside persisting lineages because of mutation or selection; and

- 

ecological turnover, where the marker profiles are approximately stable within lineages but the abundance vector $\pi_t$ changes because different lineages rise or fall in prevalence.

### Unsolved Problem

Construct statistically identifiable and computationally tractable inference procedures that, from longitudinal metagenomic data (with at most limited side information), separate these two mechanisms and quantify uncertainty in the decomposition. In particular, determine what temporal resolution, marker information, or auxiliary assays are sufficient to decide when an observed genomic shift should be attributed to adaptation rather than turnover, and whether one can make quantitative predictions for future community dynamics from that decomposition.

## Significance & Implications

This question sits at the heart of using metagenomics for evolutionary biology rather than descriptive cataloging. Without a principled way to separate selection from community replacement, it is hard to interpret microbial responses to climate change, domestication, antimicrobial pressure, or host transition. A sharp solution would turn longitudinal metagenomics into a more causally informative tool for microbial evolution and ecosystem prediction.

## Known Partial Results

- [Moguel et al. (2026)](#references) review how metagenomics has already uncovered previously inaccessible microbial diversity, deep branching events, host-associated evolution, and ancient ecological change.

- The same review identifies a remaining interpretability bottleneck: current analyses often observe genomic shifts but cannot cleanly determine whether those shifts reflect adaptation within lineages or replacement of lineages in the community.

- The review argues that longitudinal metagenomics, experimental evolution, functional assays, and predictive modeling are promising ingredients, but does not provide a general inferential framework that resolves the adaptation-versus-turnover ambiguity.

## References

[1]

 [Recent Microbial Evolutionary Insights From Metagenomics](https://academic.oup.com/gbe/article/18/3/evag029/8471837) 

Barbara Moguel, Laura Carrillo Olivas, Mariana G. Guerrero-Osornio, Sur Herrera Paredes (2026)

Genome Biology and Evolution

📍 Abstract and Significance sections, plus concluding discussion of open challenges in microbial evolution through metagenomics.

Primary source and recent status review; explicitly lists the difficulty of distinguishing adaptive evolution from ecological turnover as a key remaining challenge.

 [Link ↗](https://academic.oup.com/gbe/article/18/3/evag029/8471837) [DOI ↗](https://doi.org/10.1093/gbe/evag029)

## Notes / Progress

_Work log goes here._
