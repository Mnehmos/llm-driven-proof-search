# Joint Multi-Locus Phylogeographic Inference with Recombination, Transmission, and Geography

**Status:** Unsolved  
**Importance:** Notable
**Source:** Posed by Benjamin Singer et al. (2024)

## Categories

- Computational Biology
- Probability Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #26 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Suppose $N$ genomes are sampled from an evolving pathogen population at multiple loci $\ell=1,\dots,m$ . For each sample $i \in \{1,\dots,N\}$ and locus $\ell$ , one observes an aligned sequence $S_i^{(\ell)}$ together with spatial metadata $z_i$ , such as a discrete sampling region or a continuous sampling location in a geographic space $\mathcal{Z}$ .

For each locus $\ell$ , let $T_\ell$ be the rooted local genealogy with branch lengths and leaves labeled by the sampled genomes. In the presence of recombination or reassortment, the genealogies $T_1,\dots,T_m$ need not agree. The multi-locus ancestry is therefore more naturally represented by an ancestral recombination graph (ARG), or another coupled collection of local trees,

$
\mathcal{A}=(T_1,\dots,T_m;B),
$

where $B$ encodes the recombination or reassortment structure linking the local genealogies.

Along each local genealogy $T_\ell$ , one would also like to reconstruct an ancestral geographic-history process taking values in $\mathcal{Z}$ and describing migration or spatial movement through time. In pathogen settings, the underlying data-generating mechanism may additionally involve transmission or birth-death dynamics that couple the genealogies and the geography.

### Unsolved Problem

Develop a statistically coherent and computationally tractable model for joint inference of sequence evolution, transmission or birth-death history, recombination, and geography across multiple loci, with full uncertainty quantification. In particular, design an inference procedure that does not treat loci independently, that scales beyond toy datasets, and that can represent uncertainty both in the recombination structure and in the reconstructed geographic histories of genomic regions with partially incompatible ancestries.

## Significance & Implications

Modern phylogeography is used to understand how pathogens emerge and spread, but recombination and reassortment can decouple the geographic histories of different genomic regions. Without a joint model, multi-locus phylogeographic conclusions can miss or blur these divergent histories. A scalable solution would directly improve the analysis of recombining pathogens and link phylogeography more tightly to modern ARG inference.

## Known Partial Results

- [Singer et al. (2024)](#references) introduce incompatibility measures that compare phylogeographies across loci and thereby detect when different genomic regions carry genuinely different geographic histories.

- The same paper explicitly states that the next major step is a full stochastic model of sequence evolution, birth-death, transmission, recombination, and geography for joint multi-locus inference, and notes that adding transmission and geography remains a technical challenge.

- On the scalability side, ARG inference has advanced substantially; for example, [Kelleher et al. (2019)](#references) show that large-scale whole-genome history inference is possible in related settings.

- What is still missing is a single framework that combines this genealogical scalability with joint phylogeographic uncertainty under recombination.

## References

[1]

 [Comparing Phylogeographies to Reveal Incompatible Geographical Histories within Genomes](https://academic.oup.com/mbe/article/41/7/msae126/7699621) 

Benjamin Singer, Antonello Di Nardo, Jotun Hein, Luca Ferretti (2024)

Molecular Biology and Evolution

📍 Discussion, especially the paragraph beginning 'Eventually, a full stochastic model of sequence evolution, birth-death, transmission, recombination, and geography should be developed...'.

Primary source; introduces incompatibility measures for locus-specific phylogeographies and explicitly states the open challenge of a full joint stochastic model with recombination, transmission, and geography.

 [Link ↗](https://academic.oup.com/mbe/article/41/7/msae126/7699621) [DOI ↗](https://doi.org/10.1093/molbev/msae126) [2]

 [Inferring whole-genome histories in large population datasets](https://doi.org/10.1038/s41588-019-0483-y) 

Jerome Kelleher, Yan Wong, Anthony W. Wohns, Chaimaa Fadil, Patrick K. Albers, Gil McVean (2019)

Nature Genetics

📍 Primary article on scalable whole-genome history inference cited by the 2024 MBE paper as relevant recent progress.

Background reference on scalable inference of genome-wide genealogical structures, illustrating progress on the ARG side without solving the geography/transmission extension.

 [Link ↗](https://doi.org/10.1038/s41588-019-0483-y) [DOI ↗](https://doi.org/10.1038/s41588-019-0483-y)

## Notes / Progress

_Work log goes here._
