# TFBS Prediction from ChIP-seq Positives with Uncertain or Synthetic Negatives

**Status:** Unsolved  
**Importance:** Notable
**Source:** Posed by Natan Tourne et al. (2026)

## Categories

- Computational Biology
- Learning Theory
- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #27 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\Sigma_{\mathrm{DNA}}=\{A,C,G,T\}$ and fix a window length $w$ . For a transcription factor (TF) and a cellular context $c$ (for example a cell line or tissue condition), a candidate site is a genomic window $x \in \Sigma_{\mathrm{DNA}}^w$ . Let

$
B(x,c) \in \{0,1\}
$

indicate whether the TF truly binds in that window and context. Let

$
A(x,c) \in \{0,1\}
$

indicate whether the chromatin in that window is accessible to TF binding in that context.

In ideal evaluation, negatives should be accessible-but-unbound sites, that is, windows with $A(x,c)=1$ and $B(x,c)=0$ . However, when only ChIP-seq peaks are available, training data are typically constructed by labeling observed peaks as positives and treating either random genomic windows, nearby windows, other TF binding sites, or synthetic sequence perturbations such as dinucleotide-shuffled positives as negatives. Such negatives may be too easy, biologically unrealistic, or contaminated by false negatives caused by inaccessible chromatin.

### Unsolved Problem

Design a learning and evaluation framework for transcription factor binding site prediction that, using only standard ChIP-seq-style positive data and no matched accessibility assay at deployment time, produces predictors whose reported performance is calibrated against the true accessible-but-unbound target task. In particular, determine what assumptions or auxiliary modeling devices are sufficient to learn from positive-only, noisy-negative, or synthetic-negative training sets without inflating apparent performance, and whether one can obtain methods that generalize across TFs and cell lines on realistic genomic data rather than on artifactually easy negatives.

## Significance & Implications

TF binding prediction is a core problem in regulatory genomics, but much of the apparent progress in model architecture can be confounded by how negatives are chosen. If synthetic or poorly chosen negatives let a model solve the wrong problem, then benchmark gains do not translate into biologically reliable binding prediction. A principled solution would improve both training methodology and the credibility of reported performance numbers in regulatory genomics.

## Known Partial Results

- [Tourne et al. (2026)](#references) construct high-quality evaluation sets using matched ATAC-seq to identify accessible-but-unbound negatives and show that standard training-set metrics often substantially overestimate true performance.

- In their experiments, genomic sampling based on similarity to positives performs best among the tested negative-sampling strategies, whereas dinucleotide-shuffled negatives perform poorly despite being common in the literature.

- Even the best tested strategy still falls short of models trained on genuinely high-quality datasets with explicit negatives.

- The remaining open problem is therefore broader than selecting a better heuristic negative sampler: it is to build training and evaluation methods that remain valid when only standard positive ChIP-seq evidence is available.

## References

[1]

 [How negative sampling shapes the performance of transcription factor binding site prediction models](https://academic.oup.com/bioinformatics/article/42/2/btag048/8442895) 

Natan Tourne, Gaetan De Waele, Vanessa Vermeirssen, Willem Waegeman (2026)

Bioinformatics

📍 Abstract and Introduction, especially Section 1.2 'The negatives problem' and the discussion of whether synthetic and sampled negatives are representative of real genomic data.

Primary source; shows that commonly used negative-sampling choices can inflate TFBS-prediction performance and explicitly frames the representativeness of such negatives as unresolved.

 [Link ↗](https://academic.oup.com/bioinformatics/article/42/2/btag048/8442895) [DOI ↗](https://doi.org/10.1093/bioinformatics/btag048)

## Notes / Progress

_Work log goes here._
