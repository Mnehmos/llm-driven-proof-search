# Out-of-Distribution Generalization for TCR-pMHC Binding Prediction

**Status:** Unsolved  
**Importance:** Notable
**Source:** Posed by Yang Deng et al. (2026)

## Categories

- Computational Biology
- Learning Theory
- Mathematical Statistics

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #22 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $\Sigma_{\mathrm{aa}}$ denote the amino-acid alphabet. In the TCR-pMHC prediction task reviewed by Deng et al. (2026), one input object is a T-cell receptor (TCR), one is an antigen peptide, and one is a major histocompatibility complex (MHC) allele presenting that peptide.

Let $\mathcal{T}$ be a set of TCR descriptors. Each $t \in \mathcal{T}$ represents the sequence features used for one receptor clonotype, typically one or both CDR3 amino-acid chains (often the paired $\alpha$ / $\beta$ chains, or at minimum the $\beta$ -chain CDR3 sequence), together with any optional gene annotations used by the predictor. Let $\mathcal{P} \subseteq \Sigma_{\mathrm{aa}}^{\ast}$ be the set of antigen peptide sequences (epitopes). Let $\mathcal{M}$ be the set of MHC allele identities, such as HLA alleles in humans. For $(p,m) \in \mathcal{P} \times \mathcal{M}$ , write $(p,m)$ for the peptide-MHC complex, abbreviated pMHC.

A labeled example is a quadruple $(t,p,m,y) \in \mathcal{T} \times \mathcal{P} \times \mathcal{M} \times \{0,1\}$ , where $y=1$ means experimentally supported recognition or binding of receptor $t$ to the complex $(p,m)$ and $y=0$ means nonbinding or nonrecognition under the data-generation protocol.

Suppose training data

$
\mathcal{D}_{\mathrm{train}}=\{(T_i,P_i,M_i,Y_i)\}_{i=1}^n
$

are drawn from a distribution $D_{\mathrm{train}}$ whose support is concentrated on a finite collection of observed epitopes, MHC alleles, and repertoire contexts. Let $f_n:\mathcal{T} \times \mathcal{P} \times \mathcal{M} \to [0,1]$ be a computational predictor trained on $\mathcal{D}_{\mathrm{train}}$ .

To model the hardest generalization regime emphasized in recent benchmarks, consider an out-of-distribution family $D_{\mathrm{ood}}$ whose peptide support is disjoint from the training epitopes, or consists of mutational variants of held-out epitopes, and may also shift the MHC distribution or the TCR repertoire background. Evaluate predictors by ranking or probabilistic loss on $D_{\mathrm{ood}}$ , for example AUROC, AUPRC, or expected log loss.

### Unsolved Problem

Determine whether there exist computationally feasible learning frameworks that achieve genuinely nontrivial generalization from $D_{\mathrm{train}}$ to these held-out-epitope or epitope-variant distributions at realistic biological scale. In particular, characterize what extra structure is necessary and sufficient for such generalization, such as 3D complex information, repertoire context, multi-omics covariates, or mechanistic constraints, and whether one can move from weak out-of-distribution scoring to reliable prediction and eventually de novo TCR design for novel antigens.

## Significance & Implications

TCR-pMHC recognition sits at the core of cancer immunotherapy, infectious-disease vaccinology, and personalized mRNA vaccine design. Strong in-distribution benchmarks are no longer enough: the hard practical regime is recognition of previously unseen or slightly mutated antigens. A mathematically grounded understanding of when out-of-distribution generalization is possible would clarify whether current sequence-only pipelines are fundamentally limited or merely data-limited, and would shape the next generation of immunoinformatics models.

## Known Partial Results

- [Deng et al. (2026)](#references) benchmark 18 state-of-the-art TCR-pMHC predictors and report only marginal absolute gains on challenging out-of-distribution unseen-epitope-variant datasets.

- The same review argues that current sequence-centric pipelines are hitting a structural limit and highlights enhanced structural modeling, multi-omics integration, and generative modeling as the leading routes forward.

- The field has therefore identified the right empirical failure mode, but not yet a theory or method class that reliably closes the held-out-epitope generalization gap.

## References

[1]

 [AI-driven computational methods and benchmarking for T-cell antigen identification](https://academic.oup.com/bib/article/27/2/bbag123/8526139) 

Yang Deng, Jinhao Que, Guangfu Xue, Yideng Cai, Wenyi Yang, Yilin Wang, Yi Hui, Zuxiang Wang, Yi Lin, Wenyang Zhou, Zhaochun Xu, Qinghua Jiang, Haoxiu Sun (2026)

Briefings in Bioinformatics

📍 Abstract and concluding highlights: benchmark on unseen epitope-variant datasets shows a persistent generalization gap and motivates enhanced structural modeling, multi-omics integration, and generative design.

Primary source and recent status review; includes a standardized benchmark of 18 TCR-pMHC predictors and an explicit out-of-distribution generalization warning.

 [Link ↗](https://academic.oup.com/bib/article/27/2/bbag123/8526139) [DOI ↗](https://doi.org/10.1093/bib/bbag123)

## Notes / Progress

_Work log goes here._
