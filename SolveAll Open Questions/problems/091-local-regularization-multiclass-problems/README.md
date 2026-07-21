# Can Local Regularization Learn All Multiclass Problems?

**Status:** Partially Resolved  
**Source:** Posed by Julian Asilis et al. (2024)

## Categories

- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #91 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix a domain $X$ , a label set $Y$ (possibly infinite), and a hypothesis class $H \subseteq Y^X$ . For a distribution $\mathcal{D}$ over $X \times Y$ and a predictor $f:X\to Y$ , define the $0$ - $1$ risk $L_{\mathcal{D}}(f)=\Pr_{(x,y)\sim \mathcal{D}}[f(x)\neq y]$ . For a sample $S=((x_1,y_1),\dots,(x_n,y_n))\in (X\times Y)^n$ , define the empirical risk $L_S(h)=\frac{1}{n}\sum_{i=1}^n \mathbf{1}[h(x_i)\neq y_i]$ and the set of sample-consistent hypotheses $H_S:=\{h\in H: L_S(h)=0\}$ . Call $\mathcal{D}$ realizable w.r.t. $H$ if there exists $h^*\in H$ with $L_{\mathcal{D}}(h^*)=0$ .

A (possibly improper) learning algorithm $A$ maps each finite sample $S$ to a predictor $A(S)\in Y^X$ . We say $A$ PAC-learns $H$ in the realizable setting if there exists a sample complexity function $m_A:(0,1)^2\to\mathbb{N}$ such that for every realizable $\mathcal{D}$ and every $\epsilon,\delta\in(0,1)$ , if $S\sim \mathcal{D}^n$ with $n\ge m_A(\epsilon,\delta)$ then

$
\Pr_{S\sim \mathcal{D}^n}\big[L_{\mathcal{D}}(A(S))\le \epsilon\big] \ge 1-\delta.
$

Let $m_H(\epsilon,\delta):=\inf_A m_A(\epsilon,\delta)$ denote the pointwise-optimal realizable PAC sample complexity over all learners for $H$ .

A local regularizer for $H$ is a function $\psi:H\times X\to \mathbb{R}_{\ge 0}$ . A learner $A$ is induced by $\psi$ if for every sample $S$ and every test point $x\in X$ ,

$
A(S)(x) \in \{h(x):\ h\in \operatorname*{argmin}_{g\in H_S} \psi(g,x)\}.
$

(Thus $\psi$ may induce multiple learners via tie-breaking.) Say that $\psi$ learns $H$ if every learner induced by $\psi$ PAC-learns $H$ .

### Unsolved Problem

 **Problem 2024.** For multiclass classification, is it true that every realizable-PAC-learnable hypothesis class $H$ can be learned by some local regularizer $\psi$ ? If yes, can one choose $\psi$ so that at least one induced learner has sample complexity matching $m_H(\epsilon,\delta)$ up to constant factors (or more permissively, up to polylogarithmic factors in $1/\epsilon$ and $1/\delta$ )?

## Significance & Implications

Local regularization is an ERM-like template: it selects, for each test point $x$ , a label among sample-consistent hypotheses by minimizing a pointwise regularizer $\psi(h,x)$ . The question is whether this restricted optimization-based mechanism is universal for realizable multiclass PAC learning, despite known phenomena unique to multiclass settings (e.g., the need for improper prediction and the use of one-inclusion-graph-based constructions in existing characterizations). A positive answer would yield a simple, uniform recipe for building learners (and potentially near-optimal learners) from an appropriate choice of $\psi$ , avoiding the explicit combinatorial machinery of known optimal learners. A negative answer would separate learnability from learnability-by-local-regularization, pinpointing when dependence on the unlabeled geometry of the sample (as in one-inclusion graph methods) is genuinely necessary and cannot be eliminated by any pointwise regularizer.

## Known Partial Results

- The COLT 2024 note formalizes local regularization via $\psi:H\times X\to\mathbb{R}_{\ge 0}$ and induced learners that, for each test point $x$ , output $h(x)$ for a sample-consistent $h\in H_S$ minimizing $\psi(h,x)$ .

- The note highlights that, unlike binary classification where ERM over $H$ attains near-optimal sample complexity when VC dimension is finite, multiclass learning can require qualitatively different (improper) learners.

- Daniely and Shalev-Shwartz (2014) show there exist realizable, PAC-learnable multiclass classes for which any optimal generic learner must be improper; in particular, ERM (and other proper templates optimizing over $H$ ) cannot be universally optimal.

- Existing multiclass learners/characterizations discussed in the note rely on orientations of one-inclusion graphs associated with $H$ , which can depend on the unlabeled sample inputs and may be infinite when $Y$ is infinite.

- Asilis et al. (2024) study a strengthened variant, unsupervised local regularization, where the regularizer may also depend on the unlabeled datapoints in the training sample; the note states this variant can learn all multiclass problems with near-optimal sample complexity, leaving open whether the unlabeled dependence can be removed.

- The note proposes a candidate counterexample class $H_\triangle$ with $X$ infinite and labels $Y=\{*\}\cup 2^X$ , defined from triples $(A,B,C)$ of finite subsets with $|A|=|B|=|C|=k$ and pairwise intersections of size $k/2$ ; each hypothesis outputs $*$ off $A\cup B\cup C$ and is constant on each of $A\cap B$ , $A\cap C$ , and $B\cap C$ with values chosen from the corresponding pair of set-labels. The class is argued to be PAC learnable by a simple default- $*$ rule, but the note conjectures symmetry may prevent any (supervised) local regularizer from selecting the natural label without effectively using unlabeled sample geometry, leading to Open Problem 2 for $H_\triangle$ .

- Jafar, Asilis, and Dughmi (COLT 2025) partly resolve the question by proving a negative result in the transductive model: some learnable multiclass problems cannot be learned transductively by any local regularizer, while the realizable PAC case remains open.

## References

[1]

 [Open Problem: Can Local Regularization Learn All Multiclass Problems?](https://proceedings.mlr.press/v247/asilis24b.html) 

Julian Asilis, Siddartha Devic, Shaddin Dughmi, Vatsal Sharan, Shang-Hua Teng (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/asilis24b.html) [2]

 [Open Problem: Can Local Regularization Learn All Multiclass Problems? (PDF)](https://proceedings.mlr.press/v247/asilis24b/asilis24b.pdf) 

Julian Asilis, Siddartha Devic, Shaddin Dughmi, Vatsal Sharan, Shang-Hua Teng (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/asilis24b/asilis24b.pdf) [3]

 [Optimal learners for multiclass problems](https://proceedings.mlr.press/v35/daniely14b.html) 

Amit Daniely, Shai Shalev-Shwartz (2014)

Conference on Learning Theory (COLT), PMLR 35

📍 PMLR

 [Link ↗](https://proceedings.mlr.press/v35/daniely14b.html) [4]

 [A Characterization of Multiclass Learnability](https://doi.org/10.1109/FOCS54457.2022.00093) 

Nataly Brukhim, Daniel Carmon, Irit Dinur, Shay Moran, Amir Yehudayoff (2022)

IEEE 63rd Annual Symposium on Foundations of Computer Science (FOCS 2022)

📍 Related work and partial progress context.

 [Link ↗](https://doi.org/10.1109/FOCS54457.2022.00093) [DOI ↗](https://doi.org/10.1109/FOCS54457.2022.00093) [arXiv ↗](https://arxiv.org/abs/2203.01550)

## Notes / Progress

_Work log goes here._
