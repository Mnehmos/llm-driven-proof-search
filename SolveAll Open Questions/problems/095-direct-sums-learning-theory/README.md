# Direct Sums in Learning Theory

**Status:** Unsolved  
**Source:** Posed by Steve Hanneke et al. (2024)

## Categories

- Learning Theory

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #95 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Let $X$ be an instance space and $Y$ a (finite or infinite) label set. For an integer $k\ge 1$ , write $\binom{Y}{k}=\{T\subseteq Y:|T|=k\}$ . A $k$ -list hypothesis is a function $h:X\to \binom{Y}{k}$ , with $0$ - $1$ list loss on an example $(x,y)\in X\times Y$ given by $\ell(h,(x,y))=\mathbf{1}[y\notin h(x)]$ . For a distribution $D$ over $X\times Y$ , define population loss $L_D(h)=\mathbb{E}_{(x,y)\sim D}[\ell(h,(x,y))]$ . For an i.i.d. sample $S=((x_1,y_1),\ldots,(x_n,y_n))\sim D^n$ , define empirical loss $L_S(h)=\frac1n\sum_{i=1}^n \mathbf{1}[y_i\notin h(x_i)]$ .

A (possibly improper) $k$ -list learning rule is a map $A:(X\times Y)^*\to (\binom{Y}{k})^X$ . Its expected error at sample size $n$ on $D$ is

$
\varepsilon_n(D\mid A)=\mathbb{E}_{S\sim D^n}[L_D(A(S))].
$

A distribution $D$ is realizable by a (standard, $1$ -list) concept class $\mathcal{C}\subseteq Y^X$ if there exists $c\in\mathcal{C}$ with $\Pr_{(x,y)\sim D}[y=c(x)]=1$ . The (realizable) PAC learning curve of $\mathcal{C}$ is

$
\varepsilon(n\mid\mathcal{C})=\inf_A\sup_{D\ \mathrm{realizable\ by}\ \mathcal{C}}\varepsilon_n(D\mid A),
$

where the infimum ranges over all $1$ -list learning rules $A$ . For a fixed marginal distribution $\mathcal{D}$ over $X$ , define $\mathcal{D}_c$ by $x\sim\mathcal{D}$ and $y=c(x)$ , and the fixed-marginal learning curve

$
\varepsilon(n\mid\mathcal{D},\mathcal{C})=\inf_A\sup_{c\in\mathcal{C}}\varepsilon_n(\mathcal{D}_c\mid A).
$

For concept classes $\mathcal{C}_1\subseteq Y_1^{X_1}$ and $\mathcal{C}_2\subseteq Y_2^{X_2}$ , define their product (direct sum) class $\mathcal{C}_1\otimes\mathcal{C}_2\subseteq (Y_1\times Y_2)^{(X_1\times X_2)}$ by

$
\mathcal{C}_1\otimes\mathcal{C}_2=\{(x_1,x_2)\mapsto (c_1(x_1),c_2(x_2)) : c_1\in\mathcal{C}_1,\ c_2\in\mathcal{C}_2\}.
$

For $r\in\mathbb{N}$ , write $\mathcal{C}^r=\mathcal{C}\otimes\cdots\otimes\mathcal{C}$ ( $r$ times). If $\mathcal{D}$ is a distribution on $X$ , write $\mathcal{D}^r$ for the product distribution on $X^r$ .

### Unsolved Problem

Whether joint learning on product classes can beat the naive linear direct-sum bound, and to characterize how key learnability quantities behave under $\otimes$ , in the following concrete forms.

- 

Realizable direct-sum (worst-case distributions): For every $\mathcal{C}$ and $r\ge 2$ , one has $\varepsilon(n\mid\mathcal{C}^r)\le r\,\varepsilon(n\mid\mathcal{C})$ . Does there exist $\mathcal{C}$ and $r\ge 2$ such that $\varepsilon(n\mid\mathcal{C}^r)=o(r\,\varepsilon(n\mid\mathcal{C}))$ as $n\to\infty$ ?

- 

Realizable direct-sum (fixed marginal): For every $\mathcal{C}$ , $\mathcal{D}$ , and $r\ge 2$ , one has $\varepsilon(n\mid\mathcal{D}^r,\mathcal{C}^r)\le r\,\varepsilon(n\mid\mathcal{D},\mathcal{C})$ . Does there exist $(\mathcal{C},\mathcal{D},r)$ such that $\varepsilon(n\mid\mathcal{D}^r,\mathcal{C}^r)=o(r\,\varepsilon(n\mid\mathcal{D},\mathcal{C}))$ as $n\to\infty$ ?

- 

Uniform convergence under products: With

$
\varepsilon_{\mathrm{UC}}(n\mid\mathcal{C})=\sup_D\ \mathbb{E}_{S\sim D^n}\Big[\sup_{h\in\mathcal{C}}\big|L_D(h)-L_S(h)\big|\Big],
$

determine the dependence of $\varepsilon_{\mathrm{UC}}(n\mid\mathcal{C}^r)$ on $r$ and on $\varepsilon_{\mathrm{UC}}(n\mid\mathcal{C})$ .

- Agnostic direct sums: With

$
\varepsilon_{\mathrm{agn}}(n\mid\mathcal{C})=\inf_A\sup_D\Big(\mathbb{E}_{S\sim D^n}[L_D(A(S))]-\inf_{c\in\mathcal{C}}L_D(c)\Big),
$

determine the dependence of $\varepsilon_{\mathrm{agn}}(n\mid\mathcal{C}^r)$ on $r$ and on $\varepsilon_{\mathrm{agn}}(n\mid\mathcal{C})$ .

- 

Minimal list size under products: For a standard class $\mathcal{C}\subseteq Y^X$ , let $K(\mathcal{C})\in\mathbb{N}\cup\{\infty\}$ be the minimal $k$ such that $\mathcal{C}$ is realizable $k$ -list PAC learnable (or $\infty$ if no such $k$ exists). Given $\mathcal{C}_1,\mathcal{C}_2$ , determine tight bounds on $K(\mathcal{C}_1\otimes\mathcal{C}_2)$ as a function of $K(\mathcal{C}_1)$ and $K(\mathcal{C}_2)$ .

- 

Compressibility and products: A finite-size $k$ -list sample compression scheme for $\mathcal{C}$ consists of a compressor and reconstructor such that for every finite labeled sample $S$ realizable by $\mathcal{C}$ , the reconstructor outputs a $k$ -list hypothesis $h$ consistent with $S$ (i.e. $y\in h(x)$ for all $(x,y)\in S$ ) from a bounded-size message produced by the compressor. Let $K_{\mathrm{comp}}(\mathcal{C})$ be the minimal $k$ such that $\mathcal{C}$ is $k$ -list compressible. Given $\mathcal{C}_1,\mathcal{C}_2$ , determine (or tightly bound) the minimal $k$ for which $\mathcal{C}_1\otimes\mathcal{C}_2$ is realizable $k$ -list PAC learnable as a function of $K_{\mathrm{comp}}(\mathcal{C}_1)$ and $K_{\mathrm{comp}}(\mathcal{C}_2)$ .

## Significance & Implications

Direct-sum questions in learning theory ask whether learning $r$ labeled prediction problems that factor across coordinates (i.e. a product class $\mathcal{C}^r$ ) necessarily costs Theta( $r$ ) times the samples needed for one task, or whether joint learning can provably achieve a sublinear-in- $r$ improvement in worst-case expected excess error. A sharp answer would pin down when multitask/product structure only yields the trivial union-bound scaling versus when it yields genuine sample reuse, and it would also clarify how foundational quantities (realizable and agnostic learning curves, uniform convergence rates, and minimal list size/compressibility parameters) behave under forming direct-sum/product concept classes.

## Known Partial Results

- Trivial direct-sum upper bounds hold for learning curves: for every $\mathcal{C}$ and $r\ge 2$ , $\varepsilon(n\mid\mathcal{C}^r)\le r\,\varepsilon(n\mid\mathcal{C})$ ; and for every fixed marginal $\mathcal{D}$ , $\varepsilon(n\mid\mathcal{D}^r,\mathcal{C}^r)\le r\,\varepsilon(n\mid\mathcal{D},\mathcal{C})$ .

- For minimal list size, the COLT 2024 note states general multiplicative-type bounds for any classes $\mathcal{F},\mathcal{G}$ :

$
(K(\mathcal{F})-1)(K(\mathcal{G})-1)\le K(\mathcal{F}\otimes\mathcal{G})\le K(\mathcal{F})\,K(\mathcal{G}).
$

- For specific multiclass dimensions, the note records partial product rules: for Natarajan dimension $d_N$ ,

$
d_N(\mathcal{F})+d_N(\mathcal{G})-2\le d_N(\mathcal{F}\otimes\mathcal{G})\le d_N(\mathcal{F})+d_N(\mathcal{G}),
$

and for Littlestone dimension $\mathrm{LS}$ it records additivity $\mathrm{LS}(\mathcal{F}\otimes\mathcal{G})=\mathrm{LS}(\mathcal{F})+\mathrm{LS}(\mathcal{G})$ .

- Using list Daniely-Shwartz (DS) dimension inequalities as stated in the note, non-learnability can tensorize: if $\mathcal{F}$ is not $k$ -list learnable and $\mathcal{G}$ is not $k'$ -list learnable, then $\mathcal{F}\otimes\mathcal{G}$ is not $kk'$ -list learnable.

- The note highlights a route to linear-in- $r$ lower bounds for realizable direct sums via DS dimension: it states linear growth of $\mathrm{DS}_1(\mathcal{C}^r)$ in $r$ and relates this (via known DS-based lower bounds on realizable learning curves) to linear-in- $r$ lower bounds on $\varepsilon(n\mid\mathcal{C}^r)$ up to constants and $1/n$ scaling, pointing to the importance of pinning down the tight relationship between $\varepsilon(n\mid\mathcal{C})$ and $\mathrm{DS}_1(\mathcal{C})/n$ .

- For compression versus learnability, the note records that $k$ -list compression can be strictly stronger than $k$ -list learnability (i.e. there exist $2$ -list learnable classes with no finite $2$ -list compression scheme), motivating the open question about how $\otimes$ interacts with compressibility-based parameters.

## References

[1]

 [Open problem: Direct Sums in Learning Theory](https://proceedings.mlr.press/v247/hanneke24c.html) 

Steve Hanneke, Shay Moran, Waknine Tom (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Open-problem note in COLT proceedings.

 [Link ↗](https://proceedings.mlr.press/v247/hanneke24c.html) [2]

 [Open problem: Direct Sums in Learning Theory (PDF)](https://proceedings.mlr.press/v247/hanneke24c/hanneke24c.pdf) 

Steve Hanneke, Shay Moran, Waknine Tom (2024)

Conference on Learning Theory (COLT), PMLR 247

📍 Proceedings PDF.

 [Link ↗](https://proceedings.mlr.press/v247/hanneke24c/hanneke24c.pdf)

## Notes / Progress

_Work log goes here._
