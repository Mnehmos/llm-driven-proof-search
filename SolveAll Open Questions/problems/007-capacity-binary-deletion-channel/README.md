# Capacity of the Binary Deletion Channel

**Status:** Unsolved  
**Importance:** Major

## Categories

- Information Theory
- Theoretical Computer Science

## Origin

Listed on [SolveAll.org](https://solveall.org/problems) — a community-curated
collection of unsolved problems in the mathematical sciences. This folder mirrors
problem #7 from the site's browse listing (sorted by importance) as of 2026-07-17.
The full problem statement, references, and discussion live on the site; paste or
summarize the statement below once pulled.

## Problem Statement

### Setup

Fix a deletion probability $d\in[0,1)$ . The binary deletion channel $\mathrm{BDC}(d)$ is defined as follows: for input blocklength $n$ , the transmitter sends $X^n=(X_1,\dots,X_n)\in\{0,1\}^n$ . Independently for each $i\in\{1,\dots,n\}$ , a deletion indicator $D_i\sim\mathrm{Bernoulli}(d)$ is drawn, with $\mathbb P(D_i=1)=d$ and $\mathbb P(D_i=0)=1-d$ , and $(D_i)$ is independent of $X^n$ . The output is the random subsequence

$
Y=(X_i:\,D_i=0)\in\{0,1\}^{L_n},
$

where $L_n=\sum_{i=1}^n(1-D_i)$ is random. Thus deleted symbols are removed, undeleted symbols keep their original order, and the receiver is not told the deleted positions.

A block code of length $n$ and size $M_n$ consists of an encoder $f_n:\{1,\dots,M_n\}\to\{0,1\}^n$ and a decoder $g_n:\{0,1\}^*\to\{1,\dots,M_n\}$ , where $\{0,1\}^*=\bigcup_{\ell\ge 0}\{0,1\}^\ell$ . With uniformly distributed message $W\in\{1,\dots,M_n\}$ , average error probability is

$
P_e^{(n)}=\mathbb P\!\big[g_n(Y)\neq W\big].
$

A rate $R\ge 0$ is achievable if there exists a sequence of codes with $\lim_{n\to\infty}P_e^{(n)}=0$ and $\liminf_{n\to\infty}\frac{1}{n}\log_2 M_n\ge R$ . The Shannon capacity is

$
C(d)=\sup\{R:\,R\ \text{is achievable}\}.
$

### Unsolved Problem

Determine $C(d)$ exactly as a function of $d$ for the binary deletion channel. In particular, determine the exact asymptotic behavior of $C(d)$ as $d\to 1$ , i.e., find an explicit asymptotic equivalent $a(d)$ such that $C(d)/a(d)\to 1$ as $d\to 1$ (and, ideally, further terms of the asymptotic expansion).

## Significance & Implications

The deletion channel is one of the simplest channels whose capacity remains unknown, despite being introduced in the 1960s. Unlike the binary symmetric or binary erasure channels (whose capacities have clean formulas), the deletion channel's capacity is notoriously difficult because the receiver does not know *which* bits were deleted. This makes synchronization a fundamental challenge ( [Mitzenmacher (2009)](#references) ). [Kanoria & Montanari (2013)](#references) established small- $d$ asymptotics, and [Cheraghchi (2019)](#references) proved improved capacity upper bounds for deletion-type channels.

## Known Partial Results

- Global (all $d\in[0,1)$ ): $C(d) \le 1-d$ (standard genie-aided erasure-channel upper bound).

- Asymptotic as $d\to 0$ : [Kanoria & Montanari (2013)](#references) derive a rigorous small- $d$ expansion (including the $d\log d$ correction term).

- Global upper bounds beyond the trivial $1-d$ bound: [Cheraghchi (2019)](#references) gives improved upper bounds for deletion-type channels, including the binary deletion channel.

- As of 2019 (Cheraghchi) and subsequent survey context, the exact asymptotic equivalent of $C(d)$ as $d\to 1$ is still open.

## References

[1]

 [A survey of results for deletion channels and related synchronization channels](https://doi.org/10.1214/08-PS141) 

Michael Mitzenmacher (2009)

Probability Surveys

📍 Section 7 (upper bounds) and Open Questions (asymptotics as deletion probability goes to 0 and to 1), p. 22.

 [DOI ↗](https://doi.org/10.1214/08-PS141) [2]

 [Optimal coding for the binary deletion channel with small deletion probability](https://doi.org/10.1109/TIT.2013.2262020) 

Yashodhan Kanoria, Andrea Montanari (2013)

IEEE Transactions on Information Theory

📍 Introduction and Theorem 1: asymptotic expansion of capacity for small deletion probability ($d\to 0$).

 [DOI ↗](https://doi.org/10.1109/TIT.2013.2262020) [arXiv ↗](https://arxiv.org/abs/1104.5546) [3]

 [Capacity Upper Bounds for Deletion-type Channels](https://doi.org/10.1145/3281275) 

Mahdi Cheraghchi (2019)

Journal of the ACM

📍 Main upper-bound theorems and numerical upper bounds for the binary deletion channel (global in $d$).

 [DOI ↗](https://doi.org/10.1145/3281275) [arXiv ↗](https://arxiv.org/abs/1711.01630)

## Notes / Progress

_Work log goes here._
