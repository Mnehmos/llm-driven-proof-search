# Erdős #858 — credit & honest limits

## The problem

**Paul Erdős**, *Some extremal problems in combinatorial number theory*, in
*Mathematical Essays Dedicated to A. J. Macintyre*, Ohio Univ. Press, 1970,
pp. 123–133 (problem on p. 128). Catalogued as
[erdosproblems.com/858](https://www.erdosproblems.com/858) (Thomas Bloom).

## The paper we formalized from

**Przemek Chojecki**, *An exact frontier theorem and the asymptotic constant for
Erdős problem #858*, 15 April 2026 (`erdos858.pdf` in this folder). The rooted
tree / parent map `π`, the frontier antichains `A_N(K)`, the max-closure
reformulation, the sign theorem, and the prime–semiprime asymptotic analysis
yielding `α₂` and `c₂` are all his. Our formalization of §1–§2 follows his
definitions and lemma statements faithfully; the Lean *proofs* are our own
(elementary divisibility in place of his `p`-adic valuation bookkeeping).

## Sources the paper builds on (not re-verified here)

- Behrend (1935); Alexander (1966/67); Erdős–Sárközy–Szemerédi (1968) — the
  primitive-set circle of ideas.
- J. D. Lichtman, *Translated sums of primitive sets* (2022); *A proof of the
  Erdős primitive set conjecture*, Forum Math. Pi 11 (2023) e18.
- P. Kinlaw and C. Pomerance, *Lower bounds for numbers with three prime
  factors*, Integers 19 (2019) A22 — the explicit Mertens error bounds used in
  the paper's Lemma 4.3.
- G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*
  (GSM 163, AMS 2015) — Mertens' theorem.

## What this folder does and does not claim

- **Does:** three independent, pinned-kernel-verified results forming the
  paper's §1–§2 order-theoretic foundation (`⪯` is a partial order; the sandwich
  lemma; prime-child uniqueness). Every one is a real `kernel_verified` outcome
  through the tracked `proofsearch` `episode_step` path — see
  [evidence.md](evidence.md). Nothing rests on trusting the model or a paper's
  claim.
- **Does not:** verify Theorem 1.1 (`M(N) = M_fr(N)`), Theorem 1.2
  (`M(N) = (c₂+o(1))log N`), or any analytic ingredient of §4.2 or §5. It does
  not endorse or refute Chojecki's paper as a whole; it independently
  machine-checks the part that is currently within reach and honestly maps the
  rest ([THEOREM-CATALOG.md](THEOREM-CATALOG.md), [attack-plan.md](attack-plan.md)).
- **Fidelity caveat:** the registered problems carry `fidelity_status =
  attested` (an honest developer attestation, not a peer fidelity review), so
  results can reach `kernel_verified` but never `certified`. The faithfulness
  of the Lean encoding of `⪯` to the paper's `P⁻(t) > a` condition is argued in
  [evidence.md](evidence.md).

## Toolchain

`leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`,
via the `proofsearch` LLM-driven proof-search environment (Mnehmos). Formalized
by Claude (Opus 4.8) as the agent host / policy; the environment's pinned Lean
kernel is the sole authority on every "verified" claim.
