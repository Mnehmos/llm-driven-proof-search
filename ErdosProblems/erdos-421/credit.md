# Credit — Erdős Problem #421

## Original mathematics

- **Erdős–Graham** (problem source, [ErGr80, p.84]) and **P. Erdős** for
  the original question.
- **J. Selfridge** (attribution via Erdős–Graham) for the density
  `1/e − ε` partial construction (Erdős Problem #786), still unformalized
  in the corpus as of this writing.
- **Przemek Chojecki**, with heavy assistance from GPT-5.x models, for the
  disputed claimed density-1 solution posted to erdosproblems.com/421.
  Publicly reviewed by **Terence Tao**, **uona**, **Nat Sothanaphan**,
  **BorisAlexeev**, and others; moderated by **Thomas Bloom**
  (erdosproblems.com maintainer). This project does not adopt or rely on
  that claim — see [whitepaper.md](whitepaper.md).
- **Castryck, Cluckers, Dittmann, Nguyen** (determinant method for uniform
  point counts), **Bilu, Tichy** and **Hajdu, Tijdeman** (separated-variable
  Diophantine classification), **Runbo Li** (arXiv:2407.05651, primes in
  almost all short intervals) — external results cited by the disputed
  proof; tracked in our dossier as unverified external citations, not
  independently re-derived by us.

## Formal statement

- **google-deepmind/formal-conjectures**, `FormalConjectures/ErdosProblems/421.lean`
  (`Erdos421.erdos_421`) and `FormalConjectures/ErdosProblems/786.lean`
  (`Erdos786.erdos_786.parts.i.selfridge`) — the corpus formal statements
  this project's `problem_create` calls are matched against (with the
  corpus's `HasDensity` abbreviation unfolded to Mathlib primitives, since
  it is not part of pinned Mathlib).

## This project's contribution

- Independent elementary construction and Lean kernel-verification (2026-07-13)
  of the density-1/4 partial result via the 2-adic-valuation + block-reindexing
  argument described in [whitepaper.md](whitepaper.md) — our own idea, not
  sourced from the forum thread.
- Independent Python empirical verification of several candidate
  constructions (the trivial identity sequence's immediate collision, the
  `4n+2` construction, a refuted naive `6n+2` generalization, and the
  forum's "prefix-stable greedy" idea's empirical density) — see
  [evidence.md](evidence.md).
- A research dossier tracking the disputed proof's known bug history and
  current unverified status, so future sessions do not need to re-derive
  the provenance of ideas from the raw forum thread.

## Attribution note

Per this project's operating doctrine: advisory metadata (dossier nodes,
candidate constructions, empirical searches, exposition) never marks
anything proved. Only the reasoning-log-tracked `episode_step` outcomes
below are kernel evidence.
