# Credit & disclosure — Erdős #647

> Living document; last updated 2026-07-13.

## Mathematics

- **Problem:** Erdős #647 (Erdős–Selfridge, ~1979): is there `n > 24` with
  `max_{m<n}(m + τ(m)) ≤ n + 2`? **Open.** Catalogued by Thomas Bloom at
  [erdosproblems.com/647](https://www.erdosproblems.com/647).
- **Scott Hughes** ([erdos647-proof-chain](https://github.com/scottdhughes/erdos647-proof-chain)):
  the Stage-1 modular reduction (2520·N, 41 residues mod 46189) and its Lean
  formalization; the 6.16×10¹⁷ finite-range certificate; the
  direct-full-value and single-overlap closure techniques; **Theorem 2**
  (prime-chain reduction — *statement and paper sketch*; the Lean
  formalization in this folder is ours); the **all-avoid obstruction**; and,
  with Kitamura, the Brun-sieve density program (`≪ x/(log x)⁷`).
- **Kenta Kitamura**: necessary conditions (e.g. `(n−3)/3` prime),
  co-development of the prime-7-tuple/Brun-sieve direction.
- **Patrik Idén**: computational verification to 10¹² (Zenodo-deposited),
  `D(n)` depth records, gap-growth analysis.
- Both Hughes and Kitamura publicly disclose AI assistance in their own
  posted work; this project matches that community norm (see below).

## This folder's contributions

- Independent re-derivation and kernel-verification of the modular
  reduction under a second verifier setup, with a **tighter base sieve**
  (48 survivors vs 96) and a **bridging-closure layer** deriving every
  sieve row from classification theorems (so the reduction is proven, not
  scanned).
- Fresh Lean proofs (not ports) of four residue closures, reaching Hughes's
  exact 41-class frontier independently.
- **48 previously-unrecorded sub-AP congruence closures** from an original
  search (same species as the 6549 inside Hughes's certificate; frozen once
  their structural limits were clear).
- **First machine-checked proof of Hughes's Theorem 2** (three
  kernel-verified stages) — to our knowledge; we'd welcome a correction.
- An **extension of the all-avoid negative result** to Theorem-2 chain
  forms (informal argument recorded in the whitepaper; formalizing it is an
  open task).
- A kernel-verified **exact Mertens-style identity** (`∑ 1/p` in terms of
  Chebyshev θ via Abel summation) — the first brick of a quantitative
  Mertens theorem that Mathlib currently lacks, aimed at the density-bound
  program.

## Tools & authorship

- Proofs authored by an LLM agent (Claude, Anthropic) operating in a
  verifier-gated proof-search environment built by **Mnehmos** (this
  repository); human direction and review by Mnehmos throughout.
- **Verified solely by the Lean 4 kernel + pinned Mathlib.** No claim in
  this folder rests on trusting the model or the human. Where we made
  errors mid-campaign (an initially wrong "Mathlib has no sieve theory"
  verdict; a stale automation loop), the whitepaper records them.

## Honest limits

- **The problem remains open.** Nothing here is a resolution, and the
  known exclusion bound (6.16×10¹⁷) is Hughes's computation, not ours
  (we independently replicated only to 5×10⁹).
- Theorem 2's mathematics is Hughes's; our contribution is the rigorous
  reconstruction of the proof from his sketch and its formalization.
- The density-bound program (Theorems 3–4) is Hughes–Kitamura mathematics;
  our Layer A work formalizes *supporting* analytic infrastructure and has
  not yet reached their bound.
- The proof snapshots await an independent local-toolchain replay (see
  evidence.md caveat).
