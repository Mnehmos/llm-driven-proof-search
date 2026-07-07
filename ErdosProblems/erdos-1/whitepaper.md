# Erdős Problem #1 — Distinct Subset Sums (calibration case study)

**Problem folder whitepaper — 2026-07-07**

## The problem

[erdosproblems.com/1](https://www.erdosproblems.com/1): if `A ⊆ {1,…,N}` is
a finite set of positive integers all of whose subset sums are distinct,
must `N ≫ 2^{|A|}`? **Open** since Erdős posed it; prize $500. The powers of
two show `2^{|A|}` is the right order of growth — the open part is a
matching lower bound.

This folder does not resolve the open problem. It documents the **weaker,
known bound** `N ≫ 2^{|A|}/|A|` (Erdős's classical counting argument, proved
in the corpus) and uses it as the project's **calibration case study** —
the first check that our verification pipeline's "done" signal can be
trusted at all.

## What this folder proves (kernel-verified)

**Theorem (weaker Erdős bound).** *There is a constant `C > 0` such that for
every `N` and every `A ⊆ {1,…,N}` with distinct subset sums,
`C · 2^{|A|}/|A| < N`.*

This is `erdos_1.variants.weaker` in the canonical Lean corpus
(google-deepmind/formal-conjectures), one of the few corpus entries shipped
with a **complete proof on file** rather than a `sorry`. We wrote an
**independent** proof of the identical statement and ran it through the
tracked pipeline, then compared verdicts.

## Why this problem: the calibration audit

Systems goal (maintainer's words): *"an independent solve of a verified
proof to ensure that what our tool says is done matches the proof on
file."* Protocol:

| Check | Result |
|---|---|
| Statement registered byte-faithfully (`IsSumDistinctSet` inlined — reducible, definitionally identical) | hash `6d9502df…` |
| Solved problem version hash equals registered target hash | ✅ same `6d9502df…`, `formal_benchmark_hash_alignment` |
| **Reference proof on file** compiled in our pinned toolchain (lean4:v4.32.0-rc1 + mathlib@360da6fa) | ✅ exit 0, no drift repairs needed |
| **Independent solve** through the tracked loop | ✅ `kernel_verified`, pass@1 |
| Result recorded with episode cross-check | fidelity `canonical_statement_hash_match`, result `95780c12` |

**Verdict: MATCH.** The two proofs are distinct artifacts — the reference
uses `C = 1/3` with a fused term-mode argument; ours uses `C = 1/4` with a
calc-style counting chain and `congrArg`-based injectivity. Two different
proofs, one statement, one verifier — both green. What the tool reports as
done agrees with an external artifact it did not produce.

**Disclosure.** The reference proof was necessarily *inspected* during
target selection (that is how "has a proof on file" was established). The
submitted proof was then written independently, but both use the only known
route to this bound (`2^{|A|}` subset sums must fit in `[0, |A|·N]`). The
audit's value is in the **pipeline** (statement fidelity → tracked solve →
kernel verdict → agreement with an external artifact), not proof
originality.

## Verification record

| field | value |
|---|---|
| statement | `∃ C > 0, ∀ N A, (A ⊆ Icc 1 N ∧ subset-sums injective) → N ≠ 0 → C·2^{\|A\|}/\|A\| < N` |
| statement hash | `6d9502df287501ce86c7c99563413736cec446695e5787cb87136dd2c065fcf0` |
| suite / problem | `ErdosProblems-FormalConjectures` (`4c2b3e65…`) / `c8602e7f…` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| episode / result | `2a9bb264…` / `95780c12…` — **kernel_verified, pass@1** |
| module_source_hash | `de56869c52beef3ca9b331083b7fc5f621dfa39fe267d9f9a8e3a77cf0972016` |
| toolchain | lean4:v4.32.0-rc1 + mathlib@360da6fa |

Full hash-chained ledger: [trace/trajectory.md](trace/trajectory.md).
Evidence detail: [evidence.md](evidence.md). Credit and disclosure:
[credit.md](credit.md).

## Reproduce

The exact assembled module the verifier checked is
[proof/Erdos1_variants_weaker_calibration.lean](proof/Erdos1_variants_weaker_calibration.lean)
(exported from the tracked ledger, byte-stamped by the `module_source_hash`
above) — a standalone file, ready to feed to `lake env lean`.

## Infrastructure this established

- New trusted suite `ErdosProblems-FormalConjectures`, upstream
  google-deepmind/formal-conjectures — trust flag justified by the same
  criterion as PutnamBench (externally curated canonical corpus).
- Corpus abbrevs need inlining to be self-contained for registration
  (reducible, so definitionally faithful) — the pattern every later problem
  folder in this project follows.
- This audit's pass unblocked the production work in
  [../erdos-1052/](../erdos-1052/whitepaper.md), the project's first
  from-scratch contribution to a previously-unproven corpus statement.
