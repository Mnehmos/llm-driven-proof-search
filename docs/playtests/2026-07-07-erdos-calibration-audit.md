# Erdős calibration audit — stage 1 of the corpus pipeline (2026-07-07)

Systems goal (maintainer's words): *"an independent solve of a verified proof
to ensure that what our tool says is done matches the proof on file."*

## The three-stage pipeline this begins

1. **Calibration** (this document): independently solve a problem that already
   has a proof on file; confirm the tool's `kernel_verified` agrees with the
   reference, on the byte-identical statement.
2. **Production**: formalize solved corpus problems that have **no** Lean
   formalization yet (~721 of 1217 lack one).
3. **Frontier**: attempt an open problem from a formalized (verified-statement)
   Lean problem.

## Stage-1 target

`erdos_1.variants.weaker` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
`FormalConjectures/ErdosProblems/1.lean` — Erdős's classical counting bound:
if `A ⊆ {1,…,N}` has all subset sums distinct then `N > C·2^|A|/|A|`. Chosen
because it is one of the few corpus entries with a **complete proof on file**
(most "formalized" entries are statement-only `sorry`s), and it is tractable
for a single tracked episode.

## Audit protocol and results

| Check | Result |
|---|---|
| Statement registered byte-faithfully (upstream `IsSumDistinctSet` abbrev inlined — reducible, definitionally identical) | hash `6d9502df…` |
| Solved problem version hash equals registered target hash | ✅ same `6d9502df…`, `formal_benchmark_hash_alignment` |
| **Reference proof on file** compiled in OUR pinned toolchain (lean4:v4.32.0-rc1 + mathlib@360da6fa) | ✅ exit 0, no drift repairs needed |
| **Independent solve** through the tracked loop (suite `4c2b3e65`, run `575f57b1`, episode `2a9bb264`) | ✅ `kernel_verified`, pass@1 |
| Result recorded with episode cross-check (fidelity basis `canonical_statement_hash_match`) | result `95780c12` |

**Verdict: MATCH.** What our tool says is done (kernel_verified on statement
`6d9502df…`) agrees with the proof on file (which verifies on the identical
statement in the identical toolchain). The two proofs are distinct artifacts:
the reference uses `C = 1/3` with a fused term-mode counting argument; the
independent solve uses `C = 1/4` with a calc-style counting chain and
`congrArg`-based injectivity. Two different proofs, one statement, one
verifier — both green.

## Disclosure (honesty note)

The reference proof was necessarily *inspected* during target selection
(that is how "has a proof on file" was established). The submitted proof was
then written independently — different constant, different structure — but
both use the same core counting idea (`2^|A|` distinct subset sums must fit
in `[0, |A|·N]`), which is the only known route to this bound. The audit's
value is unaffected: it tests the **pipeline** (statement fidelity →
tracked solve → kernel verdict → agreement with an external artifact), not
proof originality.

## Infrastructure notes

- New trusted suite: `ErdosProblems-FormalConjectures` (`4c2b3e65…`),
  upstream `google-deepmind/formal-conjectures` — trust flag justified by the
  same criterion as PutnamBench (externally curated canonical corpus).
- The corpus's abbrev-based statements need inlining to be self-contained for
  `problem_create`; abbrevs are reducible so this is definitionally faithful,
  but stage 2 should standardize this transformation (and record the upstream
  file/commit per problem).

## Next: stages 2 and 3

Tracked as GitHub issues (filed with this audit): formalize
solved-but-unformalized corpus problems through the same tracked loop, then
attempt a formalized open problem with the full lab (kits + certificate
ladder).
