# PutnamBench status: 8/12, and what the remaining gaps actually are

**Date:** 2026-07-06. A reviewer's map of where the 12-problem PutnamBench
sample stands after the two 2026-07-06 playtest runs and the issue work they
produced. Full run reports: `2026-07-05-putnam-genuine-attempt.md` (run
`8942c216`, 6/12) and `2026-07-06-putnam-retry-six.md` (run `76619de7`, +2).
No proof bodies are published here or in those reports; complete formal
proofs live only in the private ledger (`proofsearch.db`) and its private audit
exports, per the PutnamBench contamination policy.

## The headline numbers

- **8/12 solved**, kernel-verified against the pinned toolchain
  (`lean4:v4.32.0-rc1 + mathlib@360da6fa…`), all through the tracked
  `episode_step` loop. Baseline was 1/12 (2026-07-04, placeholder attempts).
- **0 remaining `formalization_gap`** statuses. Every environment blocker
  found in the first genuine run (lost `open`/scoped context, noncomputable
  solution defs, missing observe/trust tools, cold-cache import timeout) was
  fixed in #61–#67 and acceptance-tested by the retry run: two former gaps
  became pass@1/pass@3 kernel-verified proofs, and the other two now
  elaborate correctly and fail only on mathematics.
- **4 remaining problems are domain formalization projects**, not iteration
  targets: putnam_1965_a1 (synthetic-geometry configuration analysis),
  putnam_1962_a3 (cevian/Routh area machinery), putnam_1970_a1 (power-series
  coefficient uniqueness plumbing), putnam_1962_a1 (finite convex-position
  combinatorics). Each needs bridge infrastructure that pinned Mathlib does
  not currently provide in usable form.

## What the issue work delivered

- **#61–#67** (landed first, v0.3.24): the environment fixes — MCP tools
  capability advertisement, `open`-directive import manifests, `noncomputable
  section` module wrapping, the benchmark-statement shadow guard,
  suite/problem observe + audited trust admin, import-validation
  timeout/caching, inline-`by` documentation.
- **#68–#71, #76** (v0.3.25): benchmark **reporting hardening** — stale
  module receipts now dominate export status (no clean CERTIFIED over a
  source-hash mismatch), tracked-benchmark training eligibility is
  quarantined by default and fidelity labels carry reviewer provenance,
  every export surface has a machine-checkable `proof_body_redacted` marker,
  the retry's tactic-transport hazards are documented in `readme_first`, and
  failed results can carry a structured formalization-gap taxonomy that
  `benchmark_run_observe` aggregates alongside trust-basis grouping.
- **#72–#75** (v0.3.25, `lean-checker/LeanChecker/Kits/`): **minimum
  reusable math kits** toward the four remaining problems — power-series
  coefficient uniqueness (`PowerSeriesKit`), affine/determinant area
  scaffolding (`AffineAreaKit`), isosceles/betweenness angle bridges
  (`GeometryAngleKit`), and finite convex-position criteria
  (`FiniteConvexityKit`). Each compiles under the pinned toolchain, ships
  small fixtures, and documents its route to the target problem. None of
  them claims to close a benchmark problem yet — the stretch goals are
  explicitly staged.

## Suggested next step

Putnam 1965 A1 via `GeometryAngleKit` (#74): the kit already reduces the
diagram to two scalar angle equations whose linear solution is `π/15`; the
remaining work is the betweenness case analysis — the shortest path from new
infrastructure to another benchmark-aligned win. Difficulty order thereafter:
#73 (1962_a3), #72 (1970_a1), #75 (1962_a1).
