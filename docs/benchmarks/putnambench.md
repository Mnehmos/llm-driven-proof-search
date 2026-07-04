# PutnamBench

Repository: https://github.com/trishullab/PutnamBench

This document currently covers the contamination policy for PutnamBench results
(issue #33). The full harness design (problem import shape, runner behavior,
smoke fixtures — issues #28, #29, #31, #32) will be added here as those ship.

## Why this matters

PutnamBench's own README asks that public confirmation settings not include
proof solutions, and asks that people not write formal proofs for benchmark
problems in public without first engaging with the maintainers — this is
meant to protect the benchmark corpus from contamination (e.g. by future
model training runs scraping public completed proofs). Leaderboard
submissions should be accompanied by a preprint or publication, coordinated
with the maintainers, not published as a side effect of running an
evaluation.

ChatDB's benchmark-tracking tools (`benchmark_suite_create`,
`benchmark_problem_register`, `benchmark_run_create`, `benchmark_result_record`,
`benchmark_run_observe` — see the README's MCP Tools table) and its
`proof_export` tool must make it hard to *accidentally* violate that policy,
while still fully supporting private verification, replay, and
maintainer-coordinated submissions.

## Contamination policy, as enforced in code

`proof_export`'s `format` (see `ExportMode` in `crates/chatdb-mcp/src/lib.rs`)
has two tiers:

- **Never exposes the completed proof body, regardless of any flag:**
  `public_summary`. Safe to call and share unconditionally — status, hashes,
  toolchain, obligation counts, replay/integrity metadata, and (if the
  episode's problem is linked to a tracked benchmark suite) the suite name
  and upstream problem id. No proof term, no assembled Lean source, no
  verified-module source.
- **May expose the completed proof body:** `markdown` (default), `lean`,
  `audit_archive`, `training_export`, `paper_dossier`, `maintainer_submission`.
  If the episode being exported is linked to a tracked benchmark suite (its
  problem_version's `root_statement_hash` matches a registered
  `benchmark_problems` row — the same comparison `benchmark_result_record`
  uses to bind results to episodes), calling `proof_export` in one of these
  modes requires `allow_putnambench_proof_export=true`. Without it, the call
  is rejected with an error pointing back to this document. This is a
  deliberate speed bump, not a technical impossibility — the same discipline
  used everywhere else in ChatDB: make the safe path the default path.

So: full proof artifacts (`markdown`/`lean`/`audit_archive`/`paper_dossier`)
are private-by-default for any problem tied to a benchmark suite; a public or
automated report generator should use `public_summary`, which needs no flag
and never leaks a proof body no matter what.

`maintainer_submission` mode is the same content tier as `audit_archive`
(full proof source, every attempt including failures) but explicitly labeled
as a package for private, direct communication with a benchmark suite's own
maintainers — never for unilateral public posting. If you solved a
PutnamBench problem and want to report it upstream, use this mode, gate it
with `allow_putnambench_proof_export=true`, and reach out to the PutnamBench
maintainers directly rather than publishing the artifact yourself.

## What "public" safely includes

Aggregate metrics, problem identifiers (`upstream_problem_id`, `theorem_name`),
statuses (`kernel_verified`/`certified`/`failed`/...), diagnostic categories,
Lean/Mathlib toolchain hashes, and replay status are all safe for public
disclosure — this is exactly what `benchmark_run_observe` and
`proof_export(format="public_summary")` report. None of it includes a
completed proof body.

## What this does not cover yet

- A dedicated report-generation tool that reads directly from
  `benchmark_results` (today, disclosure-safe reporting is per-episode via
  `proof_export`; a batch/CSV export across a whole run is part of #31/#32).
- The full harness design (import shape, runner, fixtures) — #28/#29/#31/#32.
