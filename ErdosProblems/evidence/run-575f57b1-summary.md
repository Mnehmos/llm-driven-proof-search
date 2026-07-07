# Benchmark run `575f57b1-335a-4c30-9914-c4bc8746aed5` — machine summary

From `benchmark_run_observe` (2026-07-07). Suite:
`ErdosProblems-FormalConjectures` (`4c2b3e65-8f42-4836-b79e-c5d378acfc35`,
trusted_canonical_source, upstream google-deepmind/formal-conjectures).
Envelope `e874bb6f` (mode `benchmark`, host Claude Code / claude-opus-4-8).

## Toolchain (server-detected, never client-supplied)

- `leanprover/lean4:v4.32.0-rc1 + mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`
- attempt_budget 3, solve_mode `submit_module_allowed`, lean_timeout 600s

## Aggregate metrics

| metric | value |
|---|---|
| problems_attempted | 2 |
| solved_count | 2 (solved_rate 1.0) |
| kernel_verified_count | 2 |
| pass_at_1_rate | **1.0** |
| average_attempts_per_result | 1.0 |
| results_by_trust_basis | `canonical_statement_hash_match: {kernel_verified: 2}` |
| verifier_wall_time_ms | 58,271 |
| mcp_action_count | 2 |

## Per-problem results

| upstream id | theorem | status | pass@ | fidelity basis | diagnostic |
|---|---|---|---|---|---|
| `erdos_1.variants.weaker` | `erdos_1_variants_weaker` | kernel_verified | 1 | canonical_statement_hash_match | calibration_audit_match_independent_solve_agrees_with_reference_proof_on_file |
| `erdos_1052.even_of_isUnitaryPerfect` | `even_of_isUnitaryPerfect` | kernel_verified | 1 | canonical_statement_hash_match | bounty_board_lane1_independent_proof_of_corpus_sorry_variant |

Cost honesty (verbatim policy fields): `cost_completeness:
total_cost_incomplete` — host-side and MCP-side monetary costs are not
instrumented and are reported as null, never fabricated as zero.

## Public summaries (proof_export, redaction marker verbatim)

Both episodes export with `proof_body_redacted: true` in `public_summary`
mode; the full bodies are published DELIBERATELY in `../proofs/` (see
`disclosure-note.md`).

- Episode `2cc1e02a` (erdos 1052): statement hash `6ea8f9fe…`, trajectory
  first/last `f322e4e8…`/`64d378d2…`, outcome KERNEL_VERIFIED.
- Episode `2a9bb264` (calibration): statement hash `6d9502df…`, trajectory
  first/last `63700549…`/`f3dba4d9…`, outcome KERNEL_VERIFIED.
