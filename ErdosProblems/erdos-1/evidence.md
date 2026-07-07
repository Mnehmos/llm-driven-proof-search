# Evidence — Erdős #1 weaker variant (calibration audit)

Machine records for this problem. Run-level metrics shared:
[../shared/run-575f57b1-summary.md](../shared/run-575f57b1-summary.md).
Disclosure rationale: [../shared/disclosure-note.md](../shared/disclosure-note.md).

## Result row (benchmark_result_record, verbatim)

| field | value |
|---|---|
| result_id | `95780c12-4388-4ca5-be10-101bdde0256f` |
| run / suite | `575f57b1…` / `4c2b3e65…` (ErdosProblems-FormalConjectures, trusted) |
| benchmark_problem_id | `c8602e7f-9d9b-4a65-9a61-d69d7848dec9` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 |
| fidelity basis | `canonical_statement_hash_match` |
| diagnostic | `calibration_audit_match_independent_solve_agrees_with_reference_proof_on_file` |

## Episode public summary (proof_export public_summary, verbatim fields)

- episode: `2a9bb264-7eb8-431f-8852-952a3e880fb4`
- outcome: `KERNEL_VERIFIED`; `proof_body_redacted: true` in summary mode
- statement hash: `6d9502df287501ce86c7c99563413736cec446695e5787cb87136dd2c065fcf0`
- import manifest hash: `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- environment hash: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- trajectory: 3 events, first `63700549…`, last `f3dba4d9…`
  (chain detail: [trace/trajectory.md](trace/trajectory.md))
- timing: created 02:31:08Z → verified 02:32:08Z (one attempt, ~60s)

## The audit comparison (what this evidence establishes)

Same statement hash on the registered corpus target and the solved problem
version; the corpus's own reference proof compiles unmodified in this
toolchain; our independently written proof reaches `kernel_verified` through
the tracked loop. **Two proof artifacts, one statement, one verifier — both
green.** Full protocol and verdict: [whitepaper.md](whitepaper.md).
