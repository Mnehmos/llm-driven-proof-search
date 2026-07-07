# Evidence — Erdős #1052 (even_of_isUnitaryPerfect)

Machine records for this problem. Run-level metrics shared with the
calibration problem: [../shared/run-575f57b1-summary.md](../shared/run-575f57b1-summary.md).
Disclosure rationale for publishing the full proof body:
[../shared/disclosure-note.md](../shared/disclosure-note.md).

## Result row (benchmark_result_record, verbatim)

| field | value |
|---|---|
| result_id | `27534f5e-d6c6-4570-a0f6-7a3df805853e` |
| run / suite | `575f57b1…` / `4c2b3e65…` (ErdosProblems-FormalConjectures, trusted) |
| benchmark_problem_id | `0279379a-09fe-46a3-b730-f70f9d02005f` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 |
| fidelity basis | `canonical_statement_hash_match` |
| diagnostic | `bounty_board_lane1_independent_proof_of_corpus_sorry_variant` |

## Episode public summary (proof_export public_summary, verbatim fields)

- episode: `2cc1e02a-290b-43bd-bca4-c06d163cd413`
- outcome: `KERNEL_VERIFIED`; `kernel_verified: true`; `certified: false`
- `proof_body_redacted: true` (the redaction gate works; the body is
  published deliberately — see disclosure note)
- statement hash: `6ea8f9fe2ac827150c04fb425a963ec770d76c7cba34c7c2c2cbba7b238f3b27`
- import manifest hash: `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- environment hash: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- trajectory: 3 events, first `f322e4e8…`, last `64d378d2…`
  (chain detail: [trace/trajectory.md](trace/trajectory.md))
- timing: created 03:20:04Z → verified 03:22:58Z (one attempt, ~2m54s
  including full Lean verification)

## Cross-check evidence (reference non-portability)

Attempted replay of the corpus-linked AlphaProof proof under our pinned
toolchain fails: it references the custom tactic `valid` (a
formal-conjectures `Util` macro absent from Mathlib) and era-specific
syntax. Grep evidence: `valid` occurs at lines 49 and 66 of the fork's
`1052.lean`; no such tactic exists in the pinned Mathlib snapshot.
