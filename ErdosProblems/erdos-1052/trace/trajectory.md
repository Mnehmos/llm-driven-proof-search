# Trajectory — Erdős #1052 variant (episode `2cc1e02a-290b-43bd-bca4-c06d163cd413`)

Verbatim hash-chained event ledger from `trajectory_export` (2026-07-07).
The full `payload.action.root_theorem.proof_term` is byte-identical to
[`../proofs/Erdos1052_even_of_isUnitaryPerfect.lean`](../proofs/Erdos1052_even_of_isUnitaryPerfect.lean)'s
proof body (content-addressed below by `module_source_hash`); regenerate the
raw JSON with:
`trajectory_export {episode_id: "2cc1e02a-290b-43bd-bca4-c06d163cd413", allow_putnambench_proof_export: true}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `11c1f6e7`, max_steps 6) | `f322e4e8c4dc93f6eb0b1751bafaf765f6a1902bae8f14359860693e64ec0ec3` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, outcome `kernel_pass`) | `39df690ed34473817c9fd4740491c667a5df91dfc16ed1b0673272093481be71` | `f322e4e8…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `64d378d25cdfb06330ed3fbdeadc9c0545151631441703799dd0b42f74587609` | `39df690e…` |

Event-2 integrity fields (verbatim):

- `statement_hash`: `6ea8f9fe2ac827150c04fb425a963ec770d76c7cba34c7c2c2cbba7b238f3b27`
- `module_source_hash`: `7d29ed5d2d8a8a1157d4c15262fe0da5137970c105c1a8788015f2ebeb567944`
- `declaration_manifest_hash`: `5a80d7429076f20a3cf9f8499d4c3e4b599905de497bc9a9e430a64c9ecbbb26`
- `lean_environment_hash`: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- `obligation_id`: `238474fb-5d11-401c-adb3-9fa4211d80f8`
- timestamps: created 2026-07-07T03:20:04Z, committed 2026-07-07T03:22:58Z
  (one attempt, ~2m54s including the full Lean verification)
