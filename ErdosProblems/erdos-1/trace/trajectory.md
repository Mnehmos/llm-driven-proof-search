# Trajectory — calibration audit (episode `2a9bb264-7eb8-431f-8852-952a3e880fb4`)

Verbatim hash-chained event ledger from `trajectory_export` (2026-07-07).
The full proof body is
[`../proofs/Erdos1_variants_weaker_calibration.lean`](../proofs/Erdos1_variants_weaker_calibration.lean)
(the exported assembled module — exactly what the verifier checked).
Regenerate raw JSON with:
`trajectory_export {episode_id: "2a9bb264-7eb8-431f-8852-952a3e880fb4", allow_putnambench_proof_export: true}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `4d979256`, max_steps 6) | `63700549d7ace62e52583d63311b4d0d85717cfa0497e67dfc865fa3857f4655` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, outcome `kernel_pass`) | `196a1cc8f1236ed8a4cb2ac07adf68ce926c512057222a99c03dd022708067bf` | `63700549…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `f3dba4d99d9518770534ae24fee0a53c773d6b440aa684e36c2022abeed13fc3` | `196a1cc8…` |

Event-2 integrity fields (verbatim):

- `statement_hash`: `6d9502df287501ce86c7c99563413736cec446695e5787cb87136dd2c065fcf0`
- `module_source_hash`: `de56869c52beef3ca9b331083b7fc5f621dfa39fe267d9f9a8e3a77cf0972016`
- `declaration_manifest_hash`: `990ec1d73220a1474dc51c052dda7f72a85e8e6884a9145359663358f90d95d3`
- `lean_environment_hash`: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- `obligation_id`: `090fc49b-5bbf-4e61-b1a7-818b5181558b`
- timestamps: created 2026-07-07T02:31:08Z, committed 2026-07-07T02:32:08Z
  (one attempt, ~60s including the full Lean verification)
