# Serious-math benchmark ladder (issue #5)

A checked-in ladder of seven rung classes that push the environment past
toy-surface proofs toward the shape of serious mathematics. The fixture lives at
[`benchmarks/serious_math_ladder/ladder.json`](../../benchmarks/serious_math_ladder/ladder.json);
per-rung write-ups and the failure-mode table are under
[`benchmarks/serious_math_ladder/`](../../benchmarks/serious_math_ladder/).

## Rung taxonomy

| Rung | Slug | Shape | native_decide | Character |
|---|---|---|---|---|
| 1 | finite_native_decide | single theorem | allowed | computational |
| 2 | helper_def_required | module | banned | computational_with_construction |
| 3 | bijection | module | banned | structural |
| 4 | counting_induction | module | banned | structural |
| 5 | structural_invariant | module | banned | structural |
| 6 | construction_plus_lemma | module | banned | computational_with_construction |
| 7 | large_parameter | single theorem | banned | structural |

Each rung carries an `allowed_tactics` list, boolean
`requires_helper_definitions` / `requires_structural_lemma`, an
`expected_artifact_shape`, a `proof_character`, and a `source_fidelity_status`,
plus a gold `TypedAction` and an `expected_status`.

## Test wiring

`ladder.json` is embedded via `include_str!` in `crates/proofsearch-mcp/src/lib.rs`
and driven by three deterministic tests (no real Lean required, `MockGateway`):

- `test_serious_math_ladder_metadata_is_complete_and_covers_required_rungs` —
  the fixture has all seven rungs with complete metadata, at least one
  helper-definition module rung and at least one `native_decide`-banned rung,
  and every rung's dossier file exists and is non-empty.
- `test_serious_math_ladder_gold_artifacts_produce_expected_status` — each gold
  artifact is driven through the real `episode_step` reducer and produces its
  fixture's `expected_status`.
- `test_serious_math_ladder_native_decide_disallow_is_enforced_not_just_declared`
  — each `native_decide`-banned rung's probe (a `SubmitModule` whose proof
  contains `native_decide`) is rejected as a prohibited construct, proving the
  ban is enforced by `lean/module.rs`, not merely a JSON flag.

An optional real-Lean gated test can re-run the gold artifacts through
`RealLeanGateway` so their mathematical content is genuinely kernel-checked.

## Trust boundary

All rung metadata is **descriptive only** and is never consulted to grant or
gate proof/fidelity status (same discipline as the Level-4 research substrate).
`expected_status` is a gold outcome to assert against, not a truth derived from
metadata. See [`benchmarks/serious_math_ladder/README.md`](../../benchmarks/serious_math_ladder/README.md).
