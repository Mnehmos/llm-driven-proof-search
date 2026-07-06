# Serious-math benchmark ladder (issue #5)

Seven rung classes that force the API into the shape of serious mathematics
instead of only proofs that fit a toy surface. Each rung climbs from a
`native_decide`-allowed finite sanity check up to a large-parameter theorem
where finite brute force is impossible *in principle*.

`ladder.json` is the checked-in fixture; `dossiers/rung_N_*.md` document each
rung. The ladder is driven through the real `problem_create → episode_create →
attempt_claim → episode_step` loop by the tests in
`crates/chatdb-mcp/src/lib.rs` (`test_serious_math_ladder_*`).

## Trust boundary

**All rung metadata is DESCRIPTIVE ONLY.** `proof_character`,
`native_decide_allowed`, `requires_helper_definitions`,
`requires_structural_lemma`, and `source_fidelity_status` are never consulted to
grant, infer, or gate `kernel_verified`/`certified`/fidelity status — same
discipline as the Level-4 research substrate ("metadata only: never changes
proof/fidelity/budget/benchmark state"). Each rung's `expected_status` is a gold
outcome the real kernel (or `MockGateway` as the plumbing stand-in) must
*produce*; it is asserted against, never treated as truth derived from a flag.

`source_fidelity_status` is `synthetic_plumbing` for every rung: the proofs are
well-formed and exercise the real reducer/module-assembly path, but their
genuine mathematical validity is what the optional real-Lean gated test checks —
the same honesty the PutnamBench smoke fixture applies to its canned proofs.

The `native_decide` ban on the module path is a deterministic policy pre-filter
(`crates/chatdb-core/src/lean/module.rs`, `PROHIBITED_ANYWHERE_TOKENS`), not a
metadata-driven judgement. Rungs with `native_decide_allowed=false` carry a
`native_decide_probe` the tests submit to prove the ban is *enforced*, not
merely declared.

## Failure modes exposed

| Rung | Class | native_decide | Failure mode it exposes |
|---|---|---|---|
| 1 | finite_native_decide | allowed | `native_decide` gives false comfort — passing here says nothing about structural math |
| 2 | helper_def_required | banned | `Solve` alone cannot introduce the required definition |
| 3 | bijection | banned | enumeration is the wrong tool; the involution lemma is the content |
| 4 | counting_induction | banned | a finite instance is not the theorem; induction is unavoidable |
| 5 | structural_invariant | banned | brute-forcing one value misses the invariant |
| 6 | construction_plus_lemma | banned | a one-liner is not a development (construction + lemma + application) |
| 7 | large_parameter | banned | an unbounded parameter defeats `decide` in principle — the anti-brute-force rung |
