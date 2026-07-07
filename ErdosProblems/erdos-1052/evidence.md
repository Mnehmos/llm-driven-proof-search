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

## New work (this session) — local kernel verification, not yet tracked

The four results described in [whitepaper.md](whitepaper.md) (`sigmaStar_mul_of_coprime`,
`isUnitaryPerfect_87360`, `isUnitaryPerfect_wall`, `omega_odd_le_two_adic_add_one`)
are verified by direct `lake env lean` compilation of
[proof/Erdos1052_sigmaStar_and_bounds.lean](proof/Erdos1052_sigmaStar_and_bounds.lean)
and the living copy `lean-checker/LeanChecker/Erdos/Erdos1052.lean` — both compile
with zero errors (two harmless library-deprecation warnings only). These have **not**
been submitted through the tracked MCP episode pipeline yet (no `benchmark_problem_id`,
episode, or `result_id` to report) — that is the natural next step to bring them to
the same audit standard as `even_of_isUnitaryPerfect` above.

Reproduce:
```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1052.lean
```

## Literature verification (this session)

Checked via web search, not assumed from memory:
- Subbarao & Warren, "Unitary perfect numbers," Canad. Math. Bull. 9 (1966) — original
  source for `even_of_isUnitaryPerfect`, confirmed to match our formalized statement.
- Wall, "New unitary perfect numbers have at least nine odd components," Fibonacci
  Quarterly 26(4) (1988) — confirmed genuine via MR 0967649 and Zbl 0657.10003
  (legitimate Mathematical Reviews / Zentralblatt identifiers). Full proof text not
  accessible (pre-digital print journal); only the theorem statement is used here,
  not reproduced.
- A 2026 arXiv preprint found while searching ("Bounded-box reductions in the
  Subbarao–Warren problem," arXiv:2605.20475) was read in full and assessed as very
  likely AI-fabricated: invented "3-Higgs prime" terminology beyond the real, much
  narrower "Higgs prime" concept, zero independent footprint for the named author,
  and suspiciously precise unverifiable computational claims (exact runtimes,
  hyper-specific counts) wrapped around genuine citations (Zsigmondy, Ford, Wall,
  Graham) as camouflage. Discarded; not used for anything in this folder.
