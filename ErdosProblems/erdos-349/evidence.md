# Evidence — Erdős #349 (exists_finset_sum_two_pow)

Machine records for this problem. Run-level metrics shared with the
calibration and #1052 problems: [../shared/run-575f57b1-summary.md](../shared/run-575f57b1-summary.md).
Disclosure rationale for publishing the full proof body:
[../shared/disclosure-note.md](../shared/disclosure-note.md).

## Result row (benchmark_result_record, verbatim)

| field | value |
|---|---|
| result_id | `f6ed83a2-1f43-451b-89a2-ad4a6368fab4` |
| run / suite | `575f57b1…` / `4c2b3e65…` (ErdosProblems-FormalConjectures, trusted) |
| benchmark_problem_id | `7c0c927c-f22c-41ce-a833-8a9b04bb3911` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 |
| fidelity basis | `canonical_statement_hash_match` |
| kit_lemmas_used | `["Finset.sum_toFinset_bitIndices_two_pow"]` |
| diagnostic | `production_lane_local_corpus_scan_research_solved_sorry_theorem` |

## Episode public summary (proof_export public_summary, verbatim fields)

- episode: `844e5846-fc4b-4651-b1dd-9e0735a643ce`
- outcome: `KERNEL_VERIFIED`; `kernel_verified: true`; `certified: false`
- `proof_body_redacted: true` in summary mode; the full body is published
  deliberately in [proof/](proof/) (see the disclosure note)
- statement hash: `2328323a2b3bbeba5fa2318fbc84fd47675231f738edc38166e21687ced920ed`
- import manifest hash: `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- environment hash: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- trajectory: 3 events, first `b4591ecb…`, last `ae4c666f…`
  (chain detail: [trace/trajectory.md](trace/trajectory.md))
- timing: created 04:54:47Z → verified 04:55:59Z (one attempt, ~72s)

## Discovery method (distinct from #1052/#1)

This problem was surfaced by a **local corpus scan**, not external research:
a script grepped every `.lean` file in the local google-deepmind/formal-conjectures
clone for `@[category research solved ...]` theorems whose body is `sorry`,
scored ~691 hits by elementary-proof signals read directly from each
docstring (no web fetch), and this one scored near the top because its own
comment says outright: *"Proved by strong induction: subtract the largest
power ≤ k, recurse on the remainder."* Mathlib turned out to already contain
the sharper fact needed (`Finset.sum_toFinset_bitIndices_two_pow`, built for
the Kruskal–Katona `Finset.Colex` development), so no induction needed to be
hand-written at all — see [whitepaper.md](whitepaper.md) for the one detail
that took real effort (finding the lemma's true qualified name).
