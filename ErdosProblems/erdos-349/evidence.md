# Evidence — Erdős #349 (seven-theorem cluster, integer characterization COMPLETE)

Machine records for this problem. The older run-level snapshot shared with
the calibration and #1052 problems is
[../shared/run-575f57b1-summary.md](../shared/run-575f57b1-summary.md); it
predates the #349 result rows below, so the per-theorem rows in this file are
the current #349 evidence.
Disclosure rationale for publishing the full proof body:
[../shared/disclosure-note.md](../shared/disclosure-note.md).

This folder now covers **seven** kernel-verified theorems from the same
corpus file, all registered against suite `4c2b3e65…`
(ErdosProblems-FormalConjectures) and recorded against the same run
`575f57b1…`. The first (`exists_finset_sum_two_pow`) was proved in an
earlier session; four more were proved together in one continuous session in
direct response to the maintainer's objection that treating
`exists_finset_sum_two_pow` as disconnected "scaffolding" was wrong. The
sixth, `alpha_gt_two_not_isGoodPair`, was proved in the dedicated follow-up
session promised by the attack plan. The seventh, `integer_isGoodPair_iff`,
assembles the four component lemmas via case split into the full
characterization — **the cluster's culminating theorem, now complete**. See
[whitepaper.md](whitepaper.md) for the cluster narrative and
[attack-plan.md](attack-plan.md) (all milestones now DONE).

## Result row 1/6 — exists_finset_sum_two_pow (benchmark_result_record, verbatim)

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

## Result row 2/6 — int_coeff_ge_two_not_isGoodPair

| field | value |
|---|---|
| result_id | `ac1fe599-0b43-4980-b559-45940c5f91d6` |
| run / suite | `575f57b1…` / `4c2b3e65…` |
| benchmark_problem_id | `5e6b7098-1b62-4f20-a8eb-21c011c792e0` |
| problem_version_id | `ae483dd8-edd6-4773-9301-b1b487276935` |
| episode | `f447f17e-18d7-48fd-b1ef-1ee8aa7bb9c8` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 (on a *fresh* episode — see the format note below) |
| statement hash | `444d78b6081aa380d9260f96fb8501f05347817736672fdc2f0a9a08f769747f` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| assembly role | one of `integer_isGoodPair_iff`'s four pieces: integer `t ≥ 2` fails |

**Format note (honest disclosure).** A *prior* episode on this same problem
(`5ee35ac2…`) hit `budget_exhausted` after 4 rejected `episode_step` calls, all
misdiagnosed as tactic bugs in real time. The actual cause, found only by
replicating the exact server-assembled module locally: the first proof line
had 0 leading spaces while every later line had 2, and `raw_lean_block`
preserves relative indentation exactly — that single-line inconsistency broke
parsing. Fixed by resubmitting on a fresh episode with uniform indentation
throughout. No mathematical content changed between the failing and
succeeding submissions.

## Result row 3/6 — alpha_le_one_not_isGoodPair

| field | value |
|---|---|
| result_id | `d8e57141-e124-41bc-97fe-9bf4e882ec72` |
| run / suite | `575f57b1…` / `4c2b3e65…` |
| benchmark_problem_id | `168f0fd3-7701-40f8-8132-b702a70ac9ac` (theorem_name `alpha_le_one_not_isGoodPair_diag`, see note) |
| problem_version_id | `231ba8c9-b2d7-4854-ae00-834e2c943d51` |
| episode | `6766c89d-7840-4d11-9fa6-fb7495f12435` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 (on the episode that used the fix below) |
| statement hash | `b2eb28f162b568bbe4bc83534248463d1efab3ae807e13866c0eaa8d36f55d21` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| assembly role | one of `integer_isGoodPair_iff`'s four pieces: `α ≤ 1` fails |

**Naming note (honest disclosure).** The first registration of this theorem
(benchmark_problem_id `ce8478bf…`, theorem_name `alpha_le_one_not_isGoodPair`,
no `_diag` suffix) never got a matching proof — it's an orphaned row, harmless
but unused. What actually got proved is registered under the diagnostic name
`alpha_le_one_not_isGoodPair_diag`, created while root-causing the format bug
below. The **statement is byte-identical mathematics** (same theorem, just
typed on one line instead of two during diagnosis) — only the bookkeeping
label differs.

**Format note (honest disclosure) — the REAL root cause, superseding the
int_coeff misdiagnosis above.** This theorem hit the identical-looking
`parse_error: "expected token"` four times running, at the exact same
line:col regardless of proof content — including once with a bare `sorry` as
the entire proof, which cannot itself cause a parse error. That proved the
bug was in the *statement/header*, not the proof. Root cause, confirmed by
bisection with `mathlib_search_declarations` and `lean_declaration_lookup`:
`problem_create` defaults its Lean environment to **`Mathlib.Tactic.Ring` +
`Mathlib.Tactic.NormNum` only** — nowhere near enough for `Finset.sum`,
`Finset.Icc`, or `∀ᶠ … in …` notation, all of which come from far more of
Mathlib. The fix is `problem_imports: ["Mathlib"]` on `problem_create` (not
just on `benchmark_problem_register`, which already defaults there). This
means the *earlier* int_coeff "indentation" diagnosis was likely papering
over the same underlying issue by coincidence of which module happened to be
in scope — the real, general lesson for every future `problem_create` call in
this project is: **always pass `problem_imports: ["Mathlib"]` unless there's
a specific reason to scope it down.**

## Result row 4/6 — one_two_isGoodPair

| field | value |
|---|---|
| result_id | `685c12b8-0331-4e6a-8a70-71e6094493eb` |
| run / suite | `575f57b1…` / `4c2b3e65…` |
| benchmark_problem_id | `e4c75259-d4e0-49a6-9839-e878724c3abd` |
| problem_version_id | `1d834834-03eb-44b3-bdb4-9868831fe3b5` |
| episode | `0d2fa763-6adc-4a4d-bd4d-e3626bad712a` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 |
| statement hash | `ec9344f81572cf51336326d49a224e0abeae96f161623ba088c4c31008064737` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| assembly role | one of `integer_isGoodPair_iff`'s four pieces: `(1,2)` is good |

## Result row 5/6 — dyadic_two_isGoodPair

| field | value |
|---|---|
| result_id | `a00f0171-7298-4acb-ab32-e97870ca5fbd` |
| run / suite | `575f57b1…` / `4c2b3e65…` |
| benchmark_problem_id | `b9e1d69d-4b00-45ab-85f1-b9acdb04ffaf` |
| problem_version_id | `40f8a013-90b1-4298-8e6e-66323d1c4679` |
| episode | `130631aa-4deb-4040-bc6d-f72c6468d833` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 |
| statement hash | `32303ccb359f6f8007e88d6f58e40aefd4c2adc26068ce356db81cc1cd4ae28c` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| assembly role | none — extra result, not one of the four `integer_isGoodPair_iff` pieces |

## Result row 6/6 — alpha_gt_two_not_isGoodPair

| field | value |
|---|---|
| result_id | `d986f456-340c-4fa6-ae95-06304a51eedb` |
| run / suite | `575f57b1…` / `4c2b3e65…` |
| benchmark_problem_id | `1c56259c-043f-48e7-b4bf-e40e24681c64` |
| problem_version_id | `729145be-7407-4951-be16-3a33a2941c17` |
| episode | `6c0babf6-d577-4847-a2a5-08d2318b97e5` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 3 / 3 |
| statement hash | `cbf2b02039d244db72f164690842335875e1735b8b459b78cdfe9fcd7da2d7b1` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| assembly role | one of `integer_isGoodPair_iff`'s four pieces: `2 < α` fails |

## Episode public summary — alpha_gt_two_not_isGoodPair

- episode: `6c0babf6-d577-4847-a2a5-08d2318b97e5`
- outcome: `KERNEL_VERIFIED`; `kernel_verified: true`; `certified: false`
- `proof_body_redacted: true` in summary mode; the full body is published
  deliberately in [proof/Erdos349_alpha_gt_two_not_isGoodPair.lean](proof/Erdos349_alpha_gt_two_not_isGoodPair.lean)
- statement hash: `cbf2b02039d244db72f164690842335875e1735b8b459b78cdfe9fcd7da2d7b1`
- import manifest hash: `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- environment hash: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- trajectory: 5 events, first `f29fa7b8…`, last `b897322a…`
  (chain detail: [trace/trajectory.md](trace/trajectory.md))
- timing: created 06:27:47Z → verified 06:33:13Z (three tracked attempts)

**Attempt history.** Attempt 1 had the right mathematical proof shape but used
unqualified `Tendsto` / atTop-tendsto identifiers. Attempt 2 qualified
`Filter.Tendsto` and related tendsto names but still left `atTop`
unqualified. Attempt 3 also qualified `Filter.atTop`; Lean accepted it.

## Result row 7/7 — integer_isGoodPair_iff (the culminating assembly)

| field | value |
|---|---|
| result_id | `2635b554-0171-48aa-8fd2-8bfc9f80239a` |
| run / suite | `575f57b1…` / `4c2b3e65…` |
| benchmark_problem_id | `3e6a7150-c9ea-44e0-b1ab-0dca473f9ebc` |
| problem_version_id | `c0c9276f-4c29-4ea0-9a8b-b980fec92e84` |
| episode | `4f28677b-09ba-442a-8543-33e49e021e35` |
| status / outcome | kernel_verified / kernel_verified |
| attempts_used / pass_at | 1 / 1 |
| statement hash | `a020861a71336e9406c8ce201d23d2082dcd0880fefecb2f018c80ffade1522b` |
| fidelity basis | `formal_benchmark_hash_alignment` → `canonical_statement_hash_match` |
| assembly role | the theorem itself — combines all four pieces via case split |

**Proof shape.** Since the tracked pipeline verifies each `problem_version`
in isolation (no cross-problem_version imports), the four component lemmas
are restated as local `have`s inside one `solve` submission rather than
referenced as separately-registered theorems — mechanically identical
content to the four standalone proofs above, just re-declared in scope. The
argument: rule out `α = 1` via `alpha_le_one_not_isGoodPair` and `α > 2` via
`alpha_gt_two_not_isGoodPair` to force `α = 2`; then rule out `t ≥ 2` via
`int_coeff_ge_two_not_isGoodPair` to force `t = 1`; the converse direction is
exactly `one_two_isGoodPair`. First attempt, no format issues — the earlier
`problem_imports: ["Mathlib"]` lesson (row 3/6 above) was applied from the
start this time.

**Episode public summary.**

- episode: `4f28677b-09ba-442a-8543-33e49e021e35`
- outcome: `KERNEL_VERIFIED`; `kernel_verified: true`; `certified: false`
- full body published in [proof/Erdos349_integer_isGoodPair_iff.lean](proof/Erdos349_integer_isGoodPair_iff.lean)
- import manifest hash: `aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7`
- environment hash: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- trajectory: 3 events (chain detail: [trace/trajectory.md](trace/trajectory.md))
- timing: created 06:55:46Z → verified 06:59:12Z (one attempt)

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
