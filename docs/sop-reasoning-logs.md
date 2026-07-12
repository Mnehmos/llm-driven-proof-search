# SOP: durable reasoning logs

## Purpose

Every meaningful proof-search decision must leave a durable, queryable trail in
this environment. Plans, failed checks, diagnostics, retries, strategy pivots,
calibrations, submission-format repairs, successful verification, and the
decision to give up are valuable training evidence. A final verified proof alone
does not preserve how the agent recovered from mistakes.

The environment ledger is the system of record. A terminal transcript, an
untracked `lake env lean` invocation, a file under a user profile or system temp
directory, or hidden scratch work is invisible to the episode. Do not move
scratch work outside the workspace. Prefer the tracked `proof_session`, `draft`,
and `reasoning_log` tools. When a workspace-local diagnostic command is
necessary, record its purpose before running it and record its concrete result
immediately afterward; never wait until the final proof to reconstruct the path
from memory.

A reasoning log is an externalizable decision summary, not a proof and not a
request for private token-by-token chain-of-thought. Record the hypothesis,
approach, observations, decisions, and lessons needed to reproduce the search.

## Mandatory cadence and hard gate

The ordinary-attempt threshold is `REASONING_LOG_GATE_THRESHOLD = 2`, with a
stricter dynamic rule for `give_up`.

1. Before the first `episode_step`, add an `initial_plan` reasoning log whenever
   possible. The hard gate permits at most two ordinary submissions between
   logs so a malformed or failed opening move cannot strand the episode.
2. After an attempt, promptly add a fresh log describing its actual result and
   what the next action will change. A third ordinary submission after the
   latest log is refused.
3. A log may be filed before `attempt_claim`; `action_attempt_id` is optional so
   planning is not forced outside the ledger.
4. `episode_step` rejects a normal call when two prior attempts are newer than
   the latest log (or when two attempts exist and no log has been filed). The
   rejected call does not mutate episode or proof state.
5. `give_up` is gated too. It is the most detailed checkpoint: the latest fresh
   log must include non-empty `actual_outcome` and `lesson_learned`, explaining
   the blocker, what was tried, and what a future attempt should retain.

The threshold is a backstop, not permission to discard an iteration: log each
meaningful plan, diagnostic, retry, and pivot promptly. A reasoning log
satisfies the process gate only; it never changes an obligation, outcome,
certification, or training-eligibility status.

## Standardized form

Use `reasoning_log` with `action.type = "add"` and fill these fields:

| Field | Requirement | Intent |
|---|---|---|
| `episode_id` | Required | Episode whose process is being documented. |
| `episode_revision` | Required | Revision the reasoning concerns. |
| `action_attempt_id` | Optional | Link a retrospective to a specific claimed attempt. Omit for planning before a claim exists. |
| `reasoning_kind` | Required | Closed-vocabulary classification described below. |
| `hypothesis` | Optional, strongly expected for plans/pivots | Falsifiable belief motivating the next check. |
| `approach_summary` | Required, non-empty | Concrete technique, diagnostic, or change being attempted. |
| `expected_outcome` | Optional, strongly expected before attempts | What result would support or refute the hypothesis. |
| `actual_outcome` | Optional; required before `give_up` | What happened, including the relevant verifier/tool diagnostic. |
| `lesson_learned` | Optional; required before `give_up` | What the result changes about the next attempt or future work. |
| `confidence` | Optional: `low`, `medium`, or `high` | Calibrated confidence in the hypothesis/approach. |
| `author` | Required, non-empty | Agent/model/run identifier responsible for the declaration. |

Do not paste undigested logs into `approach_summary`. Preserve the actionable
diagnostic, the interpretation made from it, and the consequent decision.

## Reasoning kinds

- `initial_plan`: before the episode's first submission; state the initial
  hypothesis, intended proof shape, and first discriminating check.
- `retry_after_failure`: the previous attempt failed and the next attempt makes
  a localized repair based on that result.
- `strategy_pivot`: evidence invalidated the current approach and the next
  attempt changes proof architecture, encoding, lemma choice, or search method.
- `error_diagnosis`: isolate a parser, elaborator, resource, environment, or
  kernel failure before choosing the repair.
- `success_retrospective`: record why a successful/certified attempt worked and
  which earlier failure-recovery steps mattered.
- `other`: a meaningful process checkpoint not represented above; explain the
  reason clearly in `approach_summary`.

## Worked example: Game of Life Garden-of-Eden proof

The following is the intended sequence, condensed from episode
`d8911237-8c2c-4b5d-95da-e25dc2ad633c`:

1. `initial_plan`: hypothesize that a finite exhaustive computation can certify
   the collision/no-preimage claim; expect a direct `decide` proof to elaborate.
2. `error_diagnosis`: record that direct reduction hit a recursion-depth wall;
   the failure is computational structure, not evidence that the theorem is
   false.
3. `strategy_pivot`: record the type-encoding hypothesis and the planned small
   calibration. The 128-state search succeeds while 256 exceeds the practical
   reduction boundary, refuting the earlier assumption that one monolithic
   decision is viable.
4. `retry_after_failure`: switch to a chunked-decision proof whose chunks remain
   below the observed boundary; expect kernel evaluation to finish within the
   resource limit.
5. `error_diagnosis`: the workspace-local proof checks, but the submitted
   embedding fails twice because multi-line relative indentation changes under
   transport. Record the parse diagnostics and choose a one-line semicolon
   sequence with every inline `by` block parenthesized (or use
   `proof_format = "raw_lean_block"` when indentation is intentional).
6. `success_retrospective`: record that chunking solved the recursion-depth
   problem and flattened/parenthesized transport solved the embedding problem;
   the final submission was certified.

Example add call:

```json
{
  "action": {
    "type": "add",
    "episode_id": "d8911237-8c2c-4b5d-95da-e25dc2ad633c",
    "episode_revision": 2,
    "reasoning_kind": "error_diagnosis",
    "hypothesis": "The proof idea is sound; relative indentation changed when the proof term was embedded.",
    "approach_summary": "Compare the standalone and submitted parser diagnostics, then flatten the tactic sequence and parenthesize inline by-blocks.",
    "expected_outcome": "The same mathematical proof will elaborate after transport-safe formatting.",
    "actual_outcome": "The submitted form failed at the first indentation-sensitive bullet while the workspace-local file compiled.",
    "lesson_learned": "Treat proof transport as a separate failure mode; use raw_lean_block for intentional indentation or flatten the sequence.",
    "confidence": "high",
    "author": "agent-run-id"
  }
}
```

## Which artifact to use

- `reasoning_log`: the agent's process across attempts—plans, diagnostics,
  retries, pivots, outcomes, and lessons. This is the mandatory gate artifact.
- `draft`: informal mathematical content before formalization, plus extracted
  mathematical moves. A draft does not replace the per-attempt process log.
- `exposition`: human-readable mathematical prose about the problem, lemmas,
  construction, or verified result. It is not the agent's attempt history.
- `proof_session`: tracked tactic-by-tactic exploration. Its nodes and failures
  preserve interactive search evidence; add `reasoning_log` checkpoints for the
  decisions and lessons around promotion through `episode_step`.

Use `reasoning_log` with `action.type = "observe"` to audit the complete
chronological trail for an episode.
