# Architecture Card: reasoning-log gate

## Capability

The MCP server accepts append-only, client-declared reasoning summaries and uses
their presence/freshness to refuse excessive unlogged `episode_step` submissions.
Ordinary steps permit at most two submissions between logs. `give_up` always
requires a fresh log with `actual_outcome` and `lesson_learned`.

The server itself does not call a model. This card treats the external model host
as the proposer because its output enters the server through MCP.

## What the model may propose

One `reasoning_log` `add` payload containing an episode/revision, optional attempt
link, closed-vocabulary reasoning kind, optional hypothesis/outcome/lesson fields,
required non-empty approach summary, optional calibrated confidence, and required
author. The proposal asserts only what the agent says it thought, tried, observed,
or learned. It does not assert proof correctness.

## What owns truth

- SQLite foreign keys and server queries own episode/attempt identity and log
  chronology.
- The typed episode state machine owns attempt legality, revisions, budgets, and
  state transitions.
- The pinned Lean kernel owns proof verification.
- A reasoning log owns no proof truth and cannot change an episode or obligation
  outcome.

## Validation before commit

1. Serde/JSON Schema validates the internally tagged action shape.
2. The handler validates the reasoning-kind and confidence vocabularies.
3. It rejects negative revisions, empty approach summaries, and empty authors.
4. It verifies that the episode exists and that an optional attempt exists and
   belongs to that episode.
5. The database enforces foreign keys and closed-vocabulary checks again.

For `episode_step`, the gate counts prior attempts by their latest execution
timestamp (falling back to claim time) since the latest log before the action
state machine mutates anything. A real `give_up` attempt additionally
requires a fresh detailed log. Fabricated/cross-episode attempt identifiers are
left to the foundational attempt validator so the SOP gate cannot mask its
established invalid-response semantics.

## Commit boundary

For `reasoning_log add`, the commit boundary is the transaction inserting one
`reasoning_logs` row. There is no update or delete action.

For `episode_step`, the gate runs before the transaction that calls
`attempt_prepare`. Rejection therefore creates no action execution, proof-state
mutation, budget charge, certification change, or fabricated result.

## Rejected proposals

Malformed or illegal log proposals return bounded MCP invalid-parameter errors
and write nothing. A gated step returns an actionable invalid-parameter error
pointing to `reasoning_log` and `docs/sop-reasoning-logs.md`; the caller may add
one valid checkpoint and retry. There is no server-side retry loop and no
server-inferred replacement reasoning.

## Randomness ownership

The capability uses no semantic randomness. UUID generation supplies row
identity only; it does not influence validation, gate decisions, proof search, or
kernel outcomes.

## Evidence required

- Add/observe round-trip preserves fields and chronological append-only rows.
- Invalid vocabularies, empty required text, unknown episodes, unknown attempts,
  and cross-episode attempt links fail without writes.
- Two ordinary attempts may proceed without an intervening log; the third is
  refused before state mutation; adding a log permits the retry.
- `give_up` without a fresh detailed log is refused; a qualifying log permits it.
- Logging never changes episode/obligation proof state or certification.
- Existing workspace build and tests remain green.

## Recovery

Disable the enforcement by removing the early gate call while retaining the
append-only ledger and SOP data. Remove the MCP registration/dispatch only if the
feature itself is rolled back. Existing `reasoning_logs` rows are harmless
metadata and should not be destructively deleted during rollback.
