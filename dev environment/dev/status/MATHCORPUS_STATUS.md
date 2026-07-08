# MathCorpus Status

Global status file for the MathCorpus agent workspace. Owned by the dev
loop agent (`dev/github_issues`); domain agents propose updates rather
than editing directly.

## Corpus totals

| Metric | Value |
|--------|-------|
| Total packets | 146 |
| Verified public packets | 145 |
| Negative packets | 1 |
| Target for v0.1 | 250 packets |
| Progress | ~58% |
| Remaining to v0.1 | 104 packets |

## Domain distribution

| Domain | Packets |
|--------|---------|
| Algebra | 64 |
| Number theory | 36 |
| Geometry | 24 |
| Combinatorics | 22 |

## Level distribution

| Level | Packets |
|-------|---------|
| L0 | 64 |
| L1 | 68 |
| L2 | 14 |

## Validation status

Not yet re-synced against the scaffolded per-domain `DASHBOARD.md` files —
this snapshot reflects the last known corpus state prior to workspace
scaffolding.

## Redaction audit status

Not yet run against this workspace.

## CI status

Not yet wired to this workspace.

## Current target

Fill the domain gap toward v0.1 (250 packets) while keeping domain balance;
see individual `packets/*/*/QUEUE.md` files for next targets.

## Recommended next domains

Combinatorics and geometry are furthest behind algebra; prefer them when a
domain choice is otherwise unconstrained.

## Known environment bugs

- Attempt-claim burst-concurrency bug: use sub-waves of 7 until fixed (see
  `dev/github_issues/BUGS.md`).

## Known workflow workarounds

- On an invalid claim response, re-observe; if still pending, re-claim with
  a fresh idempotency key and retry.

## Current safe batch size

Sub-waves of 7 proof attempts.
