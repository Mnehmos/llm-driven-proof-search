# Fix Plan — Stale CHECK Constraints on Long-Lived Databases (2026-07-03)

## The finding

A live playtest session (attempting IMO 2025 P3, the "bonza" functional
equation problem) hit `problem_create` failing with a generic
"Tool execution failed" on every single attempt — including a minimal,
ASCII-only, no-imports payload, which ruled out anything about the request
itself. `problem_list` and `lean_declaration_lookup` worked fine on the same
running server.

Reproducing directly against a copy of the actual live `proofsearch.db` (not a
fresh test database) surfaced the real error, which the generic MCP error
message had been hiding:

```
CHECK constraint failed: fidelity_status IN ('pending', 'approved', 'revoked')
```

## Root cause

`proofsearch.db` was created before the proof-soundness-vs-statement-fidelity
rewrite (`docs/fix_plan_playtest_02.md`), which changed the fidelity
vocabulary from `('pending', 'approved', 'revoked')` to
`('unreviewed', 'attested', 'verified', 'rejected', 'revoked')` and added
`'kernel_verified'` to `episodes.outcome`.

SQLite bakes `CHECK` constraints into a table at `CREATE TABLE` time.
`CREATE TABLE IF NOT EXISTS` — what `initialize_v1_db` runs on every
startup — is a complete no-op against a table that already exists; it does
not, and cannot, update an existing table's constraints. The v0.2.4 fix for
"existing databases are not migrated" (`docs/fix_plan_playtest_04.md`) only
handled the *missing-column* version of this problem
(`import_manifest_json`/`import_manifest_hash`). It did not address a
database that already has the columns but is still enforcing an **older
CHECK constraint** — which is a harder failure than a missing column: every
`problem_create` call inserts `'unreviewed'` or `'attested'`, and every one
of those values is rejected by the old 3-value constraint, permanently and
deterministically, until the table itself is rebuilt.

Checking further, `episodes` had the identical exposure: its `outcome` CHECK
was still the pre-fidelity-split list, missing `'kernel_verified'` — meaning
any episode on this database that reached `kernel_verified` would have hit
the same class of failure the moment it tried to write that outcome.

## The fix

SQLite has no `ALTER TABLE ... DROP CONSTRAINT` / `ALTER CHECK`. The only way
to change a CHECK constraint is the standard create-copy-drop-rename
sequence, run automatically and idempotently on every startup:

- `migrate_fidelity_status_vocabulary`: detects a `problem_versions` table
  still enforcing the old constraint (by checking whether its stored SQL
  already mentions `'unreviewed'`), and if so, rebuilds it with the current
  constraints, remapping `'approved'` → `'verified'`, `'pending'` →
  `'unreviewed'`, `'revoked'` → `'revoked'` (unchanged), anything unexpected
  → `'unreviewed'`.
- `migrate_episode_outcome_vocabulary`: same technique for `episodes`,
  detecting the presence of `'kernel_verified'` in the stored SQL.
- `initialize_v1_db` now runs with `PRAGMA foreign_keys = OFF` for the whole
  init sequence (both migrations drop/recreate tables that other tables
  reference — `problem_fidelity_reviews` → `problem_versions`,
  `episode_obligations`/etc. → `episodes` — which FK enforcement would
  otherwise block), re-enabling it at the end.

**Why `'approved'` maps to `'verified'`, not `'attested'`**: `'attested'` can
never reach `state = 'COMPLETE'` under the current CHECK invariant
(`state <> 'COMPLETE' OR fidelity_status = 'verified'`). The live database
already had a row in `COMPLETE` state — mapping to `'attested'` would have
made the migration's own `INSERT` violate the current constraint immediately,
failing the migration outright. `'verified'` is both the semantically
faithful mapping (the old `'approved'` meant "reviewed and confirmed") and
the only choice that keeps every existing row valid under the new invariants.

## Verification

- New regression tests (`p2_fidelity_vocabulary_migration.rs`): a simulated
  pre-fidelity-split database (both tables, realistic CHECK constraints,
  rows in `COMPLETE` and `PROVING` state) migrates correctly on startup,
  a fresh insert using the current vocabulary succeeds afterward where it
  previously failed, an episode reaching `'kernel_verified'` can be inserted,
  a second startup against an already-migrated database is a no-op (no
  duplication, no failure), and a fresh database accepts the current
  vocabulary directly.
- `cargo test --workspace`: 35 tests / 15 suites, all passing.
- Live check: copied the actual `proofsearch.db` from the ongoing session (16 real
  rows, including an in-progress IMO 2025 P3 attempt), ran it through a
  debug build with the fix. Every pre-existing row's `fidelity_status`
  correctly shows `verified` (was `approved`), row count and content
  otherwise unchanged, and `problem_create` — which failed 100% of the time
  before — now succeeds normally.

## Not yet done

The actual running server process for this session's live `proofsearch.db` was
started from the release binary before this fix was written, and Windows
holds an exclusive lock on a running `.exe`, so the release binary could not
be rebuilt in place while that process is live. The fix is verified correct
against a copy of the real database via a debug build; the running process
needs to be restarted (picking up a rebuilt release binary) before the fix
takes effect against the actual `proofsearch.db` the live session is using. The
migration runs automatically and safely on that next startup — no manual
database surgery is needed.

## Lesson

A "database migration" story isn't complete until it accounts for **every**
kind of schema drift a long-lived database can carry — not just missing
columns (v0.2.4's fix) but stale CHECK constraints from vocabulary changes.
Both are invisible at `cargo test` time (fresh in-memory databases always
get the current schema straight from `CREATE TABLE`) and only surface against
a database that's actually lived through the history of schema changes —
exactly why this bug shipped in v0.2.4 undetected and was only found by an
actual long-running live session hitting it.
