# Fix Plan — v0.2.4 Hotfix: Latency + Lean Source Injection (2026-07-03)

## The finding

Live use in Claude Desktop hit "Failed to call tool 'lean_declaration_lookup'"
mid-episode, discarding an in-flight reasoning turn (~100k thinking tokens).

Root cause: `lean_declaration_lookup` always ran its full two-pass check —
the problem's own manifest, then unconditionally the entire Mathlib umbrella
(`import Mathlib`) — every single call. The umbrella pass alone reliably
takes 15-40+ seconds (cold `lake env lean` process, no persistent server).
That routinely exceeded the MCP client's tool-call timeout, and the call was
also holding the shared DB connection mutex for the whole duration, so it
could additionally block other in-flight tool calls on the same server.

## The fix (v0.2.4)

**The umbrella check is now opt-in, not automatic.**

- `lean_declaration_lookup` gained a `deep_check: bool` argument, default
  `false`.
- Default behavior: check only the problem's own import manifest (a few
  seconds). A miss returns the new status `not_available_under_current_manifest`
  — explicitly documented as inconclusive on its own; it does **not** mean the
  declaration is absent from the pinned library, only that it needs an import
  or a deeper check.
- `deep_check=true`: additionally checks under the full Mathlib umbrella and
  returns a conclusive `not_in_current_import_scope` (add an import) vs.
  `unknown_declaration` (genuinely absent/misspelled) verdict — the same two
  statuses the original tool returned unconditionally.
- The DB connection lock is now released before the (possibly slow) call into
  the gateway, instead of being held across it.
- `RealLeanGateway::run_lean_json` now takes an explicit `timeout: Duration`
  per call site (20s fast pass, 90s umbrella pass, 60s verify, 45s manifest
  validation) instead of one hardcoded 60s for everything.
- Tool description text and `environment_describe.epistemic_rules` updated so
  a driving agent knows a `not_available_under_current_manifest` result alone
  isn't proof of absence, and that `deep_check=true` is required for a
  conclusive verdict.

Live-verified against the real Lean/Mathlib environment (not a mock):
default lookup for an out-of-scope name returned in ~4.8s with
`not_available_under_current_manifest`; the same name with `deep_check=true`
took ~19.1s and correctly resolved to `not_in_current_import_scope`; an
in-scope name resolved in ~4.5s without needing `deep_check` at all.

## Self-inflicted regression during this fix, and how it was caught

An intermediate attempt at this same fix wrapped the three blocking gateway
calls (`lean_declaration_lookup`, `problem_create`'s manifest validation,
`episode_step`'s attempt commit) in `tokio::task::block_in_place`, intending
to stop a long synchronous call from starving the async runtime's worker
threads.

`block_in_place` requires a multi-threaded Tokio runtime and **panics** on a
current-thread one. The real server runs under `#[tokio::main]` (multi-threaded
by default), but the test harness runs the server inside a `tokio::spawn` task
under `#[tokio::test]`, which defaults to `current_thread`. The panic happened
inside that detached spawned task, so it silently killed the server task
without ever writing a response — the test client's read simply blocked
forever. Every test that exercised one of the three wrapped call sites hung
indefinitely instead of failing.

Caught by: the test run visibly not returning ("its been like 10 minutes"),
confirmed via `Get-Process` showing a stuck `chatdb_mcp-*.exe` test binary
with ~0% CPU, then isolating the exact hung tests by running individual test
binaries with `--exact` under a hard shell `timeout`.

Fix: removed `block_in_place` from all three call sites, reverting to the
plain unwrapped synchronous call — the same pattern `episode_step`/
`attempt_commit` had used all along without any reported runtime-starvation
issue. No replacement mitigation was added; the premise that starvation was
an actual observed problem (versus a hypothetical one) didn't hold up, and
introducing an actual hang to fix a latency complaint is strictly worse.

**Lesson:** a fix that changes async/threading behavior needs to run under
both the real server's runtime flavor *and* the test harness's runtime flavor
before being considered done — they are not the same, and a primitive that's
correct on one can silently deadlock on the other.

## Verification (latency fix)

- `cargo test --workspace`: 32 tests / 13 suites, all passing, full run in
  ~8s (no hangs).
- Live Python acceptance script against the release binary + real
  Lean/Mathlib toolchain confirmed both the fast default path and the
  `deep_check=true` opt-in path.

---

# Part 2 — Lean source injection through import/declaration strings

An independent adversarial review of the v0.2.3 commit (the environmental
scope collapse fix) found that the mechanism used to expose more of the
environment — import manifests as real, client-supplied data, and
`lean_declaration_lookup`'s `#check`-based probing — opened a command
injection path into the verifier, through a different door than the one the
proof-soundness-vs-fidelity split (`docs/fix_plan_playtest_02.md`) had closed.

## P0: `problem_imports` permitted arbitrary Lean source injection

`problem_create` only checked that each `problem_imports` entry was
non-empty, then handed it straight to `RealLeanGateway::build_import_block`,
which writes `import {module}\n` verbatim into every proof file checked
against that problem's manifest. A string containing a newline could append
arbitrary Lean commands after the `import` line — e.g.
`"Mathlib\naxiom cheat : False"` — which the validation probe would happily
compile (an `axiom` isn't an error), after which the injected axiom would be
silently baked into every subsequent proof for that problem, letting a prover
certify any proposition using it without ever writing `sorry`. This is the
same soundness-bypass class the fidelity split closed, reopened through the
new import-manifest interface.

**Fix**: added `valid_lean_module_path` — every `problem_imports` entry must
be a dot-separated sequence of `[A-Za-z_][A-Za-z0-9_]*` segments (max 256
chars, max 50 entries per problem), checked and rejected with
`mcp_invalid_params` *before* it ever reaches the gateway or gets stored.
Compilation success was never a valid substitute for syntax validation —
Lean will happily compile `import Mathlib\naxiom cheat : False`, since
nothing about that is a syntax error.

## P1: `lean_declaration_lookup`'s `names` had the same injection surface

Each queried name is written verbatim into `#check {name}\n`. A name
containing a newline could append arbitrary Lean commands that execute
inside the verifier process during the lookup itself (this runs in a
temp file, so it doesn't produce a certificate, but it's still arbitrary
code execution in a process that isn't an OS sandbox).

**Fix**: added `valid_lean_declaration_name` (no whitespace, alphanumeric +
`_ ' . ! ?` only, max 256 chars) and a 50-names-per-call limit, enforced the
same way — rejected before any Lean invocation.

## P1: v0.2.2 databases were never migrated to the v0.2.3 schema

`import_manifest_json`/`import_manifest_hash` were added to the
`CREATE TABLE IF NOT EXISTS problem_versions` statement, but SQLite's
`IF NOT EXISTS` is a no-op against a table that already exists — a database
created before v0.2.3 would permanently lack these columns, and the first
query touching them would fail with `no such column`. There was a
`schema_migrations` table and a `migrate_v0_to_v1` function in the codebase,
but nothing on the actual startup path (`initialize_v1_db`) ever called an
ALTER-TABLE-style migration for this specific change.

**Fix**: `migrate_add_import_manifest_columns` runs before the schema batch
on every startup — checks whether `problem_versions` exists and already has
the column (no-op on both a fresh DB and an already-migrated one), and
otherwise `ALTER TABLE ADD COLUMN`s both columns and backfills
`import_manifest_hash` with the real `canonical_hash` of the base manifest
(not left empty) for pre-existing rows, since that's what they were actually
checked against.

## P1: `check_pass` could report false availability on an environment failure

`lookup_declarations`' `check_pass` only recorded errors whose line numbers
matched the expected `#check` lines, discarding `proc_success` entirely. An
error elsewhere in the file — e.g. a bad import failing on line 1, so no
`#check` ever actually ran — left every queried name with zero recorded
failures, which the code then reported as `Available` for all of them: a
lookup that never actually checked anything could report success.

**Fix**: errors landing outside the `#check` line range are now classified
as an environment failure and returned as `Err` (surfaced to the caller as
an honest tool-call error) instead of being silently dropped; a process
failure that produces no diagnostics at all (crash before any output) is
also now an `Err` rather than defaulting to "all available."

## P2: default `validate_import_manifest` now fails closed

The trait default previously returned `Ok(())` — a gateway that didn't
override it silently approved any custom import. Changed the default to
`Err`, so a gateway must explicitly opt into vouching for custom imports
(`RealLeanGateway` does, with a real compile check; the test `MockGateway`
now does too, explicitly, to keep isolating manifest-extension bookkeeping
from real Lean validation in unit tests).

## P2: stderr was silently discarded on Lean process failures

`run_lean_json` only parsed stdout's `--json` stream; Lake resolution
failures and other process-level errors often land on stderr instead,
leaving callers with an unexplained `"process failed"`. `run_lean_json` now
also returns captured stderr, and `verify_exact`/`validate_import_manifest`/
`check_pass` surface it in their diagnostic/error output when nothing else
explains a failure.

## Verification (injection fix)

- New regression tests: `test_problem_create_rejects_malformed_import_syntax`
  (8 malicious/edge-case import strings, plus confirms a legitimate module
  path is still accepted), `test_lean_declaration_lookup_rejects_malformed_names`
  (5 malicious names + a >50-names limit check), and two migration tests
  (`p1_import_manifest_migration.rs`: a simulated pre-v0.2.3 database gains
  the columns with the correct backfilled hash, a second startup against an
  already-migrated database is a no-op, and a fresh database is unaffected).
- Live check against the real `RealLeanGateway` (not a mock): a newline- and
  a semicolon-injection attempt via `problem_imports` were both rejected in
  <0.01s (no Lean process spawned at all), an injection attempt via
  `lean_declaration_lookup` names was rejected the same way, and a
  legitimate new import was still accepted end-to-end (~5s, real compile).
- `cargo test --workspace`: 33 tests / 14 suites, all passing, ~9s, no
  hangs.
