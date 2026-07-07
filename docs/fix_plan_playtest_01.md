# Fix Plan — Live Playtest 01 (2026-07-02)

**Status of the environment: NOT playable end-to-end.** The MCP server boots, lists 11 tools,
creates and observes episodes, and correctly rejects forged claims and stale revisions. But five
independent blockers prevent any client from completing a single accepted step and any episode from
ever reaching a terminal state.

How this was found: raw JSON-RPC playtest over stdio against
`target/release/proofsearch-mcp.exe` (the exact path Claude Desktop / any MCP client uses), with SQL
fallbacks only where the MCP surface has no tool. The unit/phase tests all pass because they call
`proofsearch-core` functions directly with hand-picked arguments; none of them drive the MCP layer as a
client. **Every fix below must therefore land with an MCP-level integration test** (see Phase 0),
not just a core-crate unit test.

Work order is strict: Phase 0 → 1 → 2 → 3. Within a phase, tasks are independent unless noted.
Follow `docs/tdd_requirements.md` (RED → GREEN → commit) and `docs/gitflow_workflow.md`.

---

## Phase 0 — Test harness that reproduces the playtest

### 0.1 Add an MCP integration test crate/module

`crates/proofsearch-mcp/src/main.rs` already contains one duplex-transport test
(`test_mcp_list_tools_and_describe`, main.rs:772). Extend that pattern into a proper integration
test module (e.g. `crates/proofsearch-mcp/tests/mcp_playthrough.rs` with the handler factored out of
`main.rs` into a `lib.rs`, or more `#[cfg(test)]` tests — agent's choice, but the test must go
through `call_tool`, not call orchestrator functions directly).

The test MUST script this full episode against an in-memory DB with a `MockGateway` (copy the one
in `crates/proofsearch-core/tests/phase8_step_tests.rs` — pass iff source does not contain `sorry`):

1. seed problem (via the new `problem_create` tool — task 2.1; until that lands, seed via SQL in the test)
2. `episode_create` (max_steps=5, budget=1_000_000)
3. `episode_observe` → assert observation + action_request present
4. `attempt_claim` (new tool — task 1.1) → returns `action_attempt_id` + `claim_token`
5. `episode_step` with `expected_revision` **taken from the observe/claim response** and action
   `{"type":"solve","proof_term":"norm_num"}` → assert `accepted=true`, `disposition="accepted"`,
   `outcome` terminal, `termination_reason="root_proved"`
6. `episode_status` → assert `state="terminated"`, step_count=1, budget deducted
7. `trajectory_export` → assert ≥1 event (task 2.3)
8. `episode_replay` → assert audit passes on a *non-empty* trajectory

This test is the definition of done for Phases 1–2. It currently fails at step 4 (no tool), and
would fail at 5 (UNIQUE collision → rollback), 6 (CHECK violation), and 7 (no events) even if 4
existed.

Also port the negative probes (they pass today; keep them passing):
- fabricated claim → `disposition="invalid_response"`, episode state unchanged
- wrong `expected_revision` → `disposition="stale_revision"`, episode state unchanged

---

## Phase 1 — Blockers (each verified live in playtest)

### 1.1 BLOCKER: `attempt_claim` is not exposed via MCP — clients cannot step, ever

`episode_step` requires `action_attempt_id` + `claim_token`
(main.rs:71-78). These are minted only by `attempts::attempt_claim`
(crates/proofsearch-core/src/orchestrator/attempts.rs:11), which no MCP tool calls. An MCP-only client
is permanently stuck at the first step.

**Fix:** add tool `attempt_claim` to `list_tools` and `call_tool` in `crates/proofsearch-mcp/src/main.rs`:

- Args: `episode_id`, `action_request_id`, `idempotency_key`, `expected_revision` (mirror
  `attempts::attempt_claim`).
- Wrap in a transaction; on `Ok(Some(ClaimResult))` return
  `{action_attempt_id, claim_token, expires_at}`.
- On `Ok(None)` (request not pending) return a structured error that tells the client what to do
  next (e.g. `"request not pending — call episode_observe; if the claim expired it will be recovered"`).
- Call `attempts::attempt_recover_expired` at the top of the same transaction (see task 1.5) so a
  crashed client's expired claim doesn't wedge the request forever.

### 1.2 BLOCKER: accepted steps always roll back — hardcoded `episode_revision = 1` collides with UNIQUE index

`lifecycle::advance` inserts every action_request with `1_i64, // revision`
(crates/proofsearch-core/src/orchestrator/lifecycle.rs:170). The schema has
`CREATE UNIQUE INDEX idx_active_request_per_revision ON action_requests(episode_id, episode_revision)`
(crates/proofsearch-core/src/db/schema_v1.rs:342). Consequence, verified live: a step is accepted,
`attempt_commit` bumps the episode, then the post-step `advance()` inserts request #2 also at
revision 1 → UNIQUE violation → `-32603` → **the entire transaction, including the accepted step,
rolls back**. The episode can never move past revision 0.

Same root cause, second symptom: the request *advertises* `episode_revision: 1` while
`episodes.current_revision` is 0, so a client that sends the advertised value gets
`stale_revision`. The playtest hit both.

**Fix in `lifecycle::advance` (lifecycle.rs:161-177):**
- Read the episode's actual `current_revision` inside the transaction.
- Insert the action_request with `episode_revision = current_revision` (the revision the eventual
  step must present as `expected_revision`).
- Delete the `1_i64, // revision` literal.

**Contract check:** after this fix, `action_request.episode_revision` MUST equal the
`expected_revision` a client should send. Assert this in the Phase 0 test (use the advertised value
and expect `accepted=true`). This is the single most important UX invariant for agent clients.

### 1.3 BLOCKER: terminal writes violate the episodes CHECK — episodes can never end

The DB allows `outcome IN ('certified','refuted','gave_up','timeout','budget_exhausted',
'model_error','infrastructure_error')` (schema_v1.rs:113), but the MCP server writes:
- `outcome = 'terminated'` on root proved (main.rs:414)
- `outcome = 'truncated'` on step-limit truncation (main.rs:431)
- `outcome = 'truncated'` in `episode_close` (main.rs:547)

All three violate the CHECK. Verified live: `episode_close` → `-32603 CHECK constraint failed`.
The Rust `EpisodeOutcome` enum (`Terminated|Truncated|Crashed`,
crates/proofsearch-core/src/models/episode.rs) was invented and does not match the schema vocabulary,
which follows PROOFSEARCH_SPEC.md.

**Fix — align the Rust model to the schema, not the other way around:**
- Replace `EpisodeOutcome` variants with the schema vocabulary:
  `Certified, Refuted, GaveUp, Timeout, BudgetExhausted, ModelError, InfrastructureError`.
- Mapping to use in main.rs:
  - root proved → `state='terminated'`, `outcome='certified'`, `termination_reason='root_proved'`
  - give_up action terminal (if/when implemented) → `outcome='gave_up'`, `termination_reason='model_gave_up'`
  - step-limit / budget truncation → `state='truncated'`, `outcome='budget_exhausted'`, `truncation_reason='budget_exhausted'`
  - `episode_close` → `state='truncated'`, `outcome='gave_up'`, `truncation_reason` — note
    `human_cancelled` is a *TerminationReason* in the model but is written into `truncation_reason`
    today (main.rs:547); pick one consistently with schema CHECKs at schema_v1.rs:114-117 and the
    spec, and make the enum match.
- Keep the response JSON field `outcome` (now carrying the new vocabulary) and document it in the
  tool description.
- Cross-check `TerminationReason`/`TruncationReason` string forms against any CHECK constraints on
  those columns.

### 1.4 BLOCKER: KernelPass never marks the obligation proved — `root_proved` unreachable

`step::attempt_commit` (crates/proofsearch-core/src/orchestrator/step.rs) verifies with Lean but never
updates `episode_obligations.status`. `episode_step`'s termination check reads exactly that status
(main.rs:406-412: `SELECT status FROM episode_obligations WHERE ... kind='root'` → `== "proved"`).
So even a kernel-passing proof leaves the root `open` and the episode running forever.

**Fix in `attempt_commit`, in the `TypedAction::Solve` KernelPass branch:**
1. Insert an `episode_verified_lemmas` row (polarity `'positive'`, hashes from the
   `LeanVerificationResult`; schema at schema_v1.rs:182-198).
2. Update the obligation: `status='proved'`, `proved_lemma_id=<new lemma id>`, `closed_at=now`.
   NOTE the CHECK at schema_v1.rs:144-148 REQUIRES `proved_lemma_id` to be non-NULL when
   `status='proved'` — step 1 is not optional and must come first.
3. On KernelFail leave status as-is but increment `attempt_count` and consider storing the
   diagnostic in `failure_lesson` (the observation builder already surfaces
   `latest_diagnostic`/`distilled_lesson` — wire them up if cheap, else file as Phase 3).

Also fix `episode_step`'s root check (main.rs:406): `query_row` with no row panics the request if
the root obligation hasn't been seeded; use `.optional()`.

### 1.5 BLOCKER: burned requests + stuck attempts — no recovery path is ever invoked

Three ways an episode wedges permanently today (all hit in playtest):
- A step that returns `stale_revision`/`invalid_response` leaves the attempt `claimed` and the
  request `claimed`; `UNIQUE idx_one_active_attempt_per_request` (schema_v1.rs:376) forbids a second
  attempt; nothing ever expires the first one.
- A `LeanGatewayError` returns early from `attempt_commit` (step.rs:123) leaving the attempt
  `'executing'` — verified live — which `attempt_recover_expired` (attempts.rs:65) *would* reset
  after 5 min, except nothing ever calls it.
- `model_call_settle` on a failed provider call doesn't release the request either.

**Fix:**
- Call `attempts::attempt_recover_expired(&tx)` at the start of `attempt_claim` (task 1.1),
  `episode_observe`, and `episode_step` transactions. It is cheap and idempotent.
- In `episode_step`, when `attempt_commit` returns `Err(Conflict | InvalidAttempt | LeanGatewayError | ActionSchemaInvalid)`,
  explicitly finalize inside the same transaction: attempt → `'abandoned'`
  (or `'infrastructure_failed'` for gateway errors), request → back to `'pending'`. A failed step
  must leave the episode immediately re-claimable, not wedged for 5 minutes.
- `episode_observe` should include the request `status` plus, when claimed, the claim expiry, so a
  client knows whether to claim or wait.

### 1.6 BLOCKER: Lean toolchain/project missing — every `solve` is an infrastructure error

`PROOFSEARCH_LEAN_PROJECT_PATH` points at `lean-checker/`, which does not exist in the repo. The only
installed toolchain is a broken partial (`elan toolchain list` → `leanprover/lean4:v4.28.tmp`).
Verified live: `solve` → `disposition="error"`,
`LeanGatewayError("The directory name is invalid. (os error 267)")`.
The gateway hardcodes Mathlib imports (crates/proofsearch-core/src/lean/mod.rs:50-52), so the project
must depend on Mathlib.

**Fix (setup + docs, no Rust changes):**
1. Create `lean-checker/` as a Lake project pinned to a released toolchain compatible with a
   Mathlib release (e.g. `lake new leanchecker math` layout): `lakefile.toml` requiring `mathlib`,
   `lean-toolchain` file, root module `LeanChecker` with an (initially empty) `LeanChecker/Verified/`
   directory (the gateway copies passing proofs there, lean/mod.rs:204).
2. Fetch the Mathlib build cache (`lake exe cache get`) — do NOT build Mathlib from source.
3. Verify manually: `lake env lean --json <file>` on a file containing
   `import Mathlib.Tactic.NormNum` + `theorem t : 1 + 1 = 2 := by norm_num` exits 0.
4. Add a `## Lean checker setup` section to README.md (elan install, toolchain pin, cache get,
   expected disk usage). `elan-init.ps1` exists in the repo root but is referenced nowhere — fold it in
   or delete it.
5. Add a startup preflight in `main()`: if the Lean project path or `lake.exe` is missing, log a
   loud warning to stderr (do not exit — DB-only tools still work) and have `environment_describe`
   report `"lean_gateway": "unavailable"` vs `"ready"`.

---

## Phase 2 — Majors

### 2.1 No way to create a problem via MCP

`problem_versions` starts empty and `episode_create` is the only entry point. Playtest had to seed
via SQL.

**Fix:** add a `problem_create` tool:
- Args: `source_problem_text`, `root_formal_statement`, `natural_rendering` (optional),
  `metadata_json` (optional).
- Server computes hashes (`crate::hashing`), sets `fidelity_status='pending'`,
  `fidelity_method='manual'`, `state` per the problem-state machine in PROOFSEARCH_SPEC.md.
- IMPORTANT schema interaction: `problem_versions` CHECK (schema_v1.rs:25) forbids `state='PROVING'`
  unless `fidelity_status='approved'`. Since episodes should only run on approved problems, also add
  a `problem_approve_fidelity` tool (sets `approved` + records `fidelity_approval_id`) or fold an
  `approve: bool` arg into `problem_create` for dev use. `episode_create` should return a clear
  error when the problem isn't approved.
- Add `problem_list` (id, state, fidelity_status, root statement) so clients can discover
  `problem_version_id`s — the playtest had to read the DB to find one.

### 2.2 `model_call_settle` accepts negative costs and any status; reserve ignores budget

Verified live: settling `actual_cost_micros = -999999` **increased** the budget from 1,000,000 to
1,999,999. Also `status` is written unvalidated (main.rs:598-601), and `model_call_reserve` never
checks remaining budget.

**Fix in main.rs:**
- Reject `actual_cost_micros < 0` and `reserved_cost_micros < 0` with `invalid_params`.
- Validate `status` against a closed set (`settled`, `released`, `failed` — align with
  PROOFSEARCH_SPEC.md §call outcomes) and only deduct budget for statuses that consumed spend.
- In `model_call_reserve`: read the episode's remaining budget; if
  `reserved < 0 || reserved > remaining`, return a structured `budget_denied` error instead of
  inserting the lease.
- Also fix the FK error UX: reserving against an unknown `action_attempt_id` currently returns a
  bare `-32603 FOREIGN KEY constraint failed`; map to `invalid_params` with the offending field named.

### 2.3 Trajectory events are never written — export is empty, replay vacuously passes

`trajectory_export` returned `[]` after multiple steps; `episode_replay` returned
`audit_passed: true, replay_status: "()"` on that empty history. The phase-9 trajectory machinery
(`orchestrator::trajectories`) exists but the MCP step path never appends events.

**Fix:**
- In `episode_step` (and `episode_create`/`episode_close`/terminal transitions), append hash-chained
  `trajectory_events` rows via the existing trajectories module, inside the same transaction as the
  step (see ADR 0003). Minimum events: `episode_created`, `action_committed` (payload: typed action,
  disposition, verification outcome hashes), `episode_terminated`/`episode_truncated`.
- `episode_replay` must fail or report `"empty"` when there are zero events — a vacuous pass is
  worse than an error. Return `{audit_passed, events_replayed, replay_status}` and make
  `replay_status` a real enum string, not Rust debug `"()"` (main.rs:670).

### 2.4 `decompose` is accepted but does nothing

step.rs:130-133 treats `Decompose` as always-valid telemetry; no `episode_obligations` rows or
edges are created, so the action lies to the agent. Either:
- (preferred) implement it: insert child obligations (`kind='proof'`, unique `theorem_name`s — note
  `UNIQUE(episode_id, theorem_name)` schema_v1.rs:140) + `episode_obligation_edges`, then `advance`
  targets the first open child; or
- (minimum) reject it as `ActionSchemaInvalid("decompose not yet supported")` and drop it from the
  advertised action variants so clients don't waste steps on it.

### 2.5 `give_up` doesn't end the episode

`GiveUp` today just counts an invalid action and burns a step. Per the model enums it should
terminate: `state='terminated'`, `outcome='gave_up'`, `termination_reason='model_gave_up'`
(after task 1.3's vocabulary fix). Add to the Phase 0 test.

---

## Phase 3 — Polish (do after Phases 1–2 are green)

1. **`episode_status` NULL safety** — `cost_budget_micros` is nullable (schema_v1.rs:100) but read
   as `i64` (main.rs:529); an episode created without a budget makes `episode_status` error.
   Use `Option<i64>` for budget/max fields.
2. **`episode_close` on a nonexistent episode returns `"closed"`** — check
   `tx.execute` rows-affected == 1, else `invalid_params("unknown episode_id")`. Same pattern for
   other UPDATE-based tools. Also make double-close idempotent-with-notice rather than a CHECK error.
3. **Reward on non-counting steps** — rejected/invalid submissions currently emit
   `step_penalty` with `counts_as_environment_step: false` (main.rs:453-458). Emit an empty reward
   list (or an explicit `invalid_submission_penalty` if the reward policy wants one) when the step
   doesn't count.
4. **`state_hash_before` is `'dummy_hash'`** (lifecycle.rs:165) — compute a real state hash
   (canonical hash of the observation context is fine) or rename the field until it's real.
   Same for `expected_statement_hash`/`proof_source_hash` stubs in lean/mod.rs.
5. **Error-code hygiene** — domain errors surface as `-32603` internal (unknown episode in
   `episode_status`, unknown problem in `episode_create` → `FOREIGN KEY constraint failed`).
   Map not-found/validation to `invalid_params` with the field named; reserve `-32603` for genuine
   infrastructure failures.
6. **Unused-code cleanup** — `cargo fix` the 20 warnings (unused imports, `is_valid` dead
   assignment in step.rs:69, `EpisodeCloseArgs.reason` never read — either persist the close reason
   or drop the arg).
7. **Idempotency key is accepted but unused** — `episode_step`'s docs promise idempotency;
   `attempt_claim` stores the key (UNIQUE at schema_v1.rs:372) but re-submission semantics are
   untested. Add a test: same idempotency_key re-claim after crash returns the same attempt rather
   than erroring.

---

## Acceptance (run all three)

1. `cargo test --workspace` — all green, including the new Phase 0 MCP play-through test.
2. Mock-gateway play-through passes: create → observe → claim → solve → `certified` /
   `root_proved`, non-empty trajectory, replay audit on real events.
3. Live smoke test with the real gateway once 1.6 lands: seed `1 + 1 = 2` via `problem_create`,
   solve with `norm_num` through a real MCP client (Claude Desktop or the stdio driver in the
   playtest scratchpad), episode terminates `certified`, and `LeanChecker/Verified/O_*.lean`
   exists in the Lean project.

Playtest residue note: `proofsearch.db` currently contains two SQL-seeded problem versions and several
wedged episodes/attempts from the playtest (one with an artificially inflated budget from the
negative-settle probe). Wipe the DB (`proofsearch.db`, `-shm`, `-wal`) before the acceptance run.
