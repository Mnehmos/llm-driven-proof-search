# Handoff: reasoning-log SOP + hard gate on `episode_step`

**For:** Codex (ChatGPT 5.6 sol)
**From:** Claude (playtest + design session, 2026-07-10)
**Repo:** `f:\Github\mnehmos.llm-driven-proof-search.environment` (branch: `develop`)
**Status:** design done, schema landed & green, ~10% built. The rest is yours.

---

## 1. What the user actually wants (the "why")

During a playtest, the agent proved a Conway's-Game-of-Life Garden-of-Eden
theorem. It took **4 tracked `episode_step` attempts (3 `kernel_fail`, 1
`certified`)** plus **~8 untracked local `lake env lean` scratch iterations**
(recursion-depth dead ends, a wrong type-encoding hypothesis, an empirical
128-vs-256 search-size calibration, two submission-embedding parse bugs).

**Only the 4 tracked attempts became environment evidence. The ~8 scratch
iterations — the actual problem-solving, error-recovery, and hypothesis-
refinement process — evaporated.** The user's point: *that* is the gold for
training new models on problem solving and error recovery, and it must be
recorded, not discarded.

> User's exact ask: "We want each and every bit of problem solving process
> recorded. In fact each entry should probably include a standardized form
> that models fill out documenting key ideas, thoughts, processes, reasoning,
> etc behind each tool submission, passing, failing, or retry."

Plus a follow-up: "write a standard operating procedure (SOP) which is
administrative, and somehow enforce or constantly remind the model that they
need to be following these processes, and using these tools religiously."

**Decision the user made (via a direct question):** enforcement is a **HARD
GATE** — `episode_step` should *refuse* further attempts when the agent hasn't
filed a reasoning log. (They explicitly rejected "soft reminder only" and
"docs only".) See §4 for exact semantics and the one open sub-question.

A demonstration reasoning-log was already recorded for the GoL episode via the
existing `exposition` tool (`exposition_artifact_id`
`e197e421-3b0b-4bb9-8709-c8d83d94d8d0`, episode
`d8911237-8c2c-4b5d-95da-e25dc2ad633c`) — but `exposition` is the wrong home
(it's for mathematical prose about the *problem*, and it can't link to a
specific *attempt*). That's exactly why a dedicated `reasoning_logs` table +
tool is the right call.

---

## 2. Architecture context you need (learned the hard way, don't relearn it)

This is a Rust workspace. Two crates matter:

- `crates/proofsearch-core/` (package name `proofsearch_core`, note the
  underscore — `cargo build -p proofsearch_core`): DB schema, Lean gateway,
  models. **The trust-critical logic (`canonical_hash`, `to_pi_form`, kernel
  verification) lives here, NOT in the MCP crate.**
- `crates/proofsearch-mcp/` (package `proofsearch-mcp`, hyphen): the MCP
  server. `src/lib.rs` is one ~24k-line file holding every tool registration,
  dispatch arm, `do_*` handler, `Args` struct, and the entire test module.

**Design invariants this codebase holds sacred (violate = you broke the whole
philosophy):**

1. **Advisory metadata never gates proof status.** Every table except the
   kernel-backed episode/canonical ones is metadata-only and can never mark
   anything proved. `reasoning_logs` is metadata: it must *never* touch
   `episodes.outcome`, `episode_obligations.status`, budget, or certification.
   The gate rejects an *attempt from being submitted*; it never fabricates or
   alters a proof result.
2. **Append-only ledgers.** A lesson learned from a mistake is recorded
   *alongside* the mistake, never overwrites it. `reasoning_logs` is
   append-only (INSERT only, no UPDATE/DELETE handler).
3. **Server never infers, client declares.** Same pattern as `draft_moves` /
   `Decompose.sub_lemmas`: the agent fills out the form; the server just
   persists it. No LLM/inference code lives in this environment.
4. **The consolidated-tool pattern (epic #182).** Every multi-action tool is
   ONE `make_tool::<FooArgs>("foo", ...)` registration dispatching on an
   internally-tagged `enum FooAction` (`#[serde(tag = "type", rename_all =
   "snake_case")]`), one dispatch arm `"foo" => self.do_foo(args_val).await`,
   and a `tool_classification` entry in `environment_describe`. Current tool
   count is **41** (`grep -c 'make_tool::<' crates/proofsearch-mcp/src/lib.rs`).
   Adding `reasoning_log` makes it **42** — update the hardcoded
   `assert_eq!(list_res.tools.len(), 41)` and the `classified_tool_count` /
   `total_tool_count` literals in `environment_describe` (search for `41` near
   `test_mcp_list_tools_and_describe`; there's a running changelog comment
   chain above the assertion — append an entry).
5. **`episode_step` and `attempt_claim` were DELIBERATELY never consolidated
   or touched by epic #182** precisely because they're the highest-traffic,
   most foundational, most heavily-tested tools. You are now touching the most
   sensitive tool in the codebase. Tread carefully, byte-diff nothing you
   don't have to, and lean on the full test suite.

---

## 3. What's ALREADY DONE (green, committed-worthy, don't redo)

**`crates/proofsearch-core/src/db/schema_v1.rs`** — a `reasoning_logs` table +
two indexes appended to the end of the `V1_SCHEMA` raw-string constant (right
after `idx_interactive_proof_reconstructed_scripts_verified_attempt`, before
the closing `"#;` at ~line 1959). It's a brand-new table so it needs **no
separate migration function** — `init_db` applies `V1_SCHEMA` with
`CREATE TABLE IF NOT EXISTS` on every startup, so an existing DB picks it up
automatically on the next server restart. This already compiles
(`cargo build -p proofsearch_core`) and passes `cargo test -p proofsearch_core`
(0 failures). The exact DDL landed:

```sql
CREATE TABLE IF NOT EXISTS reasoning_logs (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    episode_revision INTEGER NOT NULL,
    action_attempt_id TEXT REFERENCES action_attempts(id),   -- nullable: planning precedes any attempt
    reasoning_kind TEXT NOT NULL,
    hypothesis TEXT,
    approach_summary TEXT NOT NULL,
    expected_outcome TEXT,
    actual_outcome TEXT,
    lesson_learned TEXT,
    confidence TEXT,
    author TEXT NOT NULL,
    created_at TEXT NOT NULL,
    CHECK(reasoning_kind IN ('initial_plan', 'retry_after_failure', 'strategy_pivot', 'error_diagnosis', 'success_retrospective', 'other')),
    CHECK(confidence IS NULL OR confidence IN ('low', 'medium', 'high'))
);
CREATE INDEX IF NOT EXISTS idx_reasoning_logs_episode ON reasoning_logs(episode_id, episode_revision);
CREATE INDEX IF NOT EXISTS idx_reasoning_logs_attempt ON reasoning_logs(action_attempt_id);
```

The full doc-comment above it (in the file) explains the design intent —
preserve it.

**Working tree:** `git status` shows only `M schema_v1.rs` (plus an unrelated
untracked `dev environment.zip` — leave that alone, not ours). Nothing is
committed yet; the user commits/PRs on their own cadence.

---

## 4. THE GATE — exact semantics + the one thing to confirm with the user

The user chose: *"After N attempts (e.g. 2) without an intervening
[reasoning-log] entry, further episode_step calls are rejected until one is
filed."*

**Implement it as a counted gate, not per-attempt** (per-attempt would break
literally every test and every benchmark run; the "N=2" framing is what they
picked). Concretely, inside `do_episode_step`, before the action executes:

```
count = SELECT COUNT(*) FROM action_attempts
        WHERE episode_id = ?1
          AND claimed_at > (most recent reasoning_logs.created_at for this episode,
                            or episode start if none)
```

i.e. **number of attempts submitted since the last reasoning log**. If that
count `>= REASONING_LOG_GATE_THRESHOLD` (a module-level `const i64`, default
`2`), reject with a clear `mcp_invalid_params` error before doing any work,
pointing the agent at the SOP and the `reasoning_log` tool.

- Put the threshold in a named const so it's a one-line tune:
  `const REASONING_LOG_GATE_THRESHOLD: i64 = 2;`
- The counting query is the fiddly part — simplest robust version: get
  `MAX(created_at)` from `reasoning_logs` for this episode (NULL if none), then
  `COUNT(*)` of `action_attempts` for this episode with `claimed_at >` that
  (or all attempts if NULL). Both timestamps are RFC3339 strings, lexically
  comparable. Verify `action_attempts.claimed_at` exists and is populated (it
  is — `claimed_at TEXT NOT NULL` on that table).
- **Gate placement:** do the check at the very top of `do_episode_step`, after
  arg parsing and the `cost_micros < 0` check, BEFORE the `tx1` block that
  calls `attempt_prepare`. Reject early so no state mutates. (Handler starts at
  `lib.rs:7552`; the `tx1` block starts ~7582.)
- **What the gate does NOT block:** it must still let a `give_up` through even
  if unlogged? — **confirm with the user.** My recommendation: gate ALL action
  types uniformly (including `give_up`), because "I gave up" is exactly the
  kind of decision worth a reasoning log. But a reasonable alternative is to
  exempt `give_up` so an agent can always terminate. This is the **one open
  product question** — surface it.
- **Also decide (confirm with user):** should the gate count only apply once
  the episode has had at least one attempt, so the *first* attempt is always
  free (letting an agent make an opening move, then requiring a log before the
  next)? With threshold=2 and "attempts since last log," the first two attempts
  are free and the 3rd is blocked. That's the natural reading of "after N=2."
  State this explicitly in the error message so agents understand the rhythm.

**Error message should be actionable**, e.g.:
> "reasoning_log required: you've submitted N attempts on this episode since
> your last reasoning log (limit N). File a `reasoning_log` (action `add`) for
> episode `<id>` documenting your hypothesis / what you tried / what the last
> failure taught you, then retry this step. See docs/sop-reasoning-logs.md."

---

## 5. The `reasoning_log` MCP tool to build (template: `exposition`)

`exposition` is the closest structural template — copy its shape. Reference
line numbers in `crates/proofsearch-mcp/src/lib.rs`:

- Args structs `ExpositionAddArgs` / `ExpositionObserveArgs`: **3153–3183**
- `enum ExpositionAction` + `ExpositionArgs` wrapper: **3195–3235**
- Closed-vocabulary consts + `SELECT` const + `map_*_row` + `*_json` helpers:
  **4769–4817**
- Dispatcher `do_exposition` + `do_exposition_add` + `do_exposition_observe`:
  **10862–10958**
- `make_tool::<ExpositionArgs>("exposition", ...)` registration: search
  `make_tool::<ExpositionArgs>` (~13xxx)
- `tool_classification` `"exposition"` entry in `environment_describe`: search
  `"exposition": {` (~near 13xxx)
- Dispatch arm `"exposition" => self.do_exposition(args_val).await,`: search it
  (~14xxx)

Build `reasoning_log` the same way:

- `ReasoningLogAction` enum, internally tagged, two variants:
  - **`add`**: `episode_id` (required), `episode_revision` (required i64),
    `action_attempt_id` (optional), `reasoning_kind` (required, validate
    against the 6-value vocab via a `REASONING_KINDS` const +
    `validate_one_of`), `hypothesis` (opt), `approach_summary` (required,
    non-empty), `expected_outcome` (opt), `actual_outcome` (opt),
    `lesson_learned` (opt), `confidence` (opt, validate `low|medium|high`),
    `author` (required, non-empty). Handler: validate vocab, require
    `episode_id` exists (`require_row_exists(&tx, "episodes", ...)`), require
    `action_attempt_id` exists if given, INSERT one row, return the row JSON.
  - **`observe`**: `episode_id` (required). Return all reasoning_logs for that
    episode ordered `created_at ASC, id ASC`.
- Naming: tool name `reasoning_log` (singular, matches `expert_review`,
  `semantic_skeleton` convention). Struct `ReasoningLogArgs`. Handlers
  `do_reasoning_log` / `do_reasoning_log_add` / `do_reasoning_log_observe`.
- Response should echo the honesty framing: reasoning logs are process
  metadata, never proof, never change outcome/certification/training
  eligibility (mirror exposition's `"policy"` line).

---

## 6. The blast radius (measured, not guessed) — for the gate's test fallout

- **`episode_step` test call sites in `lib.rs`: 51.** `attempt_claim`: 52.
  With threshold=2, a test that does claim→step **once or twice per episode**
  won't trip the gate; only tests that fire **3+ attempts on one episode
  without a reasoning_log** break. So the real fallout is likely FAR smaller
  than 51 — **measure it**: implement the gate, run
  `cargo test -p proofsearch-mcp 2>&1 | grep -E "FAILED|test result"`, and only
  fix the tests that actually fail. Do NOT pre-emptively edit all 51.
  - Fix pattern for a broken test: inject a `reasoning_log` `add` call (via
    `peer.call_tool(CallToolRequestParams::new("reasoning_log")...)`) between
    the offending attempts, OR — cleaner for multi-attempt loop tests — file
    one reasoning_log per iteration. Keep response-content assertions on the
    step results unchanged.
  - There's a shared test helper worth checking for (many tests build episodes
    via a common setup); if one exists, threading a reasoning_log into it may
    fix many at once.
- **`crates/proofsearch-mcp/examples/`: `putnam_runner.rs` and
  `import_putnambench.rs` call `episode_step` in loops** (8 grep hits). These
  are real batch runners that WILL break under the gate. Add a `reasoning_log`
  `add` call in their per-problem loop before each episode_step (a templated
  one-liner documenting "benchmark auto-run, problem X, attempt N" is fine —
  these are machine runs, but they should still leave a trail). Note: these
  examples already reference some pre-consolidation tool names as raw strings
  (known pre-existing debt from epic #182, flagged but out of scope then) — if
  you're in there anyway, fixing those stale names is a welcome drive-by but
  not required.
- Also update the metrics/`environment_describe` self-count assertions per §2.4.

---

## 7. SOP document to write

`docs/sop-reasoning-logs.md` — administrative SOP, referenced by the gate's
error message, `readme_first`, and the tool descriptions. Contents:

1. **Purpose:** why every problem-solving step (plan, attempt, failure,
   retry, pivot, success retrospective) must be logged — training-data value
   of error-recovery traces; the environment ledger is the only durable record
   (local scratch work is invisible).
2. **The standardized form:** the reasoning_kind vocabulary and each field's
   intent (hypothesis, approach_summary, expected vs actual, lesson_learned,
   confidence). Give a filled-in worked example — reuse the real GoL example
   (recursion-depth wall → wrong type-encoding hypothesis → empirical
   128/256 calibration → chunked-decide fix → embedding parse bugs → certified;
   the full narrative is already in exposition artifact
   `e197e421-...` on episode `d8911237-...`, or in this session's transcript).
3. **The cadence rule (the gate):** you get N=2 attempts per episode between
   logs; file a reasoning_log documenting what you learned before continuing.
   Explain the rhythm so it feels like a natural checkpoint, not a tax.
4. **When each `reasoning_kind` applies**, with a one-line trigger for each.
5. Cross-link the `reasoning_log`, `draft`, and `exposition` tools and when to
   use which (`draft` = pre-formalization informal content; `exposition` =
   mathematical prose about the problem; `reasoning_log` = the agent's own
   process across attempts).

---

## 8. Docs/discoverability so models actually follow it "religiously"

The root cause of the original problem: a tool nobody's *reminded* to use
doesn't get used (I defaulted to Bash scratch files this whole session because
nothing nudged me otherwise). So:

- **`readme_first`** (the `do_readme_first` handler / its big JSON response,
  search `readme_first`): add a top-level key like `reasoning_log_sop`
  stating the requirement plainly — "every episode_step must be preceded by a
  reasoning_log within N attempts; document your process; see
  docs/sop-reasoning-logs.md" — so it's in the very first thing any agent
  reads.
- **`episode_step`'s `make_tool` description** (`lib.rs:13283`): add a sentence
  that a reasoning_log is required within N attempts and that the call will be
  rejected otherwise, pointing to `reasoning_log` and the SOP.
- **`reasoning_log`'s own description**: state it's the SOP-mandated process
  log and the gate that enforces it.
- **The gate's rejection error message itself** is the most important nudge —
  it fires exactly when compliance lapsed. Make it teach, not just refuse.
- Also worth surfacing in `environment_describe`'s `epistemic_rules` or a new
  `reasoning_sop` capability block if you want it machine-discoverable.

---

## 9. Bonus finding worth folding in (from the GoL playtest)

The `episode_step` schema already documents the "FLATTENED-SEQUENCE TRAP"
(inline `by ...;` greedily consuming following tactics — parenthesize them).
The playtest surfaced a **second, undocumented** submission gotcha worth adding
to the `episode_step` description: **a multi-line tactic proof that relies on
relative indentation (bullets `·`, `case` blocks) can compile fine as a
standalone local `.lean` file but FAIL when submitted, because the server's
line-embedding of the proof_term doesn't preserve the same column-reference
semantics.** The robust mitigation: flatten multi-step proofs to one physical
line with `;` separators and parenthesize every inline `by <tactic>;`. This
cost 2 of the 4 GoL attempts and is currently documented nowhere. Consider
adding a one-line warning to the `episode_step` description. (Optional, but
it's real and it'll bite the next agent.)

---

## 10. Definition of done

1. `reasoning_log` tool implemented (add/observe), registered, classified,
   dispatched; tool count 41→42 with all self-count assertions updated.
2. Hard gate live in `do_episode_step` (threshold const, early rejection,
   actionable error) — with the two §4 sub-questions confirmed with the user.
3. `cargo build --workspace` clean; `cargo test --workspace` **0 failures**
   (fix only the tests that actually trip the gate).
4. `putnam_runner.rs` / `import_putnambench.rs` file reasoning_logs in-loop.
5. `docs/sop-reasoning-logs.md` written; `readme_first` + `episode_step` +
   `reasoning_log` descriptions reference it.
6. `README.md` tools table updated (new tool + count).
7. **Playtest live** after rebuild+restart: create an episode, fire 2 steps
   with no reasoning_log → 3rd rejected with the SOP error; file a
   reasoning_log → next step accepted; `reasoning_log observe` returns the
   entries. (The running server is currently the pre-change binary and has no
   `reasoning_logs` table yet — the table lands on the next `init_db` at
   restart. User rebuilds the release binary + restarts the host; only they can
   do that step. Kill stale `proofsearch-mcp.exe` procs first — there were 3
   leaked ones earlier this session holding a file lock on the release binary.)

---

## 11. Two decisions to get from the user before coding the gate

1. **Does the gate block `give_up`?** (Recommend: yes, gate it — quitting is
   worth a reason. Alt: exempt so an agent can always terminate.)
2. **Threshold value / first-attempt-free semantics?** Default proposed:
   `REASONING_LOG_GATE_THRESHOLD = 2` (two free attempts per episode between
   logs). Confirm they don't actually want strict per-attempt (=1), which is
   maximal training coverage but breaks/《requires touching》 far more tests and
   makes benchmark runs log-heavy.

Everything else is unblocked. The schema's in and green; `exposition` is your
copy-paste template; the blast radius is much smaller than the raw call-site
count suggests. Good luck.
