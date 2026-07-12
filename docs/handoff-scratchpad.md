# Handoff: recorded Lean scratchpad (`scratchpad` MCP tool)

**For:** Codex (ChatGPT 5.6 sol) — the same builder that landed `reasoning_log`.
**From:** Claude (design session, 2026-07-10)
**Repo:** `f:\Github\mnehmos.llm-driven-proof-search.environment` (branch `develop`)
**Design spec / trust reasoning:** read
`docs/architecture/scratchpad/ARCHITECTURE_CARD.md` **first** — it's the
doctrine-mandated card and has the full trust-boundary/security reasoning this
handoff assumes. This file is the build recipe.

**Product decisions already made by the user (don't re-litigate):**
1. **Full Lean scratch** — run arbitrary source including `#eval`, return all
   diagnostics + eval output. (Not compile-check-only, not a passive text
   store.)
2. **Recorded + fed to training** — entries are included in `training_export`,
   labeled untrusted.

---

## 1. Why, in one paragraph

An agent's real reconnaissance — `#eval` witness searches, trial compiles,
recursion-depth calibration — currently happens in untracked Bash / local `lake
env lean` and evaporates. `reasoning_log` records the *narration*; this records
the *executable* recon. **The server cannot detect Bash**, so this is not a
gate — it's an affordance: make a recorded scratchpad strictly easier/nicer than
Bash so agents stop reaching for the shell. It runs real Lean but is SEARCH
EVIDENCE, never proof authority.

## 2. The good news: 80% of the hard part already exists

`crates/proofsearch-core/src/lean/mod.rs`:

- **`RealLeanGateway::run_lean_json(&self, file_content, file_stem, timeout)`**
  (mod.rs:129) already: writes arbitrary source to an isolated tempdir, runs
  `lake env lean --json` in the project dir, captures **stdout JSON diagnostic
  lines + stderr + process success**, enforces a wall-clock timeout, and
  `taskkill`s a hung process. It's currently `private`, used by
  `verify_exact`/`verify_module`.
- **`#eval` output is ALREADY captured**: in `lean --json` mode, `#eval` results
  come back as `severity: "info"` diagnostic lines in the same stdout stream
  `run_lean_json` parses into `lines`. So "capture eval output" is free — it's
  already in the returned `Vec<serde_json::Value>`.
- **`RealLeanGateway::build_import_block(import_manifest, approved_dependency_ids)`**
  (mod.rs:183) renders the manifest into `import ...` lines + `open` directives.
  Reuse it (pass `&[]` for dependency ids) to prepend the episode's manifest.
- **`crate::lean::module` sanitization** (module.rs:38/57): `FORBIDDEN_TOKENS`
  = `sorry, admit, axiom, unsafe, opaque, native_decide` and a
  declaration-keyword list. Your scratch ban-list is *different* (see §4) —
  reference this for the token-scan technique, don't reuse the list verbatim.

So the core is: a new gateway method that is `run_lean_json` + manifest prefix +
scratch sanitization + structured result. Everything else is the familiar
tool/table/export plumbing.

## 3. Core crate work (`proofsearch-core`)

Add to the `LeanGateway` trait (mod.rs:33) a new method, default-fails-closed
like `verify_module`:

```rust
/// Runs arbitrary client scratch source once against the pinned toolchain +
/// `import_manifest`, returning a faithful transcript (diagnostics + #eval
/// output). SEARCH EVIDENCE ONLY — this can never verify an obligation; it is
/// deliberately separate from verify_exact/verify_module. Default fails closed.
fn run_scratch(
    &self,
    source: &str,
    import_manifest: &[String],
    timeout: Duration,
) -> Result<ScratchRunResult, String> {
    let _ = (source, import_manifest, timeout);
    Err("this gateway cannot run scratch".to_string())
}
```

`ScratchRunResult` (new struct in mod.rs): `lean_success: bool`,
`diagnostics: Vec<...>` (reuse the parsed-diagnostic shape `verify_exact`
already produces — message/kind/severity/line), `eval_output: Vec<String>`
(the `severity=="info"` lines, i.e. `#eval`/`#check` output, split out for
legibility), `stderr: String`, `wall_time_ms: i64`, `truncated: bool`.

`RealLeanGateway::run_scratch` impl:
1. `build_import_block(import_manifest, &[])` → prepend imports; append the
   `open` directives after imports (same ordering `assemble_root_theorem_source`
   uses — imports first, then opens). **Do not** wrap the client source in a
   namespace/theorem; scratch is free-form top-level Lean (that's why `#eval`
   works).
2. Assemble `"{imports}\n{opens}\n{sanitized_source}\n"`, call `run_lean_json`
   with a distinct file_stem (e.g. `"Scratch"`) and the timeout.
3. Split `lines` into `eval_output` (severity `info`) vs `diagnostics`
   (error/warning). Time it (wall_time_ms). Cap total captured text
   (e.g. 64 KiB) → set `truncated`.
4. Map a timeout `Err` from `run_lean_json` into a distinct signal the handler
   turns into `status='timed_out'` (don't swallow it as a generic error).

`MockGateway` (test double, in the mcp crate's tests + wherever the core mock
lives): implement `run_scratch` to return a canned deterministic result so unit
tests don't spawn Lean.

**Sanitization** (new pure fn, put it next to the module sanitizer or in the
gateway): scan `source` and reject (return `Err`/a typed rejection) if it
contains, as whole tokens / line-starts:
- `import` (server owns imports) — reject a client `import` line.
- `unsafe`, `axiom`, `opaque`, `partial`, `implemented_by`, `extern`,
  `native_decide`.
- **IO execution:** reject `#eval` whose expression is `IO`-typed. Detecting the
  *type* statically is hard; the pragmatic, safe rule is a **token ban** on the
  IO surface in scratch: reject `IO.`, `IO ` (as a type), `unsafeIO`,
  `System.`, `IO.FS`, `IO.Process`, `run_cmd`, `#eval show IO`. Err on the side
  of banning — pure `#eval` (numbers, lists, `Option`, `Bool`, `decide`
  results — the actual witness-search use) needs none of these. Document the
  ban-list in one place with a comment that it's the sandbox-escape line, and
  make it a `const` array so it's a one-line tune.
- Keep it a whole-word / line-aware scan like `module.rs` does (don't reject
  `imported` because it contains `import`).

Add a `run_scratch` unit test against `RealLeanGateway` behind the same
lean-available guard the other gateway integration tests use (there's a
`#[cfg]`/env gate — match it), plus pure sanitizer unit tests (no Lean needed):
IO-eval rejected, client `import` rejected, a benign `#eval 2+2` passes the
sanitizer.

## 4. Schema (`proofsearch-core/src/db/schema_v1.rs`)

Append a new append-only table to `V1_SCHEMA` (same as `reasoning_logs` landed —
new table, `CREATE TABLE IF NOT EXISTS`, no migration fn needed; `init_db`
picks it up on restart):

```sql
CREATE TABLE IF NOT EXISTS scratchpad_entries (
    id TEXT PRIMARY KEY,
    episode_id TEXT NOT NULL REFERENCES episodes(id),
    source TEXT NOT NULL,
    output_json TEXT NOT NULL,       -- {diagnostics:[...], eval_output:[...], stderr:"..."}
    lean_success INTEGER NOT NULL,   -- 0/1: process compiled with no error diagnostics
    status TEXT NOT NULL,            -- 'ran' | 'rejected' | 'timed_out' | 'truncated'
    wall_time_ms INTEGER,
    created_at TEXT NOT NULL,
    CHECK(status IN ('ran', 'rejected', 'timed_out', 'truncated'))
);
CREATE INDEX IF NOT EXISTS idx_scratchpad_entries_episode ON scratchpad_entries(episode_id, created_at);
```

Note the **deliberate absence** of any status/outcome/fidelity column that could
hold proof authority — that structural absence is the proof-safety guarantee
(mirror the doc-comments on `semantic_skeletons` / `expert_reviews`). Write a
similar doc-comment.

## 5. MCP tool (`proofsearch-mcp/src/lib.rs`) — template: `reasoning_log`

You built `reasoning_log` from the `exposition` template; build `scratchpad`
the same way. Action-enum `ScratchpadAction`, tool name `scratchpad`:

- **`run`**: `episode_id` (required), `source` (required, non-empty). Handler:
  `require_row_exists(episodes)`; read the problem's `import_manifest_json` from
  `problem_versions` (join via the episode — see how `episode_step`'s handler
  gets `import_manifest`, mod.rs-side around lib.rs:3841/6580 shows the
  `SELECT import_manifest_json FROM problem_versions` pattern); sanitize; call
  `self.gateway.run_scratch(...)` with a timeout const
  (`const SCRATCH_TIMEOUT_SECS: u64 = 60;`); INSERT one `scratchpad_entries`
  row; return the transcript + an honest `trust` line
  (`"SEARCH EVIDENCE, never proof; only episode_step reaches the kernel"`).
  **This is the first metadata-family tool that calls `self.gateway`** — most
  don't; `episode_step` is your reference for how the handler holds and invokes
  the gateway.
- **`observe`**: `episode_id` (required). Return that episode's scratch entries
  in `created_at ASC` order.

Then, exactly as for `reasoning_log`:
- One `make_tool::<ScratchpadArgs>("scratchpad", "...")` registration; tool
  count **42 → 43** — update `assert_eq!(list_res.tools.len(), 42)` and the
  `classified_tool_count`/`total_tool_count` literals + the changelog comment
  chain in `environment_describe`.
- One dispatch arm `"scratchpad" => self.do_scratchpad(args_val).await,`.
- One honest-union `tool_classification` entry (`run` = mutating + invokes Lean,
  read-only-ish side effects none-on-proof-state; `observe` = read_only). Trust
  level: untrusted execution transcript, never proof. Cost surface: `run` spawns
  a real Lean process (verifier_side wall time) — say so.

## 6. Training export inclusion (the product decision)

Find the `training_export` render path (search `training_export` in lib.rs;
it's one of `proof_export`/`trajectory_export`'s format arms). Add scratchpad
entries for the episode as a labeled section — `kind: "scratchpad_recon"`,
`trusted: false` — alongside the trajectory/reasoning_log data. Apply the same
secret-scrubbing pass already used there (api_key/auth_token/…). Keep it clearly
marked untrusted so a training consumer never treats a scratch "pass" as a
proof.

## 7. Discoverability — make it the path of least resistance (the whole point)

Since you can't block Bash, you must *pull* agents here:
- **`readme_first`**: add a `scratchpad` key — "Do your `#eval` searches, trial
  compiles, and recon with the `scratchpad` tool, NOT an external shell — it
  runs the same pinned Lean, uses this episode's imports, and records the work
  as training data. Local/Bash Lean is invisible to the environment and lost."
- **`episode_step` description**: one line — "explore candidate proofs with
  `scratchpad` (recorded) before submitting."
- **`reasoning_log` / SOP** (`docs/sop-reasoning-logs.md`): add a short section
  directing all executable recon into `scratchpad`, and update the CLAUDE.md /
  SOP language that says "keep scratch work inside the tracked workspace" to
  name the tool explicitly.
- **`environment_describe`**: consider a small capability note so it's
  machine-discoverable (the reasoning-log review flagged that `environment_describe`
  doesn't surface `docs/sop-reasoning-logs.md`; fold both fixes in here).

## 8. Definition of done

1. `LeanGateway::run_scratch` + `ScratchRunResult` + `RealLeanGateway` impl +
   `MockGateway` impl; sanitizer with IO/import/unsafe bans as a tunable const.
2. `scratchpad_entries` table; `scratchpad` tool (run/observe) registered,
   classified, dispatched; tool count 42→43, all self-count assertions updated.
3. Training-export inclusion, untrusted-labeled + secret-scrubbed.
4. Discoverability hooks (readme_first, episode_step, SOP, environment_describe).
5. `cargo build --workspace` clean; `cargo test --workspace` 0 failures
   (add: sanitizer unit tests; a gateway `run_scratch` test behind the
   lean-available guard; an end-to-end `scratchpad run`→`observe` MCP test using
   MockGateway; confirm no existing test trips).
6. ARCHITECTURE_CARD (already written, `docs/architecture/scratchpad/`) stays in
   sync if you change anything material.
7. **Live playtest after rebuild+restart** (user's step — only they can replace
   the running binary; kill stale `proofsearch-mcp.exe` PIDs first): `scratchpad
   run` a pure `#eval` search on a real episode → returns eval output, recorded;
   `scratchpad run` an `IO`-eval → rejected pre-execution, nothing ran; a trial
   `example := by decide` that fails → recorded with `lean_success=false`;
   `scratchpad observe` → returns the entries; confirm `training_export` for the
   episode contains the scratch section labeled untrusted.

## 9. Two things to confirm with the user before/while building

1. **Timeout + output cap values** — I proposed 60 s wall-clock and 64 KiB
   captured output. Fine as defaults; confirm they don't want scratch to be
   cheaper/faster-failing than a real attempt (a shorter scratch timeout, e.g.
   30 s, might be the better default since recon should be quick).
2. **IO ban strictness** — the token-ban on the IO surface is deliberately
   conservative and will reject some legitimate pure-looking code that mentions
   those names in a string/comment. Confirm "reject-and-make-the-agent-reword"
   is acceptable vs. investing in real type-level IO detection later. (Recommend
   ship conservative now, refine later.)

Everything's unblocked and the gateway heavy-lifting already exists. Same
build-verify-handoff rhythm as `reasoning_log`. Good luck.
