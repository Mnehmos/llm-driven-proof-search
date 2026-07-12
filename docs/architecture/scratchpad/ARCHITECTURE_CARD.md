# ARCHITECTURE_CARD: recorded Lean scratchpad (`scratchpad` tool)

One card per runtime capability, per the Operating Doctrine. This capability
lets an external agent **run arbitrary Lean scratch source inside the
environment** — `#eval` searches, trial `example`/`def` snippets, compile
checks — and captures the input **and** output as append-only, episode-linked
training data, so the reconnaissance that today leaks into untracked Bash /
local `lake env lean` stays in the ledger.

## Motivating failure (why this exists)

During a Game-of-Life proving session an agent (me) did ~8 untracked local
`lake env lean` iterations — `#eval` witness searches, recursion-depth
calibration, trial compiles — and only the 4 polished `episode_step`
submissions became evidence. The problem-solving/error-recovery process — the
training gold — evaporated. The `reasoning_log` gate records the agent's
*narration* of its process but not the *executable* reconnaissance itself. This
tool records the executable part.

**Hard truth that shapes the whole design:** the MCP server has no visibility
into the agent's shell and therefore *cannot detect or block* out-of-band Bash.
Enforcement is impossible. The only workable strategy is to make the recorded
scratchpad the **path of least resistance** — give the agent exactly what Bash
gave it (real Lean execution against the pinned toolchain + the episode's
manifest) so reaching for Bash becomes the harder, worse choice. This is an
administrative + affordance control, never a technical gate.

## What the model may propose

Arbitrary Lean source text (`source`) to be run once against the pinned
toolchain, scoped to an episode (so the compile uses that episode's problem's
immutable import manifest). The agent proposes:

- helper `def`s / `abbrev`s, `example ... := by ...` trial proofs, `#eval`
  expressions (the witness/search reconnaissance), `#check`, `set_option
  maxRecDepth ... in ...`, etc.

The proposal's shape is: "compile this text and tell me everything Lean said,
including `#eval` output." Nothing more is implied — in particular, **a
scratchpad run never proposes that anything is proved.**

## What owns truth

- **Proof truth: unchanged — the pinned Lean kernel reached only through
  `episode_step`'s tracked attempt path.** The scratchpad owns *no* proof
  authority. A scratch `example : P := by decide` that "passes" is SEARCH
  EVIDENCE that a tactic plausibly works, exactly like `proof_session`'s mock
  backend or `empirical_search` — it is not, and can never become, a proof of
  any obligation. To make a real claim the agent must still submit through
  `episode_step`.
- **Execution truth (what Lean actually said): the pinned toolchain**, via the
  same `RealLeanGateway`/`run_lean_json` path `episode_step` uses. The recorded
  diagnostics/eval output are a faithful transcript of a real Lean invocation,
  not a client assertion — same anti-fabrication principle as
  `root_statement_hash` (server-computed, never client-supplied).

## What validates the proposal before it commits

In order, before any Lean process spawns:

1. **Episode exists** and is resolvable (`require_row_exists` on `episodes`);
   the run is scoped to it and uses its problem's `import_manifest_json`.
2. **Source sanitization** (mirrors `crate::lean::module`'s `FORBIDDEN_TOKENS`
   but with a scratch-appropriate list). The scratchpad must **ban**:
   - `import` lines in client source — the **server** prepends the episode's
     manifest imports (via `build_import_block`); a client `import` is how you'd
     smuggle in an unvetted trusted base, and it's also just redundant.
   - `unsafe`, `axiom`, `opaque`, `partial`, `implemented_by`,
     `@[extern ...]`, and any `IO`-typed `#eval` / `unsafeIO` / process-spawning
     or filesystem-touching evaluation. **This is the security line:** Lean
     `#eval` of an `IO` action executes with the server process's privileges.
     Pure `#eval` (the witness searches we want) is fine; `IO` `#eval` is a
     sandbox escape and must be rejected pre-execution.
   - `native_decide` — not for soundness (scratch is untrusted anyway) but so a
     "scratch says it works" result can never be confused with a kernel result;
     keep the kernel/compiler distinction crisp.
   - It **allows** everything else, notably `#eval`, `def`, `example`, `#check`,
     `set_option ... in`. Allowing these is the entire point — banning them
     (the "compile-check only" option) would not replace the Bash use that
     motivated this.
3. **Resource bounds:** a hard wall-clock timeout (reuse `run_lean_json`'s
   timeout + taskkill machinery; default e.g. 60s, same order as an attempt),
   and an output-size cap on captured diagnostics/eval text (truncate + flag,
   never let a runaway `#eval` blow up the DB row).

A proposal failing (1) or (2) is rejected outright — **no Lean runs, no row is
written as an execution.** (Optionally record the *rejected attempt* itself as a
scratch row with `status='rejected'` — recommended, since "the agent tried to
run IO in scratch" is itself useful signal — but it must never have executed.)

## The commit boundary

The single event where a scratchpad run becomes durable state: **one INSERT
into the append-only `scratchpad_entries` table**, linking `episode_id`, the
sanitized `source`, the captured `diagnostics_json` + `eval_output_json` (or a
combined `output_json`), a boolean `lean_success`, `wall_time_ms`, `status`
(`ran` | `rejected` | `timed_out` | `truncated`), and `created_at`.

**This table has NO column able to hold kernel evidence, mark an obligation
proved, set fidelity, or alter an episode outcome/budget/certification** — that
structural absence (not a CHECK, not a runtime guard) is the proof-safety
guarantee, exactly as the semantic_skeleton / expert_review tables do it. The
commit writes reconnaissance, and only reconnaissance.

## What happens to a rejected proposal

- **Sanitization/validation rejection:** return a clear `mcp_invalid_params`
  naming the banned token / missing episode; optionally persist a
  `status='rejected'` row (no execution occurred). Never an unbounded retry
  loop — the agent fixes the source and calls again.
- **Execution that fails to compile** (the normal, useful case — a trial proof
  that doesn't work, a `#eval` on an undecidable instance): this is **not a
  rejection**, it's a successful scratch run whose recorded output happens to
  contain errors. Recorded verbatim, `lean_success=false`. That IS the training
  data.
- **Timeout / oversized output:** kill the process (existing taskkill path),
  record `status='timed_out'`/`'truncated'` with whatever partial output was
  captured. Bounded, never hangs.

## Who owns randomness

None required. A Lean compile is deterministic given (source, manifest,
toolchain); there is no sampling, no model call, no chance element in this path.
If a future scratch feature wants randomized search seeds, the seed is
client-supplied text inside `source` and recorded verbatim like everything else
— there is no separate typed-randomness component to own here.

## Trust-boundary invariant (the one-line version for reviewers)

> A `scratchpad` run executes real Lean and records a faithful transcript, but
> its result is SEARCH EVIDENCE and never proof authority: it cannot mark any
> obligation proved, cannot set fidelity, cannot change an episode outcome, and
> the only path to a kernel-backed claim remains `episode_step`. Its value is
> that the reconnaissance is now *recorded* (and training-visible), not that it
> is trusted.

## Training-data treatment (per the product decision)

Scratchpad entries **are included in `training_export`** as reconnaissance /
process data, clearly labeled untrusted (never proof). They sit alongside the
episode trajectory and `reasoning_logs` to form the complete problem-solving
trace the capability exists to capture. Standard secret-scrubbing
(api_key/auth_token/etc., as `training_export` already does) still applies to
the recorded source/output.
