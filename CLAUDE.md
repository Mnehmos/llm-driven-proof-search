# Operating Doctrine

Distilled from *The Vibe Coder's Bible* (CC BY 4.0).

## Mission

Trust the model to propose. Trust the system to verify. Trust the trace to
remember.

Vibe coding lowers the cost of generation. It does not lower the cost of
responsibility. Every change you produce is a proposal until it passes
validation and a human or a system accepts it. Generation is cheap. Being wrong
in a way nobody catches is expensive. Act accordingly.

## The Loop: Propose, Validate, Commit

**Propose.** Draft the change. Keep it scoped to one logical unit—one function,
one endpoint, one behavior. A proposal touching thirty files is not a proposal;
it is an unreviewable event.

**Validate.** Automated controls run first: tests, type check, lint, schema
validation. Then human review. Never skip to commit because the diff "looks
right"—plausible and correct are different properties, and you cannot tell them
apart from the inside.

**Commit.** Only validated output crosses into repository state, database state,
or any other durable, public, or executable form. A commit is a claim of
correctness. Make it deliberately, not by default.

Before reporting any task complete, run:

```powershell
cargo build --workspace
cargo test --workspace
cargo fmt --all -- --check
```

If a command cannot be run or the repository has a pre-existing failure, say so
explicitly. Do not claim success you did not check.

## The Hierarchy of Controls

When you notice yourself about to rely on a warning, an instruction, or "be
careful" language to prevent a failure, stop and ask whether a stronger control
is available. In order of reliability, strongest first:

1. **Elimination**—remove the capability so the failure cannot happen. No
   production credentials in your context. No destructive commands without an
   explicit, scoped confirmation step. No direct writes to state that a
   deterministic component should own.
2. **Substitution**—replace a dangerous, broad capability with a narrow, typed
   one. A migration tool instead of a raw SQL shell. A task runner with named
   commands instead of an open shell. A sandbox client instead of a live payment
   API.
3. **Engineering controls**—tests, type checks, schema validators, CI gates that
   fail automatically and do not depend on anyone remembering to look. If a rule
   matters, it belongs here before it belongs in a prompt.
4. **Administrative controls**—issues that define scope before work starts, PR
   checklists that name what was verified, ADRs for decisions that would
   otherwise be relitigated, handoffs that carry context forward.
5. **PPE**—careful prompting, visible uncertainty, human review. Real, but the
   last line of defense, not the first. If PPE is the only thing standing between
   a proposal and a bad outcome, say so and ask whether a stronger control should
   exist instead.

A rule that lives only in a prompt is a hope. A rule enforced by a validator is
a fact. Move rules up the hierarchy whenever you can.

## Boundaries

Do not:

- Commit secrets, API keys, or credentials in code, fixtures, or logs.
- Run destructive or irreversible commands without explicit, scoped approval
  for that specific action.
- Change production configuration, infrastructure, or access control without
  review.
- Weaken, skip, or delete a test to make a change pass.
- Mix unrelated cleanup, refactors, or scope expansion into a requested change.
  Note improvements you notice; do not silently make them.
- Invent APIs, file paths, commands, or project facts you have not verified
  against the actual repository.

## If This Project Puts a Model in Its Own Runtime Path

Skip this section for ordinary application code. It applies only if any part of
what you are building calls a model at runtime—narrating state, proposing an
action, drafting a claim, or making any decision a user or another system will
see live.

Before granting a new runtime capability, name explicitly:

- **What the model may propose**—the shape of its output, nothing implied beyond
  it.
- **What owns truth**—the deterministic component (database, rules engine,
  permission table, solver) the proposal must be checked against. Never the model
  itself.
- **What validates the proposal before it commits**—schema, then authorization,
  then domain legality. A structurally valid proposal is not an authorized one.
- **The commit boundary**—the exact event where the proposal becomes a database
  write, an executed action, a published claim, or other user-visible state.
- **What happens to a rejected proposal**—discard, bounded repair, escalate, or
  trace. Never an unbounded retry loop.
- **Who owns randomness**—if the system needs chance, name the deterministic
  component that seeds and logs it. Model output variation is not typed
  randomness and must never stand in for it.

Fill out one `ARCHITECTURE_CARD.md` per runtime capability before you build it,
not after.

## Verification Discipline

- Read the diff before claiming a task is done. Do not summarize what you
  intended; report what actually changed.
- State what you verified and how. "Tests pass" is a claim—name which suite, and
  what it covers.
- Name assumptions you made that were not explicitly confirmed. An unstated
  assumption is a bug waiting for the wrong environment.
- If you are not confident something is correct, say so plainly rather than
  presenting a guess with the same confidence as a checked fact. Plausibility is
  not authority.

## Handoff

When a session ends with work incomplete, leave a handoff a future session—or a
different agent—can act on without reconstructing your reasoning from the diff:

- What changed, and why—the decision, not just the commit.
- What was deferred, and why.
- Open questions that need a human before work continues.
- One specific next step, not a list of options.

Do not redirect to a chat log or a conversation the next reader cannot access.
If it mattered, write it down.

## Definition of Done

A change is done when it is built (compiles, no unresolved references), tested
(new behavior covered by tests that would fail without it), documented (anything
public-facing reflects current behavior, not intent), understood (you can explain
what it does and why, not just that it passed), and recoverable (there is a known
path to undo it if it is wrong).

For a runtime capability, done also requires evidence—not just code that should
produce it—that a malformed, unauthorized, or illegal proposal cannot silently
cross its commit boundary. A capability tested only on the happy path is not
done.

## Project Context

This repository is a Rust workspace for a verifier-backed LLM-driven proof-search
environment. `proofsearch-core` owns the SQLite schema, typed action state
machine, Lean gateway, canonical hashing, and kernel-backed truth. The
`proofsearch-mcp` crate exposes the MCP protocol and advisory ledgers. The server
does not call a model: the external agent host is the policy; client-authored
reasoning and proof terms remain untrusted proposals until deterministic checks
accept them.

The trust-critical invariant is that advisory metadata never marks a theorem
proved. Only the pinned Lean verifier, reached through the tracked attempt path,
can produce a kernel-backed outcome. Ledgers are append-only wherever the schema
defines them that way, and the server must not infer client reasoning.

### Key Files

- `crates/proofsearch-core/src/db/schema_v1.rs`—SQLite V1 schema and append-only
  ledgers.
- `crates/proofsearch-core/src/orchestrator/step.rs`—typed action preparation,
  verification, and commit state machine.
- `crates/proofsearch-mcp/src/lib.rs`—MCP schemas, registrations, dispatch,
  handlers, environment description, and MCP-level tests.
- `README.md` and `docs/`—public protocol and operational documentation.
- `docs/sop-reasoning-logs.md`—mandatory process-recording SOP and gate cadence.

### Do Not Touch Unless Explicitly in Scope

- User databases and WAL/SHM files (`*.db`, `*.db-wal`, `*.db-shm`) or their
  backups.
- Archives such as `dev environment.zip` and `tunnel.zip`.
- Generated build output under `target/`.
- Unrelated dirty-worktree changes or untracked handoff artifacts.
- `formal-conjectures/` without first reading its subtree `AGENTS.md`.

Do not commit or push unless the user explicitly asks. Preserve user changes and
keep requested work isolated in the diff.
