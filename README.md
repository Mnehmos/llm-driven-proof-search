# ChatDB — Verifier-Backed RL Environment for LLM-Driven Proof Search

[![Rust](https://img.shields.io/badge/Rust-2024_edition-orange)](https://www.rust-lang.org/)
[![MCP](https://img.shields.io/badge/MCP-2025--11--25-blue)](https://modelcontextprotocol.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

ChatDB is a **synthetic reinforcement learning environment** where an external LLM agent attempts to prove mathematical theorems verified by the [Lean 4](https://lean-lang.org/) kernel. It exposes a [Model Context Protocol (MCP)](https://modelcontextprotocol.io/) server so that any MCP-compatible host — Claude Desktop, Cline, Roo Code, a custom Python script, or a distributed training loop — can drive proof search episodes without ChatDB ever containing a single line of inference code.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     External Agent Host                         │
│  (Claude Desktop, Cline, Python RL loop, human, ...)            │
│                                                                 │
│  Chooses model · formats prompt · calls LLM · parses response   │
└────────────────────────┬────────────────────────────────────────┘
                         │  MCP (stdio, JSON-RPC 2.0)
                         │  Protocol version 2025-11-25
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│                     chatdb-mcp (MCP Server)                     │
│                                                                 │
│  54 tools · typed schemas · JSON Schema 2020-12                 │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│                     chatdb-core (Engine)                         │
│                                                                 │
│  Episode lifecycle · obligation scheduler · crash recovery       │
│  Atomic step (CAS) · hash-chained trajectories · replay         │
│  Budget leases · reward calculation · dataset export             │
└────────────────────────┬────────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Lean 4 Kernel (Verifier)                    │
│                                                                 │
│  Sandboxed per-attempt · deterministic · timeout-guarded        │
│  Kernel pass / fail is ground truth                             │
└─────────────────────────────────────────────────────────────────┘
```

**Key invariant:** ChatDB contains **no provider SDKs, no API keys, no model routing, no inference calls, no streaming logic, and no provider retry code.** The external host owns all of that. ChatDB is the environment; the host is the policy.

As of v0.3.x, ChatDB verifies more than single theorem bodies — see
[`Solve` vs. `SubmitModule`](#solve-vs-submitmodule) below and
[`docs/submit_module.md`](docs/submit_module.md) for the small local Lean
development this environment now supports (helper defs/theorems, mutual
recursion, staged all-or-nothing verification). For what this represents in
terms of overall system capability and what's still ahead, see
[`docs/roadmap.md`](docs/roadmap.md).

## MCP Tools

**Call `readme_first` before creating any episode.** It's the dedicated
first-contact tool (issue #35): the required proof-search loop, the trust
boundary (tracked MCP actions and Lean verdicts are evidence — your own
reasoning is not), when to use `Solve` vs `SubmitModule`, why a proof check
outside `episode_step` doesn't count as a valid attempt, and the cost/
benchmark-mode boundary. Any agent host — Claude Code, Codex, Kilo Code,
Antigravity, or a custom script — should call this first.

| Tool | Description |
|---|---|
| `readme_first` | Call this first. The proof-search protocol: the loop, trust boundary, Solve/SubmitModule guidance, untracked-attempt warning, cost and benchmark-mode boundary |
| `environment_describe` | Protocol version, capabilities, tool schemas, Lean gateway readiness |
| `problem_create` | Register a new problem version (source text + root formal statement). `fidelity_status` starts `unreviewed` |
| `problem_submit_fidelity_review` | Record an evidence-backed determination that a problem's formal statement represents its source text. The ONLY path to `fidelity_status='verified'` — required for `outcome='certified'` |
| `problem_list` | List known problem versions (includes the hashes a reviewer must submit back unchanged) |
| `episode_create` | Start an episode from a problem version with `fidelity_status` `verified` or `attested` |
| `episode_reset` | Nondestructive reset — creates a new episode with `parent_episode_id` |
| `episode_observe` | Get the current observation and pending action request |
| `attempt_claim` | Claim a pending action request to obtain the `action_attempt_id` + `claim_token` required by `episode_step` |
| `episode_step` | Submit a typed action (`Solve` / `SubmitModule` / `Decompose` / `GiveUp`) with CAS revision check |
| `episode_status` | Episode state, revision, budget, step count, outcome |
| `episode_close` | Gracefully terminate an active episode |
| `model_call_reserve` | Reserve a budget lease before calling an external model |
| `model_call_settle` | Settle or void a lease (provider failure, cancellation) |
| `trajectory_export` | Paginated export of hash-chained trajectory events |
| `episode_replay` | Re-execute typed actions (`Solve` or `SubmitModule`) through Lean and verify trajectory integrity |
| `proof_export` | Proof dossier in one of 7 modes: `markdown` (default), `lean`, `public_summary` (redacted, never includes the proof body), `audit_archive`, `training_export` (structured JSON for SFT/RL/DPO), `paper_dossier` (adds a written narrative), `maintainer_submission`. Modes exposing the proof body require `allow_putnambench_proof_export=true` when the episode is linked to a tracked benchmark suite — see [docs/benchmarks/putnambench.md](docs/benchmarks/putnambench.md) |
| `lean_declaration_lookup` | Checks whether names resolve under a problem's import manifest (fast, default). Pass `deep_check=true` to also check under the full Mathlib umbrella and distinguish "not imported here" from "genuinely absent" (slow — loads all of Mathlib). Call this before concluding an API is unavailable |
| `proof_pattern_create` | Register a reusable proof-pattern lesson (failure signature + recommended repair). Advisory only — never marks anything proved |
| `proof_pattern_search` | Free-text search over the proof-pattern library, or list it whole. Call before repeating a failure another attempt already diagnosed |
| `proof_pattern_record_application` | Record that a pattern was relevant to a real episode/attempt (failed example, repair example, or suggested hint). Insert-only metadata — never touches proof/fidelity/certification status |
| `draft_create` | Register an informal Draft artifact — untrusted planning/reasoning content. A draft can never mark anything proved |
| `draft_observe` | Read back a draft's content and any moves recorded against it |
| `draft_extract_moves` | Record structured moves (construction, auxiliary_lemma, case_split, ...) the external agent identified in a draft. Metadata only |
| `formalization_plan_create` | Create a formalization plan for a problem, optionally seeded from selected moves of an existing draft |
| `formalization_plan_observe` | Read back a formalization plan and all its items |
| `formalization_plan_update` | Update a plan's title, status, or risk flags |
| `formalization_plan_add_item` | Add a planning item (concept, missing_definition, missing_lemma, planned_module, or external_citation) to a plan |
| `formalization_plan_attach_lookup` | Attach a `lean_declaration_lookup` result to a plan item, updating its Mathlib coverage status |
| `formalization_plan_promote_item_to_obligation` | Link a plan item to an episode_obligation that already exists (created via a normal `Decompose` action). Never creates the obligation itself |
| `research_dossier_create` | Create a Level 4 research dossier, optionally linked to a problem version, an episode, or neither. Metadata only |
| `research_dossier_observe` | Read a dossier with sections, nodes, citations, assumptions, verification layers, and explicit trust-boundary buckets |
| `research_node_add` | Add a typed research node (`definition`, `proposition`, `lemma`, `theorem`, `remark`, `reference`, `open_gap`) with explicit trust status |
| `external_reference_add` | Add an external reference and optionally one theorem claim. Citations are never kernel verification |
| `assumption_boundary_add` | Add an unformalized or rejected unsafe assumption boundary |
| `citation_review_add` | Record human review of an external theorem claim. Human review remains distinct from Lean verification |
| `verification_layer_set` | Set an independent verification layer (`blocked`, `failed`, `cited`, `human_reviewed`, etc.) for a dossier target |
| `candidate_construction_add` | Propose a candidate mathematical construction (`graph_family`, `counterexample`, `coloring`, etc.). Can exist before a dossier, node, Lean theorem, or episode. A research artifact, not a proof certificate |
| `candidate_construction_observe` | Record one empirical check (`supports`/`refutes`/`inconclusive`) against a candidate construction. Never changes proof status |
| `candidate_construction_update_status` | Update a candidate construction's status/trust_status/claimed_properties/known_failures. `kernel_verified_claim_linked` is rejected unless a real kernel-verified layer is already linked |
| `candidate_construction_link_node` | Attach a candidate construction to a research node, adopting the node's dossier if the construction has none yet |
| `candidate_construction_link_verification_layer` | Attach a candidate construction to an existing verification layer, adopting the layer's dossier if the construction has none yet |
| `mathlib_search_declarations` | Search the real pinned Mathlib source tree for declaration names containing a substring (beyond exact-name lookup). Advisory only |
| `mathlib_search_local_artifacts` | Search this instance's own previously-verified theorem/def names for a substring match |
| `formalization_plan_attach_librarian_result` | Attach a Mathlib librarian result to a formalization plan item, updating its coverage status |
| `run_envelope_create` | Create a run envelope: host/model/mode (development/evaluation/benchmark/private_audit/public_report) and host-side cost accounting ChatDB cannot itself observe |
| `run_envelope_update` | Update a run envelope's host-side cost fields or notes after the fact |
| `run_envelope_attach_episode` | Tag an episode with a run envelope. Metadata only — never changes the episode's outcome/state |
| `run_envelope_observe` | Read back a run envelope and every episode tagged with it |
| `benchmark_suite_create` | Register a benchmark suite (e.g. PutnamBench) — name, upstream URL/commit, language |
| `benchmark_problem_register` | Register one problem from a suite. `root_statement_hash` is server-computed, never client-supplied |
| `benchmark_run_create` | Create a run against a suite. `lean_version`/`mathlib_commit` are read from the server's OWN detected Lean environment, never accepted from the client |
| `benchmark_result_record` | Record (or upsert, for pass@k) one problem's result within a run. If `episode_id` is given, cross-checked against that episode's ACTUAL recorded outcome AND that it proved the SAME statement as the benchmark problem (issue #36) |
| `benchmark_run_observe` | Read back a run, its results, and aggregate metrics — `solved_rate` (solved at all) vs `pass_at_1_rate` (genuine first-attempt success) are reported separately |

## Budget Accounting

Episode budgets are enforcement/accounting controls, not proof-soundness
claims. A `NULL` `episodes.cost_budget_micros` is unbounded; bounded budgets
are debited only by conditional reservations that must fit the current
remaining budget.

- `episode_step.cost_micros` is the environment step charge. It must be
  non-negative and is reserved before the step executes; over-budget steps are
  denied before any Lean gateway call.
- `model_call_reserve.reserved_cost_micros` is a host/model-call budget lease.
  It must be non-negative and immediately reserves bounded episode budget. The
  lease row is inserted only if that budget reservation succeeds.
- `model_call_settle(actual_cost_micros, status="settled")` records the
  caller-reported actual model-call cost. Settlement adjusts only the delta
  from the reservation: lower actual cost refunds the difference, higher actual
  cost conditionally debits only the extra amount.
- `model_call_settle(status="voided")` cancels a lease and refunds the full
  reserved amount; no actual model-call cost is reported for a voided lease.
- Reserved-but-unsettled costs remain reservations. Benchmark cost summaries
  continue to include only settled `actual_cost_micros` as attested
  `model_call_reported_cost_micros`, never as exact cost.

## Level 4 Research Substrate

Research dossiers are paper-scale working records for definitions, lemmas,
theorems, remarks, references, and open gaps. A dossier can be linked to a
`problem_version`, linked to an `episode`, linked to both, or created before
either exists.

The Level 4 substrate is explicit about trust boundaries:

- `proved_in_episode` means there is a linked Lean-verified episode lemma.
- `imported_from_mathlib` means the claim is attributed to Mathlib, not locally
  proved by this episode.
- `external_citation_unreviewed` and `external_citation_human_reviewed` are
  citation states, not proof states.
- `unformalized_assumption` and `rejected_unsafe_assumption` remain visible as
  assumptions or rejected assumptions.
- `verification_layers` track independent review/construction/formalization
  layers and can be `blocked` or `failed` without failing the whole dossier.

No cited, reviewed, empirical, or assumed artifact is represented as kernel
verified unless it is linked to an actual Lean-verified artifact. These tables
are research bookkeeping and do not mutate episode outcome, obligation status,
budget state, fidelity status, or benchmark results.

### Candidate construction artifacts

Candidate constructions are proposed mathematical objects — graph families,
point configurations, colorings, field towers, lattices, counterexamples,
asymptotic families, algebraic objects, combinatorial designs, and so on. They
are the first durable object layer for **motivated discovery**: beyond *what*
object is proposed, each records *why* it was proposed and what to do with it,
encoding the loop

```text
observation → motivated move → proposed object → intended role → next check
```

via the fields `motivating_move` (`generalize`, `specialize`, `decompose`,
`search_extremal_example`, `search_counterexample`, `introduce_invariant`,
`reduce_to_known_theorem`, …), `source_observation`, `intended_role`
(`witness`, `counterexample`, `extremal_example`, `lower_bound_construction`,
`formalization_target`, `bridge_to_existing_theorem`, …), `strategy_context`,
`why_this_might_work`, `why_this_might_fail`, `next_check`, and
`future_challenge_relevance`. The object itself lives in `informal_description`,
`parameters_json`, and `construction_json`; `verification_targets_json` records
what a later system should check.

A candidate construction can exist before there is a research dossier written
up, before there is a Lean theorem, before there is an episode, and before
there is empirical search machinery to generate one automatically (that
machinery is issue #26's empirical math lab; this substrate only holds the
objects it will produce and judge). Every link — `dossier_id`,
`related_node_id`, `verification_layer_id`, `problem_version_id`,
`episode_id` — is optional.

Candidate constructions are **not proof certificates**. Their `trust_status`
makes that explicit:

- `informal`, `empirical_evidence`, `cited`, `human_reviewed`, and
  `formalized_statement_exists` are all states short of kernel verification —
  empirical support, human review, a citation, or even an existing formal
  statement are each distinct from, and never imply, being proved.
- `kernel_verified_claim_linked` is the only state that claims kernel
  evidence, and it is rejected unless the construction's
  `verification_layer_id` names a `verification_layers` row whose own status
  is already `kernel_verified` (itself only reachable through real
  Lean-backed evidence — see above). A candidate construction can link to
  real evidence; it can never manufacture it.

A candidate construction can attach to a dossier, a research node, and/or a
verification layer, or exist attached to none of them. `falsified` and
`rejected` constructions stay visible in `research_dossier_observe` rather
than being deleted, since a documented dead end is itself research output.

**Benchmark contamination policy:** upstream benchmarks like PutnamBench ask
that completed formal proofs not be published without first coordinating with
their maintainers. See [docs/benchmarks/putnambench.md](docs/benchmarks/putnambench.md)
for how `proof_export`'s modes and `allow_putnambench_proof_export` flag
enforce this.

## `Solve` vs. `SubmitModule`

As of v0.3.x, `episode_step` accepts more than a single theorem body:

- **`Solve { proof_term }`** — one theorem: `theorem O_<id> : <statement> := by <proof_term>`. Good for a self-contained tactic proof.
- **`SubmitModule { module_items, root_theorem }`** — a small local Lean *development*: helper `def`s, helper `theorem`s, and a root theorem, assembled by the server into one namespaced module and verified as a unit. `module_items` is a list of:
  - `LeanModuleItem::Def { name, type_signature, body }` — `def <name> : <type_signature> := <body>`
  - `LeanModuleItem::Theorem { name, statement, proof_term }` — `theorem <name> : <statement> := by <proof_term>`
  - `LeanModuleItem::MutualGroup { members }` — 2+ `Def`/`Theorem` members that must forward-reference each other (e.g. mutually recursive functions), rendered together inside one server-owned `mutual ... end` block.

The trust boundary is the same one the single-theorem path already has, one
level up: **the model proposes, the server assembles, Lean verifies, the
ledger records.** A client never writes raw Lean — no `import`/`namespace`/
`end`/`set_option` lines, no `axiom`/`opaque`/`unsafe`/`instance`
declarations, never `mutual`/`end` directly (the server owns those tokens
even for a `MutualGroup`). Every name is sanitized to a single namespace-local
identifier, and `root_theorem.statement` must canonical-hash to the problem's
registered root formal statement — a module can never silently prove a
different goal. Verification is **staged and all-or-nothing**: either the
whole module passes the kernel and is recorded, or nothing enters the trusted
namespace.

```jsonc
{
  "type": "submit_module",
  "module_items": [
    { "item_kind": "def", "name": "double", "type_signature": "Nat → Nat", "body": "fun n => n + n" }
  ],
  "root_theorem": { "name": "root", "statement": "double 2 = 4", "proof_term": "rfl" }
}
```

Proof soundness vs. statement fidelity (below) is unchanged for module
proofs — a `SubmitModule` root proof reaches the same `kernel_verified`/
`certified` outcomes a `Solve` proof does. A verified module is also a
first-class replayable artifact: `proof_export(format="lean")` can emit the
exact verified module source, and `episode_replay` re-assembles it from the
recorded structured items and re-verifies against the kernel. Full detail,
including the mutual-recursion trust boundary and injection hardening: see
[`docs/submit_module.md`](docs/submit_module.md). For what level of capability
this represents and what's still missing, see [`docs/roadmap.md`](docs/roadmap.md).

## Drafts and formalization planning (Level 3)

Before a `Solve`/`SubmitModule` attempt, a client can preserve informal
reasoning as a **Draft** (`draft_create`) and record the moves it identifies
within it (`draft_extract_moves` — construction, auxiliary_lemma, case_split,
induction, reduction, bijection, counterexample_search, asymptotic_step,
external_citation, unknown). Selected moves can seed a **formalization
plan** (`formalization_plan_create`), which tracks planned concepts,
definitions, lemmas, and modules together with their Mathlib coverage status
(`formalization_plan_attach_lookup`, using `lean_declaration_lookup`
results).

Both are strictly advisory, mirroring the trust boundary everywhere else in
this environment: a Draft or a plan item can never mark anything proved.
Real obligations are still created only through `Decompose`, via the normal
budget-accounted `episode_step` flow —
`formalization_plan_promote_item_to_obligation` only records a metadata
*link* to an obligation that already exists that way; it never creates one
itself. See `docs/roadmap.md`'s Level 3 section for the full design.

## Proof soundness vs. statement fidelity

These are independent claims, and the environment never conflates them:

- **Proof soundness** — the Lean kernel verified this exact formal statement. Reaching this alone yields `outcome: "kernel_verified"`.
- **Statement fidelity** — that formal statement actually represents the source problem. Only `problem_submit_fidelity_review(decision="verified")` can establish this, based on evidence the server independently hash-checks against the problem's *current* source/statement/rendering (a stale or mismatched submission is rejected, not silently accepted).

`outcome: "certified"` requires **both** — a kernel-verified root can never present as certifying the source claim on proof soundness alone. This closes a real exploit: a trivially-true weakening of a source problem (e.g. proving `∀ n, Even n → True` for the claim "every even natural is divisible by two") kernel-verifies but must never be reported, rewarded, or exported as if it certified the source claim. See `docs/fix_plan_playtest_02.md`.

Two ways to unlock proving:
- **Real review**: `problem_submit_fidelity_review(decision="verified", ...)` → `fidelity_status="verified"` → root proof reaches `certified` directly (or promotes retroactively if the root was already `kernel_verified`).
- **Dev bypass**: `problem_create(unsafe_dev_attestation=true)` → `fidelity_status="attested"` → proving is allowed, but the episode can only ever reach `kernel_verified`, never `certified` — and problems/episodes under `attested` are excluded from default dataset exports (`training_eligible=false`).

A minimal prover loop is: `problem_create` → `problem_submit_fidelity_review` (or `unsafe_dev_attestation=true` for dev use) → `episode_create` → `episode_observe` → `attempt_claim` → `episode_step` → repeat `episode_observe`/`attempt_claim`/`episode_step` until `outcome` is set.

## Import manifests and "environmental scope collapse"

Every problem version has an immutable import manifest — the exact set of Mathlib modules its proofs are checked against (base: `Mathlib.Tactic.Ring` + `Mathlib.Tactic.NormNum`; extend it via `problem_create(problem_imports=[...])`, each validated with a real compile check before acceptance). Import strings and `lean_declaration_lookup` names are written verbatim into Lean source, so both are restricted to plain identifier syntax (dot-separated `[A-Za-z_][A-Za-z0-9_]*` segments for imports; no whitespace/comment/command syntax for declaration names) and capped at 50 entries per call — anything else is rejected before it ever reaches Lean, never silently compiled. See `docs/fix_plan_playtest_04.md`.

**An `unknown_declaration` diagnostic only ever proves a name didn't resolve under that exact manifest — it never proves the name is absent from the pinned Mathlib.** Before either changing proof strategy or declaring an API unavailable, call `lean_declaration_lookup`.

By default the lookup only checks the problem's own manifest — a few seconds, since it doesn't load all of Mathlib:

- **`available`** — resolves under the current manifest.
- **`not_available_under_current_manifest`** — doesn't resolve under the current manifest. **This alone does not prove absence from the library** — call again with `deep_check=true` to get a conclusive verdict.
- **`environment_error`** — the lookup itself failed; not evidence either way.

Pass `deep_check=true` to additionally check under the full Mathlib umbrella (slow — reliably 15-40+ seconds, since it loads all of Mathlib) and get a conclusive verdict:

- **`not_in_current_import_scope`** — resolves under the full umbrella but not the current manifest → add the module via a new `problem_create(problem_imports=[...])`.
- **`unknown_declaration`** — doesn't resolve even with everything imported → genuinely try a different name.

Conflating "not available under the current manifest" with "the library doesn't have this" — is a real failure mode we call **environmental scope collapse**: a local fact about one import closure gets inflated into a global claim about library capability, which can cascade into a model abandoning a provable branch. `environment_describe` carries this as an explicit epistemic rule for any agent driving the loop. Diagnostics also distinguish `unknown_declaration` (name resolution) from `parse_error` (syntax) and other categories — see `docs/fix_plan_playtest_03.md`. The fast-default/opt-in-deep split exists because the unconditional umbrella check was slow enough to blow past MCP client tool-call timeouts — see `docs/fix_plan_playtest_04.md`.

Import manifests are immutable per problem_version and included in every observation/trajectory event as `import_manifest_hash`, so replay always re-verifies against the exact closure the original attempt used.

## Prerequisites

- **Rust** (2024 edition) — install via [rustup](https://rustup.rs/)
- **Lean 4 toolchain manager (elan)** — install via [elan](https://github.com/leanprover/elan):
  ```powershell
  # On Windows, you can use the included bootstrap script:
  .\elan-init.ps1
  ```
- **The `lean-checker` Lake project** — see [Lean Checker Setup](#lean-checker-setup) below. Without it, `solve` actions fail with an infrastructure error; every other tool (episode lifecycle, decompose, trajectories, dataset export) works without it.

## Lean Checker Setup

`CHATDB_LEAN_PROJECT_PATH` (default `./lean-checker`) must point at a [Lake](https://github.com/leanprover/lake) project that depends on [Mathlib](https://github.com/leanprover-community/mathlib4). Every problem version has its own immutable **import manifest** — the exact Mathlib modules its proofs (and its `SubmitModule` developments) are checked against, starting from a base of `Mathlib.Tactic.Ring` + `Mathlib.Tactic.NormNum` (`omega` comes with core Lean once any Mathlib module is imported) and extendable per-problem via `problem_create(problem_imports=[...])` — each additional module is validated with a real compile check before the problem is accepted, not merely a name-shape check (`crates/chatdb-core/src/lean/mod.rs`). This is not a single hardcoded import list baked into the gateway; see [Import manifests and "environmental scope collapse"](#import-manifests-and-environmental-scope-collapse) above. Setting up the Lake project itself is a one-time, multi-gigabyte task — do it once per machine, not per session:

```powershell
# 0. (Optional but recommended on machines with a small C: drive) Keep the multi-GB
#    toolchain store off the system drive. Match this with CHATDB_ELAN_HOME in the
#    MCP server env so the server's Lean subprocesses resolve the same store.
$env:ELAN_HOME = "F:\lean\elan"

# 1. Scaffold a Lake project pinned to Mathlib's toolchain (skip if lean-checker/ exists).
#    The math template runs `lake update` itself, cloning mathlib + deps.
lake +leanprover-community/mathlib4:lean-toolchain new lean-checker math
cd lean-checker

# 2. Download Mathlib's prebuilt .olean cache (do NOT build from source —
#    that takes hours; the cache download takes minutes)
lake exe cache get

# 3. Verify the toolchain resolves and a trivial proof compiles
@'
import Mathlib.Tactic.NormNum
theorem t : (1:Nat) + 1 = 2 := by norm_num
'@ | Out-File -Encoding utf8 smoke.lean
lake env lean --json smoke.lean
```

If step 3 prints no `"severity":"error"` JSON lines, the gateway is ready. Point `CHATDB_ELAN_BIN_PATH` at the `.elan/bin` directory containing `lake.exe`/`lean.exe` (default `~/.elan/bin`), and `CHATDB_LEAN_PROJECT_PATH` at the `lean-checker/` directory itself (the one containing `lakefile.toml`). The server checks both paths at startup and reports readiness via `environment_describe`'s `lean_gateway` field (`"ready"` or `"unavailable"`) — an `"unavailable"` warning is also printed to stderr on stdio startup.

The gateway copies every kernel-passing proof into `lean-checker/LeanChecker/Verified/O_<id>.lean` and `lake build`s it so later obligations can `import` it as an approved dependency — keep that directory out of `.gitignore` exclusions if you want to inspect proved lemmas after a run.

## Build

```bash
# Debug build (fast compile, slower runtime)
cargo build

# Release build (optimized binary)
cargo build --release
```

The MCP server binary will be at:
- Debug: `target/debug/chatdb-mcp.exe`
- Release: `target/release/chatdb-mcp.exe`

## Run Tests

```bash
cargo test
```

This runs the full test suite across both crates:

| Test Suite | What It Verifies |
|---|---|
| `p0_migration_baseline` | Schema v0 → v1 migration safety |
| `architecture_test` | No provider SDKs in `chatdb-core` |
| `phase5_lifecycle_tests` | Episode create / reset / advance lifecycle |
| `phase6_attempts_tests` | Crash-recovery attempt state machine |
| `phase8_step_tests` | Atomic CAS step with budget deduction |
| `phase9_trajectories_tests` | Hash-chained recording and tamper detection |
| `phase11_dataset_tests` | SFT/RL/DPO export and sanitization |
| `phase12_conformance_tests` | Production path matches replay path |
| `chatdb-mcp` lib tests | Full MCP client↔server play-throughs over duplex transport: tool listing, decompose→give_up, solve→certified (mock Lean gateway), solve→kernel_fail (non-terminal), fabricated-claim/stale-revision rejection, idempotent claim retry |

## Register as MCP Server

### Claude Desktop

Add to `%APPDATA%\Claude\claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "chatdb": {
      "command": "F:\\Github\\mnehmos.llm-driven-proof-search.environment\\target\\release\\chatdb-mcp.exe",
      "args": ["chatdb.db"],
      "env": {
        "CHATDB_LEAN_PROJECT_PATH": "F:\\Github\\mnehmos.llm-driven-proof-search.environment\\lean-checker",
        "CHATDB_ELAN_BIN_PATH": "C:\\Users\\mnehm\\.elan\\bin"
      }
    }
  }
}
```

### Cline / Roo Code

Add to your `mcp_settings.json`:

```json
{
  "mcpServers": {
    "chatdb": {
      "command": "F:\\path\\to\\target\\release\\chatdb-mcp.exe",
      "args": ["chatdb.db"],
      "env": {
        "CHATDB_LEAN_PROJECT_PATH": "F:\\path\\to\\lean-checker",
        "CHATDB_ELAN_BIN_PATH": "C:\\Users\\you\\.elan\\bin"
      },
      "disabled": false
    }
  }
}
```

### ChatGPT (via OpenAI Tunnel or Direct HTTP)

ChatGPT requires an HTTP endpoint speaking the MCP SSE transport. Start the server in `http` mode:

```bash
chatdb-mcp.exe --transport http --port 8080 chatdb.db
```

Then, use a tunneling solution like the [OpenAI Secure MCP Tunnel](https://github.com/openai/tunnel-client) or `ngrok` to expose it, and register the resulting HTTPS URL in your OpenAI platform settings as a Server URL.

```bash
# Example using OpenAI tunnel-client
tunnel-client run --tunnel-id <YOUR_TUNNEL_ID> --mcp-command "chatdb-mcp.exe --transport http --port 8080 chatdb.db"
```

> **Known transport property:** some web/hosted MCP surfaces (observed with claude.ai web connectors)
> strip MCP error *bodies* down to a bare failure — the server's diagnostic messages
> (claim expiry timestamps, action-shape hints, etc.) are only visible on transports that
> relay them, such as Claude Desktop stdio or a raw JSON-RPC client. On stripped surfaces,
> diagnose via state probes instead: `episode_status`, `episode_observe`, `problem_list`.

### Programmatic (Python / Any stdio MCP client)

```python
import subprocess, json

proc = subprocess.Popen(
    ["target/release/chatdb-mcp.exe", "chatdb.db"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    env={
        "CHATDB_LEAN_PROJECT_PATH": "./lean-checker",
        "CHATDB_ELAN_BIN_PATH": "~/.elan/bin",
    }
)
# Send JSON-RPC 2.0 messages over stdin/stdout
```

## Environment Variables

| Variable | Default | Description |
|---|---|---|
| `CHATDB_DB_PATH` | `chatdb.db` | SQLite database path (also settable as first CLI arg) |
| `CHATDB_LEAN_PROJECT_PATH` | `./lean-checker` | Path to the Lean 4 project used for verification |
| `CHATDB_ELAN_BIN_PATH` | `~/.elan/bin` | Path to the directory containing the `lake`/`lean` elan proxy binaries |
| `CHATDB_ELAN_HOME` | *(unset)* | If set, exported as `ELAN_HOME` to Lean subprocesses — the elan **root** where `toolchains/` lives. Use this to keep multi-GB toolchains off the system drive (e.g. `F:\lean\elan`). When unset, elan uses the process env / `~/.elan` |

## Episode Lifecycle

```
episode_create(problem_version_id)
    │
    ▼
┌──────────────────────┐
│ awaiting_external_    │◀──────────────────────────────┐
│ action                │                               │
└──────────┬───────────┘                               │
           │  episode_observe()                         │
           │  → observation + action_request            │
           ▼                                            │
    attempt_claim(action_request_id, idempotency_key)    │
           │  → action_attempt_id + claim_token          │
           ▼                                            │
    ┌──────────────┐                                    │
    │ Host calls   │                                    │
    │ external LLM │  (outside ChatDB)                  │
    └──────┬───────┘                                    │
           │                                            │
           ▼                                            │
    episode_step(action_attempt_id, claim_token, revision, action)
           │                                            │
           ├── Solve → Lean verifies ──┐                │
           │                           ▼                │
           │                    ┌─────────────┐         │
           │                    │ KernelPass  │──▶ root proved ──▶ terminated(certified)
           │                    └─────────────┘         │
           │                                            │
           │                    ┌─────────────┐         │
           │                    │ KernelFail  │──▶ next obligation
           │                    └─────────────┘─────────┘
           │
           ├── SubmitModule → staged, all-or-nothing Lean module verification ──┐
           │        (defs + helper theorems + root theorem, one namespace)      │
           │                                            ▼                      │
           │                    ┌─────────────┐  whole module passes           │
           │                    │ KernelPass  │──▶ root proved ──▶ terminated(certified)
           │                    └─────────────┘                                │
           │                    ┌─────────────┐  policy rejection OR           │
           │                    │ KernelFail  │  any declaration fails ──▶ next obligation
           │                    └─────────────┘  (nothing enters the trusted namespace)
           │
           ├── Decompose → child obligations ──▶ next (child) obligation
           ├── GiveUp ──▶ terminated(gave_up)
           ├── budget_exhausted / max_steps_reached ──▶ truncated(budget_exhausted)
           └── stale revision / invalid claim ──▶ rejected, retry (episode unchanged)
```

## Dataset Export

ChatDB produces training-grade synthetic data:

- **SFT records** — (prompt, completion) pairs from committed steps
- **RL tuples** — (s, a, r, s', terminated, truncated, info) from trajectory events
- **DPO pairs** — (prompt, chosen, rejected) from accepted vs. rejected attempts
- **Contamination-safe splits** — deterministic train/validation/test by theorem lineage hash
- **Sanitized trajectories** — API keys, credentials, and private endpoints automatically scrubbed
- **Dataset manifests** — checksums, lineage hashes, and sanitization policy metadata

## Project Structure

```
├── Cargo.toml                    # Workspace root
├── crates/
│   ├── chatdb-core/              # Engine library (zero network dependencies)
│   │   ├── src/
│   │   │   ├── db/               # Schema, migrations, queries
│   │   │   ├── lean/             # Sandboxed Lean 4 gateway
│   │   │   ├── models/           # Typed data contracts
│   │   │   ├── orchestrator/     # Lifecycle, step, trajectories, dataset
│   │   │   ├── hashing.rs        # RFC 8785 JCS canonical hashing
│   │   │   └── schema_export.rs  # JSON Schema 2020-12 generation
│   │   └── tests/                # Integration test suites
│   └── chatdb-mcp/               # MCP server (thin shell over core)
│       ├── src/lib.rs            # 54 tools, rmcp 1.8.0, 2025-11-25 — ServerHandler + tests
│       └── src/main.rs           # CLI: stdio/http transport wiring only
├── docs/
│   ├── adr/                      # Architecture Decision Records
│   ├── playtests/                # Dated playtest reports (real-toolchain sprints, lessons learned)
│   ├── roadmap.md                # Capability levels (0-6) and what each requires
│   └── submit_module.md          # SubmitModule / mutual recursion trust boundary and mechanics
├── fixtures/                     # Test fixtures
└── CHATDB_SPEC.md                # Full specification document
```

## Design Decisions

Architectural decisions are recorded in [`docs/adr/`](docs/adr/):

- **ADR-0001** — Lean sandbox platform isolation strategy
- **ADR-0002** — Canonical vs. episode-local storage separation
- **ADR-0003** — Hash-chained trajectory design

## Playtests and roadmap

- [`docs/roadmap.md`](docs/roadmap.md) — capability levels (0 through 6), what
  v0.3.1 actually reaches (Level 2), and what each subsequent level requires.
- [`docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md`](docs/playtests/2026-07-04-v0.3.1-overnight-module-sprint.md) —
  a real-toolchain playtest sprint covering algebraic inequalities, induction,
  structural/well-founded/mutual recursion, and list predicates, with full
  proof exports and reusable proof-pattern lessons.
- [`docs/librarian.md`](docs/librarian.md) — the Mathlib librarian's
  architecture, trust boundary, confidence vocabulary, and deliberate MVP
  scope cuts (issue #25).

## License

MIT
