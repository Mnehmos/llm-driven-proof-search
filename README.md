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
│  17 tools · typed schemas · JSON Schema 2020-12                 │
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

## MCP Tools

| Tool | Description |
|---|---|
| `environment_describe` | Protocol version, capabilities, tool schemas, Lean gateway readiness |
| `problem_create` | Register a new problem version (source text + root formal statement). `fidelity_status` starts `unreviewed` |
| `problem_submit_fidelity_review` | Record an evidence-backed determination that a problem's formal statement represents its source text. The ONLY path to `fidelity_status='verified'` — required for `outcome='certified'` |
| `problem_list` | List known problem versions (includes the hashes a reviewer must submit back unchanged) |
| `episode_create` | Start an episode from a problem version with `fidelity_status` `verified` or `attested` |
| `episode_reset` | Nondestructive reset — creates a new episode with `parent_episode_id` |
| `episode_observe` | Get the current observation and pending action request |
| `attempt_claim` | Claim a pending action request to obtain the `action_attempt_id` + `claim_token` required by `episode_step` |
| `episode_step` | Submit a typed action (Solve / Decompose / GiveUp) with CAS revision check |
| `episode_status` | Episode state, revision, budget, step count, outcome |
| `episode_close` | Gracefully terminate an active episode |
| `model_call_reserve` | Reserve a budget lease before calling an external model |
| `model_call_settle` | Settle or void a lease (provider failure, cancellation) |
| `trajectory_export` | Paginated export of hash-chained trajectory events |
| `episode_replay` | Re-execute typed Solve actions through Lean and verify trajectory integrity |
| `proof_export` | Human-readable proof dossier: proof tree, assembled Lean source, full attempt history, proof/fidelity/promotion status, integrity line (`format: "markdown"` or `"lean"`) |
| `lean_declaration_lookup` | Checks whether names resolve under a problem's import manifest AND under the full Mathlib umbrella — distinguishes "not imported here" from "genuinely absent." Call this before concluding an API is unavailable |

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

Every problem version has an immutable import manifest — the exact set of Mathlib modules its proofs are checked against (base: `Mathlib.Tactic.Ring` + `Mathlib.Tactic.NormNum`; extend it via `problem_create(problem_imports=[...])`, each validated with a real compile check before acceptance).

**An `unknown_declaration` diagnostic only ever proves a name didn't resolve under that exact manifest — it never proves the name is absent from the pinned Mathlib.** Before either changing proof strategy or declaring an API unavailable, call `lean_declaration_lookup`, which checks a name under both the problem's manifest and the full Mathlib umbrella:

- **`available`** — resolves under the current manifest.
- **`not_in_current_import_scope`** — resolves under the full umbrella but not the current manifest → add the module via a new `problem_create(problem_imports=[...])`.
- **`unknown_declaration`** — doesn't resolve even with everything imported → genuinely try a different name.
- **`environment_error`** — the lookup itself failed; not evidence either way.

Conflating the first case with the third — "unknown identifier" collapsing into "the library doesn't have this" — is a real failure mode we call **environmental scope collapse**: a local fact about one import closure gets inflated into a global claim about library capability, which can cascade into a model abandoning a provable branch. `environment_describe` carries this as an explicit epistemic rule for any agent driving the loop. Diagnostics also distinguish `unknown_declaration` (name resolution) from `parse_error` (syntax) and other categories — see `docs/fix_plan_playtest_03.md`.

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

`CHATDB_LEAN_PROJECT_PATH` (default `./lean-checker`) must point at a [Lake](https://github.com/leanprover/lake) project that depends on [Mathlib](https://github.com/leanprover-community/mathlib4), because `RealLeanGateway` hardcodes `import Mathlib.Tactic.{Ring,NormNum}` into every candidate proof it checks (`omega` comes with core Lean once any Mathlib module is imported) (`crates/chatdb-core/src/lean/mod.rs`). This is a one-time, multi-gigabyte setup — do it once per machine, not per session:

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
│       ├── src/lib.rs            # 17 tools, rmcp 1.8.0, 2025-11-25 — ServerHandler + tests
│       └── src/main.rs           # CLI: stdio/http transport wiring only
├── docs/
│   └── adr/                      # Architecture Decision Records
├── fixtures/                     # Test fixtures
└── CHATDB_SPEC.md                # Full specification document
```

## Design Decisions

Architectural decisions are recorded in [`docs/adr/`](docs/adr/):

- **ADR-0001** — Lean sandbox platform isolation strategy
- **ADR-0002** — Canonical vs. episode-local storage separation
- **ADR-0003** — Hash-chained trajectory design

## License

MIT
