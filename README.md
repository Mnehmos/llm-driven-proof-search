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
│  11 tools · typed schemas · JSON Schema 2020-12                 │
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
| `environment_describe` | Protocol version, capabilities, tool schemas |
| `episode_create` | Start an episode from a problem version |
| `episode_reset` | Nondestructive reset — creates a new episode with `parent_episode_id` |
| `episode_observe` | Get the current observation and pending action request |
| `episode_step` | Submit a typed action (Solve / Skip / Decompose) with CAS revision check |
| `episode_status` | Episode state, revision, budget, step count, outcome |
| `episode_close` | Gracefully truncate an active episode |
| `model_call_reserve` | Reserve a budget lease before calling an external model |
| `model_call_settle` | Settle or void a lease (provider failure, cancellation) |
| `trajectory_export` | Paginated export of hash-chained trajectory events |
| `episode_replay` | Re-execute typed actions through Lean and verify trajectory integrity |

## Prerequisites

- **Rust** (2024 edition) — install via [rustup](https://rustup.rs/)
- **Lean 4** — install via [elan](https://github.com/leanprover/elan):
  ```powershell
  # On Windows, you can use the included bootstrap script:
  .\elan-init.ps1
  ```

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
| `test_mcp_list_tools_and_describe` | Full MCP client↔server integration over duplex transport |

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
| `CHATDB_ELAN_BIN_PATH` | `~/.elan/bin` | Path to elan-managed Lean toolchain binaries |

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
    ┌──────────────┐                                    │
    │ Host calls   │                                    │
    │ external LLM │  (outside ChatDB)                  │
    └──────┬───────┘                                    │
           │                                            │
           ▼                                            │
    episode_step(action, revision, idempotency_key)     │
           │                                            │
           ├── Lean verifies ──┐                        │
           │                   ▼                        │
           │            ┌─────────────┐                 │
           │            │ KernelPass  │──▶ Proved ──▶ terminated
           │            └─────────────┘                 │
           │                                            │
           │            ┌─────────────┐                 │
           │            │ KernelFail  │──▶ next obligation
           │            └─────────────┘─────────────────┘
           │
           ├── budget_exhausted ──▶ truncated
           └── max_steps_reached ──▶ truncated
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
│   └── chatdb-mcp/               # MCP stdio server (thin shell over core)
│       └── src/main.rs           # 11 tools, rmcp 1.8.0, 2025-11-25
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
