# ADR 0001: Lean Sandbox Platform Isolation

## Status
Accepted

## Context
The LLM-Driven Proof Search Environment orchestrator executes model-generated Lean 4 source files using the `lake env lean` command. Since this source code is produced by an untrusted external policy (LLM), it is arbitrary and potentially malicious. The orchestrator must execute this code in a secure sandbox to prevent it from escaping, consuming excessive resources, or tampering with the host environment. The primary development environment is Windows (e.g., using an `F:` drive), but the system may also run on Unix-like environments in production.

## Decision
We will implement platform-specific sandbox mechanisms with a "fail-closed" default: **if the configured sandbox cannot be established, the Lean attempt does not run.**

### 1. Platform Isolation Mechanisms
*   **Windows:** We will use **Windows Job Objects** to sandbox the Lean process. Job objects allow us to enforce CPU limits, memory limits, and process-tree termination (when the parent or job dies, all child processes spawned by `lake`/`lean` are automatically killed).
*   **Unix (Linux):** We will use `cgroups` (for resource limits like memory and CPU) and namespaces (for mount, PID, and network isolation, e.g., via `bwrap` or `systemd-run`).

### 2. Network Denial
*   Network access must be disabled during verification.
*   *Testing Methodology:* We will include a test that generates a Lean file attempting to open a TCP connection or make an HTTP request (via FFI or Lean sockets if available). The test must assert that the network request fails due to isolation, not due to parsing errors.

### 3. Resource Limits & Enforcement
*   **CPU / Memory:** Enforced via Job Objects (Windows) and `cgroups` (Unix).
*   **Wall-clock Timeout:** The Rust parent process will spawn the Lean child process and `await` it with a `tokio::time::timeout`. If the timeout expires, the entire process group (Windows Job Object or Unix PID namespace) will be forcefully terminated.
*   **Stdout/Stderr Limits:** The Rust parent will read stdout/stderr streams incrementally, capping the buffer at a fixed threshold (e.g., 1MB). Once the limit is reached, further output is discarded to prevent OOM DOS attacks.

### 4. File System Isolation & Temporary Workspaces
*   Each attempt receives a unique temporary directory (e.g., `tmp/lean_attempt_<uuid>`).
*   **Path Traversal:** All paths will be strictly validated. The generated source file must only be written into the temporary directory.
*   **Arbitrary File Access:** Lean will be configured with a restricted environment. On Unix, `bwrap` will mount only the necessary Lean toolchain paths as read-only and the temporary workspace as read-write. On Windows, we will run the process with a restricted token (if possible) and rely on the temporary directory separation.
*   **Cleanup:** The temporary directory lifecycle is managed by a Rust `Drop` guard. Regardless of whether the verification succeeds, fails, or panics, the directory will be deleted when the attempt concludes.

## Consequences
*   **Positive:** The system is protected against malicious model outputs. Crash-safe cleanup ensures no disk exhaustion from leaked temporary workspaces.
*   **Negative:** Implementing Windows Job Objects requires platform-specific `unsafe` Win32 API calls or relying on a crate like `winapi`/`windows-sys`. Unix isolation requires external dependencies like `bwrap`.
*   **Complexity:** We must abstract the sandbox execution behind a `SandboxRunner` trait to handle the platform differences transparently.
