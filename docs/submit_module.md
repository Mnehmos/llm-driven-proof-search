# SubmitModule — structured Lean module submissions

ChatDB started as a one-theorem prover: an episode's root obligation was proved
by a single `Solve { proof_term }` wrapped as `theorem O_… : <statement> := by
<proof>`. Serious math needs a small *local theory* first — helper definitions,
helper lemmas, then a root theorem that uses them. `SubmitModule` adds that,
without weakening the import / declaration-name injection hardening the
single-theorem path already has.

## The boundary: model proposes, server assembles, Lean verifies

The core principle is unchanged: **the model proposes, the server assembles,
Lean verifies, the ledger records. Nothing enters the trusted namespace until
the staged artifact passes policy and kernel verification.**

A client never sends raw Lean source. It sends structured *items* — mathematical
content only:

```jsonc
{
  "type": "submit_module",
  "module_items": [
    { "item_kind": "def",     "name": "comps",   "type_signature": "ℕ → ℕ",       "body": "fun n => …" },
    { "item_kind": "theorem", "name": "comps_pos","statement": "0 < comps n",      "proof_term": "…" }
  ],
  "root_theorem": {
    "name": "main",
    "statement": "<must canonical-hash to the problem's root_statement_hash>",
    "proof_term": "…"
  }
}
```

The **server** owns everything structural and renders the file itself
(`crate::lean::module::assemble_module`):

- the `import` lines — from the problem's immutable `import_manifest_json`, never
  a client string;
- the server-owned `set_option` linter lines;
- the `namespace ChatDB.P_<problem>` … `end` wrapper;
- the `def` / `theorem` keywords and the sanitized names.

Assembly order is: imports → server `set_option`s → open namespace → defs →
helper theorems → root theorem → close namespace.

## What is rejected (before Lean is ever run)

Policy checks are deterministic and run in `chatdb-core` before any compile:

- **Names** must be a single namespace-local identifier — ASCII letter/`_`
  start, then letters/digits/`_`/`'`. No dots (a dotted name could escape the
  generated namespace or shadow a real Mathlib declaration), no `_root_`, no
  duplicates (helpers and root share one namespace).
- **No client-written top-level commands.** A line inside any client string
  (type signature, body, statement, proof term) may not *begin* with `import`,
  `namespace`, `end`, `section`, `open`, `set_option`, `attribute`, `variable`,
  `universe`, `export`, a declaration keyword (`def`, `theorem`, `lemma`,
  `example`, `abbrev`, `instance`, `structure`, `inductive`, `class`, `axiom`,
  `opaque`, `unsafe`, `partial`, `noncomputable`), a declaration **modifier**
  (`private`, `protected`, `local`, `scoped`), an **attribute list** (`@[...]`,
  e.g. `@[simp] theorem cheat : False := ...`), or metaprogramming/eval commands
  (`macro`, `syntax`, `elab`, `notation`, `#eval`, `#check`, …). This is the
  injection boundary: a def body of `0\n\naxiom cheat : False` opens a new
  top-level command and is refused, not compiled — and so does
  `0\n\n@[simp] theorem cheat : False := ...` or `0\n\nprivate theorem cheat : False := ...`,
  since a modifier or attribute preceding a declaration keyword is just as much
  a fresh top-level command as the keyword itself (a scanner that only checks
  whether a line's first token *is* the declaration keyword is bypassed by
  prefixing one of these — a bare `@` for explicit-argument application, e.g.
  `@id Nat n`, is unaffected; only the literal `@[` attribute-list prefix is banned).
- **Never anywhere:** `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
  `native_decide` (whole-word). `sorry`/`admit` typecheck but prove nothing — the
  kernel only warns — so they are a hard rejection here *and* at the staged
  compile.
- **Root statement hash-match.** `canonical_hash(root_theorem.statement)` must
  equal the target obligation's `statement_hash` (for the root obligation, that
  is the problem's registered root formal statement). A module cannot silently
  prove a weakened or different goal.

## Staged, all-or-nothing verification

The assembled source is compiled in a **staged** location. The whole module
passes only if the process succeeds, no error diagnostics were emitted, and no
`sorry`/`admit` warning appears. On pass, the verified source is written to
`LeanChecker/Verified` and the root obligation is closed together with the
module's declarations — **no partial commit**. On failure, nothing is written,
the obligation stays open, and the structured diagnostic is preserved as a
failure lesson.

## The DB lock is never held during a Lean call

`episode_step` runs the Lean gateway call (`verify_exact` for `Solve`,
`verify_module` for `SubmitModule`) — up to 60-120 seconds against a real Lean
toolchain — WITHOUT holding the server's DB mutex, so no other concurrent tool
call on the session (`episode_observe`, `episode_status`, a different
episode's `episode_step`, ...) blocks on it.

This is a two-phase split in `chatdb-core::orchestrator::step`:

- `attempt_prepare` validates the attempt/claim/CAS, marks the attempt
  `executing`, and either fully resolves a non-Lean action (`Decompose` /
  `GiveUp` / `ExternalResponseRejected` / a policy-rejected `SubmitModule`) in
  one transaction, or — for `Solve` / a policy-passing `SubmitModule` — returns
  exactly what's needed to call the gateway, WITHOUT calling it.
- The MCP layer commits that transaction, drops the DB-lock guard, calls the
  gateway, then re-acquires the lock and opens a fresh transaction.
- `attempt_finalize` re-validates the attempt is still `executing` with the
  same claim token (protecting against a concurrent expiry sweep reclaiming a
  wedged attempt during the gap) and writes the result.

`attempt_commit` still exists as a convenience wrapper (`attempt_prepare` +
gateway call + `attempt_finalize` in one call) for callers that run
synchronously outside any async lock — direct unit/integration tests driving a
bare `rusqlite::Transaction`. The MCP layer never uses it; it calls
`attempt_prepare`/`attempt_finalize` directly so the gap between them is where
the lock is actually released.

## Outcomes and rewards

`SubmitModule` is a kernel-verification action, exactly like `Solve`:

- a passing module earns `kernel_pass` and closes the root obligation;
- a root proof under a fidelity-**verified** problem reaches `certified`
  (`terminal_success`);
- a root proof under an **attested** (dev-bypass) problem reaches
  `kernel_verified` (`root_kernel_verified`) — proof soundness without statement
  fidelity, never `certified`.

Proof soundness (did the kernel check this exact formal statement?) and
statement fidelity (does that statement represent the source problem?) remain
independent — `SubmitModule` changes how the formal statement is *proved*, not
how fidelity is decided.
