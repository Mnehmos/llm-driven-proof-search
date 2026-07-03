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
  `universe`, a declaration keyword (`def`, `theorem`, `lemma`, `example`,
  `abbrev`, `instance`, `structure`, `inductive`, `class`, `axiom`, `opaque`,
  `unsafe`, `partial`, `noncomputable`), or metaprogramming/eval commands
  (`macro`, `syntax`, `elab`, `notation`, `#eval`, `#check`, …). This is the
  injection boundary: a def body of `0\n\naxiom cheat : False` opens a new
  top-level command and is refused, not compiled.
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

A rejected module (whether refused by policy or by the staged kernel) surfaces
its reason directly on the `episode_step` response as `rejection_diagnostic`, so
a client learns *why* the draft was refused without a second `episode_observe`
round-trip. The same reason is stored as the obligation's failure lesson and
shown by `proof_export`.

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

## Persistence, export, and replay

A successful module is remembered as a structured, replayable artifact — not
just a compiled side effect — so module solves become first-class training data.

- **`episode_verified_modules`** — one row per verified module: the root
  obligation it proves, the root statement / import manifest / environment
  hashes, the `module_source_hash`, the `declaration_manifest_hash`, the kernel
  result hash, and `module_items_json` (the exact structured items + root
  theorem). Because assembly is deterministic, re-assembling from
  `module_items_json` reproduces byte-identical source (hashing to
  `module_source_hash`).
- **`episode_verified_module_items`** — one row per declaration, in assembly
  order: kind (`def` / `theorem` / `root_theorem`), local name, statement-or-type
  and body hashes, dependency metadata, and policy result. The single
  `root_theorem` row is linked to the root obligation through its parent module
  row.

Both tables are created by `CREATE TABLE IF NOT EXISTS`, so a pre-existing
v0.2.5 database gains them on the next init with no migration and no change to
existing rows.

The `action_committed` trajectory event for a module carries the
`module_source_hash` and `declaration_manifest_hash`, so replay can confirm the
exact artifact re-derives:

- **`proof_export(format="lean")`** returns the exact module source (re-assembled
  from `module_items_json`), byte-for-byte replayable. The markdown dossier adds
  a **Verified module** section with the declaration manifest and source.
- **`episode_replay`** re-parses the structured action, re-assembles the module,
  and **fails** if the re-assembled `module_source_hash` /
  `declaration_manifest_hash` differ from what was recorded — then re-verifies
  through the gateway and checks the outcome matches. Replay never trusts an
  opaque saved file.
- Dataset RL exports tag each step `solve_kind`:
  `single_theorem_solve` vs `verified_module_solve`.
