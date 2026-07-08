# Trace Policy — Combinatorics (Elementary)

All meaningful proof work for packets in this folder must stay inside the
MCP evidence rail, or be explicitly ingested into `trace.md` afterward.

This includes:

- Formal statements and proof attempts
- Lean diagnostics and compiler output
- Generated scripts and files
- Mathlib/source lookups and search results
- Failed routes and route pivots
- Repair notes
- Final proof exports

Private reasoning is not proof authority — only a Lean-verified result,
recorded through the proof-search MCP environment, counts as a proved
packet.

## Global Operating Rule

Do not let proof work escape the proof environment.

Meaningful proof work includes: formal statements, Lean diagnostics, proof
attempts, generated scripts, generated files, source reviews, failed routes,
route pivots, Mathlib lookup failures, repair notes, final proof exports.

- If it matters to how the proof was found, record it.
- If it proves the theorem, verify it through Lean.
- If it fails, record the failure.
- If it uses another domain, record the dependency.
- If it becomes reusable, promote it to `shared/`.

Private reasoning is not proof authority. Lean decides. The ledger records.
