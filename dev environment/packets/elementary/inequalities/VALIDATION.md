# Validation — Inequalities (Elementary)

Before marking a packet complete in this domain, confirm:

- [ ] `statement.lean` type-checks and matches the packet's stated theorem
      (statement fidelity).
- [ ] `proof.lean` compiles with no `sorry` (or `sorry` is explicitly
      declared and tracked in `BLOCKERS.md`).
- [ ] The proof attempt was submitted and verified through the proof-search
      MCP environment (attempt/episode tools), not produced purely in
      private reasoning.
- [ ] `trace.md` reflects the MCP-tracked research trace for this packet
      (episode id, attempt ids, key pivots).
- [ ] `metadata.json` is complete: domain, level, status, source, tags.
- [ ] Redaction / benchmark-contamination check passed if the source is a
      benchmark problem.
- [ ] `export.md` states training eligibility and any restrictions.
- [ ] `DASHBOARD.md` and `QUEUE.md` in this folder are updated to reflect
      the new packet.

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
