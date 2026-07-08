# Import Policy — Formal Conjectures

Rules for importing a statement from the upstream Formal Conjectures
repository:

1. Record upstream source, file path, commit hash (if available), problem
   name, domain, and statement hash.
2. Classify the packet as one of:
   - `open` — no known proof.
   - `solved-unproved-in-this-repo` — solved upstream/elsewhere but not
     yet formalized here.
   - `already-formally-proved-upstream` — a Lean proof already exists
     upstream.
   - `source-review-needed` — provenance or statement fidelity unclear.
3. Do not import a statement without recording its source in
   `SOURCE_MAP.md`.
4. Do not treat every imported statement as training-eligible — see
   `STATEMENT_FIDELITY.md`.

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
