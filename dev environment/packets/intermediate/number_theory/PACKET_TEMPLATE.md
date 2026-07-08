# Packet Template — Number Theory (Intermediate)

Required files:

- `packet.md` — human-readable summary
- `statement.lean` — formal statement
- `proof.lean` — formal proof (or `sorry` if incomplete)
- `metadata.json` — domain, level, status, source, tags
- `trace.md` — MCP-tracked research/attempt trace
- `validation.md` — validation commands/results
- `export.md` — export/training-eligibility status
- `notes.md` — free-form notes

Optional files:

- `failed_routes.md`
- `source_review.md`
- `scratch.md`
- `generated/`
- `artifacts/`
- `diagnostics/`

A complete packet answers:

1. What is the theorem?
2. What domain and level is it?
3. What was proved?
4. What was not proved?
5. What source or curriculum role does it serve?
6. What proof method was used?
7. What failed first?
8. What Lean result verifies it?
9. What export policy applies?
10. Can it be used for training?

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
