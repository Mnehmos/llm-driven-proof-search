# Formal Conjectures (Frontier)

Statement and proof packets imported from the upstream Formal Conjectures
repository. Formal Conjectures packets are **not** the same as
elementary/intermediate curriculum packets: they start as statement
packets, and only become proof packets after Lean verification. They only
become training-eligible after statement fidelity, source attribution,
proof verification, redaction policy, and export policy are all recorded.

Open conjectures are not treated as easy proof targets. For open problems,
build dossiers, attack plans, source maps, partial lemmas, and failed-route
traces unless there is a concrete formal path.

- Import rules: see `IMPORT_POLICY.md`
- Source tracking: see `SOURCE_MAP.md`
- Fidelity review: see `STATEMENT_FIDELITY.md`
- Solved-but-unformalized queue: see `SOLVED_QUEUE.md`
- Open problems queue: see `OPEN_QUEUE.md`
- Proof attempt log: see `PROOF_ATTEMPTS.md`
- Stalled work: see `BLOCKERS.md`
- Run this folder: see `LOOP.md`
- Packet shape: see `PACKET_TEMPLATE.md`

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
