# Erdős Frontier

The Erdős lane for the MathCorpus agent workspace: formalizing known
companion results, replacing corpus `sorry`s where possible, building
attack plans, and honestly separating solved, partial, companion, and
open-problem work.

Anti-hype rule: no open Erdős problem is claimed solved unless the proof is
Lean-verified, statement fidelity is reviewed, and the result is clearly
separated from known companion theorems or partial infrastructure.

Existing repo context — this folder is the new agent-loop workspace layer
for MathCorpus packet bookkeeping. It does not replace or duplicate the
existing Erdős research already in the repo:

- `ErdosProblems/` at the repo root holds the existing per-problem Lean
  work (e.g. `erdos-9`, `erdos-291`, `erdos-672`) and its own
  `whitepaper.md`.
- `docs/erdos/bounty-board.md` tracks the existing bounty/target board.

Cross-reference those locations before starting new work here; use this
folder to track companion-result packets, partial-result infrastructure,
and source review specific to the MathCorpus packet pipeline.

- Open problems: see `OPEN_PROBLEMS.md`
- Companion results: see `COMPANION_RESULTS.md`
- Partial results: see `PARTIAL_RESULTS.md`
- Stalled work: see `BLOCKERS.md`
- Source review: see `SOURCE_REVIEW.md`
- Run this folder: see `LOOP.md`
- Packet shape: see `PACKET_TEMPLATE.md`
- Whitepaper-eligible results: see `WHITEPAPER_QUEUE.md`

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
