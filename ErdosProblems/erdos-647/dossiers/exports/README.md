# Erdős #647 proof-search exports

Generated 2026-07-16 from the tracked proof-search environment.

This directory is the complete export archive for all 340 related episodes
identified by campaign source, explicit Lean provenance, the evidence ledger,
and a read-only transitive closure over matching problem and statement hashes.

## Outcome inventory

- 333 episodes report `KERNEL_VERIFIED` and `kernel_verified = true`.
- 3 unfinished episodes report `IN_PROGRESS`.
- 3 terminated unsuccessful episodes report `GAVE_UP`.
- 1 truncated episode reports `budget_exhausted`.

Keeping the 7 non-success histories is intentional: they preserve abandoned,
unfinished, and budget-limited routes instead of presenting only successful
trajectories.

## Layout

- `manifest.tsv`: one row per episode, including problem ID, outcome,
  fidelity status, environment hash, statement hash, timestamps, and step count.
- `EPISODES.md`: human-readable enumeration of included episode IDs and outcomes.
- `public_summary/`: redacted JSON summaries with statements and metadata.
- `full/`: full Markdown proof dossiers, including assembled Lean proofs and
  trajectory narratives where they exist.
- `training/`: structured JSON trajectory exports, including accepted proof
  actions, negative histories, and verifier metadata.

All 340 exports report `fidelity_status = attested` and environment
`9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`.

The fidelity label matters: these are project-authored formal statements checked
by Lean, not independently certified transcriptions from a neutral benchmark.
The repository-level final density composition is separately documented in
`../public-summaries.md` and `../../evidence.md`; it is a clean transitive
source replay, not a fabricated additional proof-search episode.

The committed Lean files under `../../proof/` remain the simplest portable
artifact for third-party checking. These exports preserve the proof-search
provenance and full audit trail.
