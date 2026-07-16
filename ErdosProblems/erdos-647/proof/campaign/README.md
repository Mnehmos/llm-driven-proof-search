# Full campaign proof bodies

The parent [proof/](../) directory now contains the full analytic and density
assembly as individual Lean modules. This subfolder holds the five consolidated
modular-campaign families recovered from the tracked pipeline. Every
`.lean` file here is self-contained: it checks against Mathlib with `lake`
alone, with no dependency on the project's local database.

## How a proof body is (internally) re-derivable

Every catalogued theorem's full `episode_id` is recorded in
[../../dossiers/episode-index.tsv](../../dossiers/episode-index.tsv). This is
**not a public retrieval path** — it only lets *us*, holders of the local
proof-search database, re-run `proof_export{episode_id, format: "lean"}` to
regenerate a body if a committed file is ever lost. Anyone without that
database gets nothing from an episode_id; the committed `.lean` source below
is the only thing that is actually publicly checkable.

## Committed here (fully published)

- [family1-sieve-certificates.lean](family1-sieve-certificates.lean) — all 8
  sieve counting certificates (`native_decide` cardinality proofs).
- [family2-classifications.lean](family2-classifications.lean) — all 14 shift
  classification theorems (shift-bound extraction + p-adic decomposition).
- [family3-bridging-closures.lean](family3-bridging-closures.lean) — all 21
  bridging-closure theorems (`coeff·N % ℓ ≠ 1`, derived from the matching
  Family-2 classification), covering both the `ℓ ≤ 19` and `ℓ ≤ 29` tiers.
- [family4-residue-closures.lean](family4-residue-closures.lean) — all 4
  frontier-shrinking residue closures (39325, 41470, 40612, 26884).
- [family5-subap-closures.lean](family5-subap-closures.lean) — all 48 sub-AP
  congruence closures, one per (residue, extra-prime) pair.

Every catalogued theorem across all five modular families is published as
committed, self-contained `.lean` source. The later analytic episodes have
individual source modules in the parent directory and complete provenance
exports under [../../dossiers/exports/](../../dossiers/exports/README.md).

Everything here is `kernel_verified`, pinned to
`environment_hash 9e26d28e…`; the global density theorem is complete, while
the original existence problem itself remains **open**.
