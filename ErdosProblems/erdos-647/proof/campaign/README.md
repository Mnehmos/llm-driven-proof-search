# Full campaign proof bodies

The eight headline theorems (Theorem 2 ×3, Layer A ×5) have their full Lean
source in the parent [proof/](../) directory. This subfolder holds full proof
bodies for the rest of the campaign, recovered from the tracked pipeline. Every
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

## Not yet committed

- **Family 5 — sub-AP closures (48):** the sub-cell-closure template, one per
  (residue, prime) pair, backing the mod-23·23 sub-AP layer. Reproducible via
  the episode index above; not yet materialized as committed `.lean` source.

Everything here is `kernel_verified`, pinned to
`environment_hash 9e26d28edb…`; the problem itself remains **open**.
