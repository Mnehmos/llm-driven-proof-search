# Full campaign proof bodies

The eight headline theorems (Theorem 2 ×3, Layer A ×5) have their full Lean
source in the parent [proof/](../) directory. This subfolder holds full proof
bodies for the rest of the campaign, recovered from the tracked pipeline.

## How every proof body is retrievable

All **104** catalogued theorems have their full `episode_id` recorded in
[../../dossiers/episode-index.tsv](../../dossiers/episode-index.tsv). Any body is
one call away:

```
proof_export{episode_id: "<from episode-index.tsv>", format: "lean"}
```

returns the complete, kernel-verified Lean source (as re-verified through the
pinned environment). `format: "public_summary"` returns the redacted record;
`episode_replay` re-runs it through the Lean kernel.

## Committed here

- [family4-residue-closures.lean](family4-residue-closures.lean) — three of the
  four frontier-shrinking residue closures (39325, 41470, 40612), the
  substantial mathematically-distinct proofs; the fourth (26884) is noted inline
  with its episode id.

## Not separately committed (retrievable via the index)

- **Family 1 — sieve counting certificates (9):** short `native_decide`
  cardinality proofs.
- **Family 2 — shift classification theorems (14):** the necessary-condition
  theorems; template-based (shift-bound extraction + p-adic decomposition).
- **Family 3 — bridging-closure theorems (21):** near-identical instances of one
  template (`coeff·N % ℓ ≠ 1` from the classification), one per coefficient.
- **Family 5 — sub-AP closures (48):** near-identical instances of the
  sub-cell-closure template, one per (residue, prime) pair.

These four families are dominated by template repetition — committing ~92
near-duplicate bodies would add bulk without insight, and the episode index
makes any of them reproducible on demand. If you want the complete set of `.lean`
files materialized, export each `episode_id` in the index with
`format: "lean"`.

Everything here is `kernel_verified`, pinned to
`environment_hash 9e26d28edb…`; the problem itself remains **open**.
