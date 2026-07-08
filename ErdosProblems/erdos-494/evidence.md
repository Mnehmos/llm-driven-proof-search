# Machine evidence — Erdős #494 (product version false)

## Verification record

| field | value |
|---|---|
| theorem | `Erdos494.product : ∃ A B : Finset ℂ, A.card = B.card ∧ prodMultiset A 3 = prodMultiset B 3 ∧ A ≠ B` |
| corpus target | `erdos_494.variants.product`, shipped `sorry` |
| key lemma | `prodMultiset_map_mul : c^k = 1 → prodMultiset (A.map (c·)) k = prodMultiset A k` |
| witness | `A = {1, ω, ω², 2}`, `B = ω·A`, `ω` a primitive cube root of unity |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| local verification | `lake env lean LeanChecker/Erdos/Erdos494.lean` → exit 0, **0 errors, 0 warnings** |
| proof snapshot sha256 | `9fd75fcfe16f863a341387c48f5ec77d019ddc1e3b8191e232f6d70da0b0cdb1` |
| toolchain | lean4:v4.32.0-rc1 + mathlib@360da6fa |

## Note
The proof avoids computing `powersetCard` on a `ℂ` Finset (which is
noncomputable) entirely — it works via `Finset.powersetCard_map` and the scalar
identity `∏_{x∈s}(c·x) = c^{|s|}·∏ x`, so with `|s| = 3` and `ω³ = 1` each
3-subset product is preserved. Cardinality equality is `Finset.card_map`, so
distinctness of `A`'s elements is never needed.

## Tracked-pipeline status — SUBMITTED (kernel_verified)

Re-verified through the tracked MCP episode pipeline (dev-attested → `kernel_verified`):

| field | value |
|---|---|
| problem_version_id | `febdc499-4e4f-4fb9-be05-d3963f8a491b` |
| root_statement_hash | `04cce66ba861146eb6b437749364c9d2573f37410f3892737fde579d0cfca3ee` |
| episode_id | `2913e364-0fdc-47f5-aa07-28bd0db3557f` |
| outcome | **kernel_verified**, `root_proved`, pass@2 (1st attempt used bare `mapEmbedding`; MCP has no `open Finset`, so qualified to `Finset.mapEmbedding`) |
| fidelity basis | `unsafe_dev_attestation` |

Submitted as one `solve`/`raw_lean_block` action with `prodMultiset_map_mul`
inlined as a local `have`, pre-validated locally.
