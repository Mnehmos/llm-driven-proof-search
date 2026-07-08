# Machine evidence — Erdős #399 (Cambie companion)

## Verification record

| field | value |
|---|---|
| theorem | `Erdos399.cambie : ∀ {n x y : ℕ}, x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4` |
| corpus target | `erdos_399.variants.cambie` (byte-identical), shipped `sorry` |
| method | mod-8 parity of fourth powers + `8 ∣ n!` for `n ≥ 4`; size bound for `n ≤ 3` |
| key lemma | `pow4_mod8 : a ^ 4 % 8 = a % 2` (finite check over residues) |
| local verification | `lake env lean LeanChecker/Erdos/Erdos399.lean` → exit 0, **0 errors, 0 warnings** |
| proof snapshot sha256 | `eefb770b0aef6fd5cbef46cbd54a4fc03ebdf6d49a006815c7b0497ddaaa8da9` |
| toolchain | lean4:v4.32.0-rc1 + mathlib@360da6fa |

## Tracked-pipeline status — SUBMITTED (kernel_verified)

Re-verified through the tracked MCP episode pipeline (dev-attested fidelity
basis → `kernel_verified`, the honest ceiling for a dev attestation):

| field | value |
|---|---|
| problem_version_id | `7492a839-57a3-40de-81ce-001849d82605` |
| root_statement (inlined) | `∀ (n x y : ℕ), x.Coprime y → 1 < x * y → Nat.factorial n ≠ x ^ 4 + y ^ 4` |
| root_statement_hash | `f32595d2617669913e126e3b937b9325c0c640c07b12fb9e0102653ac517ecfc` |
| episode_id | `4f6b38ec-a47f-4817-bb39-c0a96ba21469` |
| outcome | **kernel_verified**, `root_proved`, pass@2 (1st attempt hit the `n !` factorial-notation parse gap without `open Nat`; 2nd used explicit `Nat.factorial n` and passed) |
| fidelity basis | `unsafe_dev_attestation` (attested → kernel_verified, never certified) |
| import manifest | `["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]` |

The whole development (incl. the `pow4_mod8` helper, inlined as a local `have`)
was submitted as one `solve` action with `proof_format: raw_lean_block`.
