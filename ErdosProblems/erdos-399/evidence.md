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

## Tracked-pipeline status
Verified directly via `lake env lean`. Re-submission through the tracked MCP
episode pipeline is the natural next step to match the #1052/#349 audit
standard — pending (batched with #291.ii).
