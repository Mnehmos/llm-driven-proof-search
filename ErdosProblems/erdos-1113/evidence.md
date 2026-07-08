# Machine evidence — Erdős #1113 (infinitely many Sierpiński numbers)

## Verification record

| field | value |
|---|---|
| theorem | `Erdos1113.infinitely_many_sierpinski : Set.Infinite {k : ℕ \| IsSierpinskiNumber k}` |
| corpus target | `erdos_1113.variants.infinitely_many_sierpinski`, shipped `sorry` |
| key lemma | `sierpinski_of_congr : ¬2∣k → k ≡ 78557 [MOD 70050435] → IsSierpinskiNumber k` |
| construction | AP `k = 78557 + j·(2·70050435)`, injective in `j` |
| covering | `{3,5,7,13,19,37,73}`, checked on `n mod 36` (`2³⁶ ≡ 1 mod p`) via kernel `decide` |
| axioms | `[propext, Classical.choice, Quot.sound]` — **no `native_decide`/`ofReduceBool`** |
| local verification | `lake env lean LeanChecker/Erdos/Erdos1113.lean` → exit 0, **0 errors, 0 warnings** |
| proof snapshot sha256 | `a484532165643ae4b2479cb9c0047e450d9a78cb6e3cc60cfd964a9e0061b078` |
| toolchain | lean4:v4.32.0-rc1 + mathlib@360da6fa |

## Notes
- The covering data (which prime of `{3,5,7,13,19,37,73}` divides `78557·2ⁿ+1`
  for each `n mod 36`) was computed externally and confirmed: all 36 residues
  covered; `2³⁶ ≡ 1` mod each prime; `M = 70050435` odd. Inside Lean these are
  discharged by kernel `decide` (needs `maxHeartbeats 4000000`).
- Strengthens the corpus's `SierpinskiNumber.selfridge_78557` (single number,
  `native_decide`) to infinitude and to pure kernel verification.

## Tracked-pipeline status — SUBMITTED (kernel_verified)

Re-verified through the tracked MCP episode pipeline (dev-attested fidelity
basis → `kernel_verified`):

| field | value |
|---|---|
| problem_version_id | `d94c5069-3e35-4657-8b71-30bc3af375f4` |
| root_statement (inlined) | `Set.Infinite {k : ℕ \| ¬ 2 ∣ k ∧ ∀ n, 1 < k * 2 ^ n + 1 ∧ ¬ (k * 2 ^ n + 1).Prime}` |
| root_statement_hash | `6a5b10b0c93e7d8fd566b18d248d995ca66eecfca26c7c4fddbcc158bf32ad24` |
| episode_id | `d5873431-9857-4e75-ac22-65e69cb40b02` |
| outcome | **kernel_verified**, `root_proved`, pass@1 |
| fidelity basis | `unsafe_dev_attestation` (attested → kernel_verified) |

Submitted as one `solve`/`raw_lean_block` action with `sierpinski_of_congr`
inlined as a local `have`; the two covering `decide`s were wrapped
`set_option maxHeartbeats 4000000 in decide` (no theorem-level option needed),
pre-validated locally before submission.
