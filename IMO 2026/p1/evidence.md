# Evidence — IMO 2026 Problem 1

All formal work was tracked through the proof-search MCP. The Lean files under
[proof/](proof/) are direct proof_export(format=lean) outputs.

## Trust boundary

| Field | Value |
|---|---|
| Environment hash | 9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d |
| Import-manifest hash | aaf21893d520a78dee0787a1bcaf939ee6b922265ff670c272e2e1d450dd29a7 |
| Fidelity status | attested for every registered target |
| Certified | false for every target |
| Formal target matched | complete root statement hash matched in final episode |
| Kernel outcome | KERNEL_VERIFIED for complete root and seven components |

Kernel verification means Lean accepted the registered proposition. Because
the registrations used development attestation, it does not certify that any
formalization is independently fidelity-reviewed.

## Problem and episode records

| Target | Problem version | Statement hash | Episode | Attempts | Accepted attempt |
|---|---|---|---|---:|---|
| Exponent Euclidean-step gcd | 8087c6d9-e311-4707-b117-8e2a657a2921 | bcbbf4a2af241fe11c9ccc7cf03f9a48040ccce021e248c8001624eff8183557 | e118ad1a-aa66-41c6-819b-6e9e9f1d6c26 | 1 | 211263d2-b529-4ec4-89e2-4114dcfef455 |
| Pair product and lcm positivity | 533ea12d-a8d8-4016-bbee-26393c106a93 | 4c943c202472e653e0faac013ad9e9b4bc6269626a4477b79e50c1250492997c | 8a051323-a560-4c48-963d-6be3eb9f377d | 1 | 48a5f543-69c7-4e40-a721-4ee658f0f412 |
| Bounded lexicographic measure | 02947dd1-4421-4a98-b57a-27807fcd7499 | 6f9b4fd528b1a8bd07f2741e78254fdf10a10234db0183548be03e4a38afe319 | 0a2f5935-2f6c-4e28-ba07-91781fc7a61a | 1 | 465d75ca-81e8-4666-bd08-1d2083304956 |
| Move factorization | cc1fac20-e486-458c-99d2-226eb0703e58 | 701667d54651d2bd15c523e29e0249e2e55f85f24ebfca256c9210d631b72e6d | 8201d251-26b9-42a7-9205-2a1fc616fc7b | 1 | c61d8fc6-3998-4471-ba6b-48d5cf2b6edf |
| Multiset exponent gcd | 5c78677c-2b2c-4bd5-967c-1fc471db0bd8 | 91464b08d31247a7a06e2ef3e8118f50684c56dbd1559d95fed14c5d4a23be1a | d0f44790-23cd-4ba4-bb2f-419a208557a8 | 3 | 950fea64-9f6d-4397-98d4-b6f15523d755 |
| Move-local lexicographic decrease | 36eb65c0-e36a-4752-b972-e52d49e2e8fc | 827cd791f282856f8c1a5082b550d6e749b9c6df9f228ab9d27f89caa33fa94f | 7ccdfda4-1c74-47e2-987f-6f57d184e03a | 2 | 3166adbe-aea0-406b-8e9f-0a61c267f214 |
| 2026-entry move well-foundedness | 75bfb0f4-e1be-4f8b-ad26-41481170b336 | a914f8f9ff72f892442a01dc50319e764267f3fd32d2ab5eb7d773ac1d98d22d | 41680cd0-83ce-4c0f-807d-c12457abcc83 | 8 | 68b7cbb7-aac7-4b7f-907f-5c91dcdf9d7d |
| Complete IMO P1 root | 97d0b02d-054e-4530-a28f-d31036609628 | 93d5fd4c90e5a6ba942c2b013d86c867a2a5433fc3589214fbe5c9d0773394d5 | afae1dbb-fca6-4de1-b64d-a74bb53f16b3 | 6 | 9d005cdf-f3a8-4079-88b6-15ac8a86dac7 |

Every accepted episode ended with outcome=kernel_verified and
termination_reason=root_proved.

## Exported proof snapshots

| Episode | Direct Lean export |
|---|---|
| e118ad1a… | [IMO2026P1_ExponentEuclidGcd.lean](proof/IMO2026P1_ExponentEuclidGcd.lean) |
| 8a051323… | [IMO2026P1_PairProduct.lean](proof/IMO2026P1_PairProduct.lean) |
| 0a2f5935… | [IMO2026P1_BoundedLexMeasure.lean](proof/IMO2026P1_BoundedLexMeasure.lean) |
| 8201d251… | [IMO2026P1_MoveFactorization.lean](proof/IMO2026P1_MoveFactorization.lean) |
| d0f44790… | [IMO2026P1_MultisetExponentGcd.lean](proof/IMO2026P1_MultisetExponentGcd.lean) |
| 7ccdfda4… | [IMO2026P1_MoveLocalLexDecrease.lean](proof/IMO2026P1_MoveLocalLexDecrease.lean) |
| 41680cd0… | [IMO2026P1_Termination.lean](proof/IMO2026P1_Termination.lean) |
| afae1dbb… | [Final.lean](proof/Final.lean) |

## Failure history retained

- MultisetExponentGcd: two failed attempts before success. The first used
  Nat.gcd_assoc against generic GCDMonoid.gcd; the second still lacked an
  explicit change back to Nat.gcd.
- MoveLocalLexDecrease: one failed attempt caused by multiplication
  association and an unsimplified lcm filter predicate.
- Termination: seven failed attempts before success. The trail retains helper
  transport errors, WellFounded.onFun repair, Multiset.filter_le API repair,
  subtype transport failures, and the composite-measure congrArg solution.
- Complete root: five failed submissions before success. The trail retains
  SubmitModule proof-transport repair, exact root-hash enforcement, nested
  helper restructuring, and three final arithmetic API repairs.

Hash-chain endpoints and replay commands are in
[trace/trajectory.md](trace/trajectory.md). Reasoning logs remain in the MCP
ledger.

## Trust limitation

The complete root is kernel-verified and its exported source replays locally.
Its problem registration used development attestation, so this is not a
certified fidelity judgment by an independent reviewer.
