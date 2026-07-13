# Machine evidence — Erdős #647 campaign

> Living document; last updated 2026-07-13. All records below are from the
> tracked MCP episode pipeline (dev-attested fidelity basis →
> `kernel_verified`, the honest ceiling for a dev attestation). Import
> manifest for every entry: `["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]`.
> Environment hash for the 2026-07-13 session:
> `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`.

## Headline records (proof snapshots in [proof/](proof/))

### Theorem 2 (prime-chain reduction) — stage k = 1,2

| field | value |
|---|---|
| statement | `∀ n : ℕ, 24 < n → ArithmeticFunction.sigma 0 (n-1) ≤ 3 → ArithmeticFunction.sigma 0 (n-2) ≤ 4 → ∃ q, Nat.Prime q ∧ n = 2*q+2 ∧ Nat.Prime (n-1)` |
| problem_version_id | `1987e20c-6d03-4882-8c20-d0495744d9e9` |
| episode_id | `c4a688c1-053c-4e08-8da3-e3ab7c4c594e` |
| root_statement_hash | `4b5752c641c3fb016f1ecc6dae940feff8d02251d55880a491590964f7307c95` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_Thm2_Stage12.lean](proof/Erdos647_Thm2_Stage12.lean) |

### Theorem 2 — stage k = 4

| field | value |
|---|---|
| statement | `∀ q : ℕ, 13 ≤ q → q.Prime → (2*q+1).Prime → ArithmeticFunction.sigma 0 (2*q-2) ≤ 6 → ∃ p, p.Prime ∧ q = 2*p+1` |
| problem_version_id | `52ff69c0-e7f5-443c-9cc1-14da17c92dd4` |
| episode_id | `57bf2fb3-7a57-4644-b99a-f97ff2aa600c` |
| root_statement_hash | `f940625c1484f450d165e8f450a8f8c7eef5a39fc451e5f0f0a70f24f6c97afc` |
| outcome | **kernel_verified**, `root_proved`, pass@1 |
| snapshot | [proof/Erdos647_Thm2_Stage4.lean](proof/Erdos647_Thm2_Stage4.lean) |

### Theorem 2 — stage k = 8 (final family split)

| field | value |
|---|---|
| statement | `∀ p : ℕ, 7 ≤ p → p.Prime → (2*p+1).Prime → ArithmeticFunction.sigma 0 (4*p-4) ≤ 10 → ∃ s, s.Prime ∧ (p = 2*s+1 ∨ p = 4*s+1)` |
| problem_version_id | `513c65fa-b031-479b-aa97-7d39091e7587` |
| episode_id | `95fae0a4-f448-4236-9039-604e5cb902e7` |
| root_statement_hash | `068b74ebba069c507eb598bade6aced904cb882e6b46745dedaeb1f97052382a` |
| outcome | **kernel_verified**, `root_proved`, pass@1 |
| snapshot | [proof/Erdos647_Thm2_Stage8.lean](proof/Erdos647_Thm2_Stage8.lean) |

### Layer A — exact Mertens identity via Chebyshev θ

| field | value |
|---|---|
| statement | `∀ x : ℝ, 2 ≤ x → ∑ p ∈ Finset.Icc 1 ⌊x⌋₊ with p.Prime, (1/(p:ℝ)) = Chebyshev.theta x / (x * Real.log x) + ∫ t in Set.Ioc (2:ℝ) x, (Real.log t + 1) / (t^2 * (Real.log t)^2) * Chebyshev.theta t` |
| problem_version_id | `d584666d-e50d-488d-b459-5d1265a3aadd` |
| episode_id | `7a7e8098-a5bf-4dd9-97df-145e34ee914b` |
| root_statement_hash | `9802976a83cd2b4a604d3a77e6f1c4cf2800c41b9ec7797550df9f1fa28a7c98` |
| outcome | **kernel_verified**, `root_proved` |
| snapshot | [proof/Erdos647_MertensIdentity.lean](proof/Erdos647_MertensIdentity.lean) |

## Campaign ledger (problem_version_id index, 2026-07-12/13 sessions)

Base sieve & refinement certificates: `200bce1c` (48 survivors mod 46189),
`a001e7c1` (mod 23, 528), `4d2b7ec1` (mod 29, 768), `83fb9810` (mod 31, 864),
`b4196b16` (mod 37, 1152), `2f28d8d4` (mod 41, 1344), `c0f6a321` (mod 43,
1440), `b9083710` (45-class frontier certificate).

Shift classifications (13): `00cfc756` (shift 1), `87ea1d9a` (2), `323c4801`
(3), `14a21b69` (4), `e4397627` (5), `245e963a` (6), `0f8dcd94` (8),
`8ed738c7` (9), `6c5dcfd9` (10), `b9c90e1d` (12), `1710efdc` (18), `5a643568`
(20 — with the genuine `r=125` exception), `5df5a27e` (24). Reusable
characterization lemma: `fb7d4bf8`.

Bridging closures: 9 at ℓ≤19 (`de35e7ec`, `8a65bb51`, `dfb82405`, `ddc951c3`,
`c0565e84`, `efc75f5f`, `b542e676`, `a62e9824`, `7e6d5dde`) and 13 at ℓ≤29
(`90c306f4`, `3aa31e38`, `7f68e7f0`, `e6345707`, `c3337705`, `ec6ecc6a`,
`9bd67f4d`, `5ba4356c`, `84df59dc`, `b1b996c8`, `b0d5b386`, `9c93a1d6`, plus
shift-5's `7e6d5dde` tier).

Residue closures (45 → 41, matching Hughes): `e8e7b8cd` (N≡39325,
direct-full-value), `15bdd8f4` (41470, single-overlap + ZMod 8), `49ae1aa9`
(40612), `fa7e0a1f` (26884, 4-prime modulus, 11-leaf tree).

Sub-AP closures (48, frozen per the all-avoid obstruction): discovery closure
`40988498`; wave A–E `3f98ba86`, `d037ea2a`, `a109a5af`, `4b799f58`,
`02d5a4a3`; waves F–L including `82b78dec`, `1a283efe`, `32706bae`,
`61612470`, `0822d882`, `9a615fba` and 36 more (full list reproducible from
the environment's problem ledger by statement pattern
`N % <46189·p> = r → False`).

## Reproduction notes

- The `.lean` files in [proof/](proof/) are byte-faithful snapshots of the
  exact statement + proof term the kernel accepted through the tracked
  pipeline (statement hashes above). They are written as standalone files
  under `import Mathlib` with the same manifest the environment pinned.
- The tracked pipeline's episode ledgers (hash-chained, append-only) live in
  the proof-search environment's database; the IDs above are the lookup
  keys. This folder deliberately records *pointers + snapshots*, not the
  database itself.
- Honest caveat: these snapshots have not been re-executed by a second,
  independent local `lake` build in this repository yet (the environment's
  pinned toolchain is the verifying authority). Standing this folder up
  with a local `LeanChecker` harness replay, as done for erdos-291/-1052,
  is an open task in [attack-plan.md](attack-plan.md).
