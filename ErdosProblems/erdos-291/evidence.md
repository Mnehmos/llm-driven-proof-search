# Machine evidence — Erdős #291 (ii)

## Verification record

| field | value |
|---|---|
| theorem (core) | `Erdos291.infinite_gcd_gt_one : {n : ℕ \| 1 < Nat.gcd (a n) (L n)}.Infinite` |
| theorem (corpus shape) | `Erdos291.erdos_291_parts_ii : True ↔ {n \| Nat.gcd (a n) (L n) > 1}.Infinite` |
| definitions | `L n = (Finset.Icc 1 n).lcm id`, `a n = ∑_{k∈Icc 1 n} L n / k` (corpus-identical) |
| construction | `n = 2·3^k` infinite family; injective witness `k ↦ 2·3^{k+1}` |
| local verification | `lake env lean LeanChecker/Erdos/Erdos291.lean` → exit 0, **0 errors, 0 warnings** |
| proof snapshot sha256 | `431057c3ea5c4472ba904b03e72fe8a3c96754d3323d925d4ae7f56bcf31ab22` |
| toolchain | lean4:v4.32.0-rc1 + mathlib@360da6fa |

## Cross-checks (in-file `example`s, all by `decide`)
- `L 1 = 1 ∧ L 2 = 2 ∧ L 3 = 6 ∧ L 4 = 12` (matches corpus `L_eval`).
- `a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 11 ∧ a 4 = 25` (matches corpus `a_eval`).
- `Nat.gcd (a 6) (L 6) > 1` and `Nat.gcd (a 18) (L 18) > 1` — the `n=2·3^k`
  construction lands in the target set for `k = 1, 2` (independent decidable
  confirmation of the general argument).

## Tracked-pipeline status — SUBMITTED (kernel_verified)

Re-verified through the tracked MCP episode pipeline (dev-attested fidelity
basis → `kernel_verified`, the honest ceiling for a dev attestation):

| field | value |
|---|---|
| problem_version_id | `731bdae8-f2e4-4102-a863-96d0dd0d390f` |
| root_statement (a, L inlined) | `{n : ℕ \| 1 < Nat.gcd (∑ k ∈ Finset.Icc 1 n, (Finset.Icc 1 n).lcm (fun x => x) / k) ((Finset.Icc 1 n).lcm (fun x => x))}.Infinite` |
| root_statement_hash | `e22625b4686d07a3e829dc0cee20c17c718f4a1c3a4f1bbc16a9d63848d96b76` |
| episode_id | `e2320b06-fc24-4f86-909f-793685c3ce61` |
| outcome | **kernel_verified**, `root_proved`, pass@1 |
| fidelity basis | `unsafe_dev_attestation` (attested → kernel_verified, never certified) |
| import manifest | `["Mathlib.Tactic.Ring", "Mathlib.Tactic.NormNum", "Mathlib"]` |

The whole development (`L`, `a` as local `let`s; every lemma inlined as a
`have`; bridged to the inlined statement by `show`) was submitted as one
`solve` action with `proof_format: raw_lean_block`, pre-validated locally before
submission.
