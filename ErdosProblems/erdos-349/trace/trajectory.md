# Trajectory — Erdős #349 (seven episodes, one per theorem)

Verbatim hash-chained event ledgers from `trajectory_export`. Each episode is
independent (own `GENESIS`); regenerate any of them with
`trajectory_export {episode_id: "<id>", allow_putnambench_proof_export: true}`.

## 1. exists_finset_sum_two_pow — episode `844e5846-fc4b-4651-b1dd-9e0735a643ce`

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `1dc0a34f`, max_steps 4) | `b4591ecb6107343ac6b8bd3f954b653d62167d620760387f303809cd2eb0320b` | `GENESIS` |
| 2 | `action_committed` (solve, **accepted**, outcome `kernel_pass`) | `055d8b4771124aa2f5830efda560d09e4b3a18a5e414fb0b97d76bdaac40722a` | `b4591ecb…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `ae4c666fe6acbe098934eae73e122bf08d68d3d04a2f17eae175da2fb4ed1adf` | `055d8b47…` |

- `statement_hash`: `2328323a2b3bbeba5fa2318fbc84fd47675231f738edc38166e21687ced920ed`
- `obligation_id`: `0e3d09db-f8e9-4c11-a9d3-20358820cb87`
- timestamps: created 2026-07-07T04:54:47Z, committed 2026-07-07T04:55:59Z (one attempt, ~72s)

## 2. int_coeff_ge_two_not_isGoodPair — episode `f447f17e-18d7-48fd-b1ef-1ee8aa7bb9c8`

Fresh episode after a *prior* episode (`5ee35ac2…`) hit `budget_exhausted` on
an indentation-consistency bug in `raw_lean_block` mode — see
[../evidence.md](../evidence.md) for the format note. That failed episode's
ledger is not reproduced here (it proved nothing); this is the episode that
actually reached `kernel_verified`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `ae483dd8…`, max_steps 4) | `bd7d22c4d1efbcb797fe41ab470d4c116e61306576cde1401c22c4c8843fb50b` | `GENESIS` |
| 2 | `action_committed` (solve, **accepted**, outcome `kernel_pass`) | `e0821e25c6ce9b347fffd7e17d2c097d756fc2851c96978861173a12f24b9a6d` | `bd7d22c4…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `8d686c48ed0b76e61a15ba64aacf8d29a2dd2d15572d2a77fddc07f71842ca3d` | `e0821e25…` |

- `statement_hash`: `444d78b6081aa380d9260f96fb8501f05347817736672fdc2f0a9a08f769747f`
- `obligation_id`: `4ee3ec40-3bbe-49a5-b613-4af9f2d581ca`
- timestamps: created 2026-07-07T05:26:22Z, committed 2026-07-07T05:27:20Z (one attempt on this episode)

## 3. alpha_le_one_not_isGoodPair — episode `6766c89d-7840-4d11-9fa6-fb7495f12435`

Fifth episode created for this theorem after four `parse_error` rejections
across earlier episodes while root-causing a `problem_create` import-manifest
bug (see [../evidence.md](../evidence.md)) — none of those earlier episodes
reached a valid proof attempt, so none are reproduced here.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `231ba8c9…`, max_steps 4) | `1e1a271d94312611809977d16d784cf37b80d48d253330f922a86eef48a0a16a` | `GENESIS` |
| 2 | `action_committed` (solve, **accepted**, outcome `kernel_pass`) | `28a3492ab44f3404d4e051336c8feddefc641f29f0614749d9d32c77c0968a95` | `1e1a271d…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `a59085206e804b182e12ac3df2786bfe953e8efebc1538428028645a7d8c1717` | `28a3492a…` |

- `statement_hash`: `b2eb28f162b568bbe4bc83534248463d1efab3ae807e13866c0eaa8d36f55d21`
- `obligation_id`: `32d877a3-26b2-4238-b921-fcfeca2bacf0`
- timestamps: created 2026-07-07T05:58:26Z, committed 2026-07-07T05:59:17Z (one attempt on this episode)

## 4. one_two_isGoodPair — episode `0d2fa763-6adc-4a4d-bd4d-e3626bad712a`

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `1d834834…`, max_steps 4) | `93a34f732f4fcbf7dc3c0268d537d3aef43a6f9ec0f60494520c7a636d83f986` | `GENESIS` |
| 2 | `action_committed` (solve, **accepted**, outcome `kernel_pass`) | `d6a738595ab1a37270beb00c1be6087bb3701cf666fd6e1a44cd06985b2a3f44` | `93a34f73…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `f9ebd90b11b1431c6cd4056cac63f8d39d198a4cf4af4b3ff7f16076e2a31e77` | `d6a73859…` |

- `statement_hash`: `ec9344f81572cf51336326d49a224e0abeae96f161623ba088c4c31008064737`
- `obligation_id`: `6137205d-8849-4064-b57a-a7c1cb850420`
- timestamps: created 2026-07-07T06:01:54Z, committed 2026-07-07T06:02:40Z (one attempt, pass@1)

## 5. dyadic_two_isGoodPair — episode `130631aa-4deb-4040-bc6d-f72c6468d833`

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `40f8a013…`, max_steps 4) | `1abbcfc07ea4b800754146dad19829db5d5a7ebc7a9d9ac80482c0e782c469c8` | `GENESIS` |
| 2 | `action_committed` (solve, **accepted**, outcome `kernel_pass`) | `100cc663c130e3ad71179bab7eedc63fcae82db806a919f082c5e7d8a7606c4c` | `1abbcfc0…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `2d12a09db1073b9690c162fc1f96b3615b253afac94e140e26743344d51e5da7` | `100cc663…` |

- `statement_hash`: `32303ccb359f6f8007e88d6f58e40aefd4c2adc26068ce356db81cc1cd4ae28c`
- `obligation_id`: `16a29884-1a4b-4fae-851f-6650dd109e0f`
- timestamps: created 2026-07-07T06:04:32Z, committed 2026-07-07T06:05:17Z (one attempt, pass@1)

## 6. alpha_gt_two_not_isGoodPair — episode `6c0babf6-d577-4847-a2a5-08d2318b97e5`

Dedicated follow-up episode for the previously deferred growth-gap argument.
The first two tracked attempts failed on namespace qualification, not on the
mathematical route: attempt 1 left `Tendsto` and filter tendsto lemmas
unqualified; attempt 2 fixed those but still left `atTop` unqualified. Attempt
3 qualified `Filter.atTop` as well and reached `kernel_verified`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `729145be…`, max_steps 8) | `f29fa7b85798c1d38500909af62d106a20730de02b88dc89414c23b1336e7350` | `GENESIS` |
| 2 | `action_committed` (solve, rejected, outcome `kernel_fail`) | `5f1d15bc0721c767f065e284bdb071d65773f9f21cbf662cd0cc47b7e17e914b` | `f29fa7b8…` |
| 3 | `action_committed` (solve, rejected, outcome `kernel_fail`) | `2b06513fe4492b6193fe876d4aab8312d9884ce1222c8481800f2875233e5413` | `5f1d15bc…` |
| 4 | `action_committed` (solve, **accepted**, outcome `kernel_pass`) | `9d0d52bcb6377cb8ecfe9a4b0f0812e4f65bee89bf31ac586ef7b45b6542da3f` | `2b06513f…` |
| 5 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `b897322a441a451e8282282da1f599cb92ceedec00b3fb0074ed9c3d1d623279` | `9d0d52bc…` |

- `statement_hash`: `cbf2b02039d244db72f164690842335875e1735b8b459b78cdfe9fcd7da2d7b1`
- `obligation_id`: `3f924d3b-a0c3-4e81-9cb8-3e90cffd647b`
- timestamps: created 2026-07-07T06:27:47Z, verified 2026-07-07T06:33:13Z (pass@3)

## 7. integer_isGoodPair_iff — episode `4f28677b-09ba-442a-8543-33e49e021e35`

The culminating assembly. First attempt, no format issues.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `c0c9276f…`, max_steps 6) | `765c8d77742cbd51bc9fc74855128deca5a63100f9eaf30edd6c947c5a3d8256` | `GENESIS` |
| 2 | `action_committed` (solve, **accepted**, outcome `kernel_pass`) | `e1c1f90f05c18ba6d103ced421d9aabf2f3716d038039f6cc2fc342c1002c00e` | `765c8d77…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `6ce1c95fe903701bb7f5e1bd29453e787d4aafbe2c1f30739d805fe0b85d779b` | `e1c1f90f…` |

- `statement_hash`: `a020861a71336e9406c8ce201d23d2082dcd0880fefecb2f018c80ffade1522b`
- `obligation_id`: `bdd8c017-7a9e-4faf-bad8-820745a71448`
- timestamps: created 2026-07-07T06:55:46Z, committed 2026-07-07T06:59:12Z (one attempt, pass@1)

All seven share `lean_environment_hash` `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`.
