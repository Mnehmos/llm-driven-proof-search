# Trajectory — Milestone 1 (episode `1f3255d1-62b9-4105-bca4-3da2290d5858`)

Verbatim hash-chained event ledger from `trajectory_export` (2026-07-17). Full
proof body is
[`../proof/Milestone1_GaussianAntiConcentration.lean`](../proof/Milestone1_GaussianAntiConcentration.lean)
(exported assembled module — exactly what the verifier checked).

Regenerate raw JSON with:
`trajectory_export {episode_id: "1f3255d1-62b9-4105-bca4-3da2290d5858"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `d2f3e8c3`, max_steps 6) | `07302c19284a4e555172d55b085737e771fd157bfb892621634adecd2922f291` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, outcome `kernel_pass`) | `f9e41b6a46a50bb7cfdb72d9e09f202742708530e7cd526b9b02dbe5a9104ae5` | `07302c19…` |
| 3 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `75b7e396261f12a49d53448a083023530ce0fd36b329d943bc394eab1f9650a6` | `f9e41b6a…` |

Event-2 integrity fields (verbatim):

- `statement_hash`: `762c7306e47c38d97b8f925538ad47159750c1ca8c7411fb70af3c026d59699b`
- `module_source_hash`: `fc13e724ac9c50d73d6ae85ac4313b0f32575827a70593f9d19bad6d0c6e3936`
- `declaration_manifest_hash`: `03c802bc07e266a4ac2e4a8c21f6792fd91c986ae899c6370191b6e1b1009644`
- `lean_environment_hash`: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- `obligation_id`: `6f9d907c-22bb-4631-b97a-80bceb89c73c`
- `problem_version_id`: `d2f3e8c3-4b2b-4570-981d-2f0c01d76883`
- reward: `kernel_pass` +5000, `root_kernel_verified` +20000, `step_penalty` -100 (1 step total)
- one submission, pass@1, no repair steps needed — every one of the 18
  Mathlib declaration names used had been pre-checked via
  `lean_declaration_lookup` before submitting (see whitepaper.md)
- fidelity: `attested` (`unsafe_dev_attestation=true`) — honest dev-mode
  labeling; outcome caps at `kernel_verified`, never `certified`

---

# Trajectory — Milestone 1a.1 (episode `e4c031ff-c334-49b5-8e2b-0c2ec5102c3f`)

Finite-family Gaussian anti-concentration (union bound). Full proof body:
[`../proof/Milestone1a_FiniteFamilyAntiConcentration.lean`](../proof/Milestone1a_FiniteFamilyAntiConcentration.lean).

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `46bd7c1a`, max_steps 6) | `1821ac411c9b5b945ffab116611fb780cc136d8a796ef1e3d1399de1d3c74cfe` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `96930c1908aa81037418571799bc6e383f204dbca2761b9d91bd8cf6a03ea9a5` | `1821ac41…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `542f721279e5b2440ff167c4e75a3b6cdf01087c1719fbd54bb74f541aa59eaa` | `96930c19…` |

Event-2 integrity: statement_hash `cd45ebe4f8ada258bbdf14bc6d845f4314aee77eec1cb2ce7c2004117df8d07b`,
module_source_hash `c1ac7485dd051dcf97f3fc53405cb3e90cdfa4d04b06d5deef35a7a0f9b04a79`,
declaration_manifest_hash `74e7dd05673f738dcc38a503ed218a2cb2624f33180ccfe39635e5999c05e142`,
obligation_id `976dd894-3879-4935-a1fa-33586b7cf2c4`. pass@1, one submission.

# Trajectory — Milestone 1a.2 (episode `e04f96ea-0d23-42ca-9349-65db3e91d339`)

Homogeneous k-coefficient corollary.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `c1e88e47`, max_steps 6) | `39a8b8f1567ef793beb80e1f8e6b0c169f153714e94d916ea2924007a9e046a0` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `831cce6c738e965d8fee9bf8de58fd0fe5c99173cca200d32c33c81613f50e00` | `39a8b8f1…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `492c1f14726d814315b1afc03c6a76786b826f53ab317367ae7d4f49da1bd06e` | `831cce6c…` |

Event-2 integrity: statement_hash `d3f497b58d0a79fe46bcf66f6a6bc7716726a78eec54083fa904e9a0605027aa`,
module_source_hash `be142854cf8723614c066439f4b5a9e62efc75f0a3b930bb6bd9f41136935ebf`,
declaration_manifest_hash `ec5f3f2125f670e41af25efd2ac082e03772acab61d2b5546d1345fe515525f4`,
obligation_id `63a7f1fc-c2c1-4894-9301-f6b243ab5bd4`. pass@1, one submission.

Both M1a episodes: fidelity `attested`; standalone `lake env lean` of the
canonical snapshot exits 0; `#print axioms` on all roots =
`[propext, Classical.choice, Quot.sound]`.

# Trajectory — Milestone 2.0 (episode `851ff2ce-de85-4164-a274-024f4f2bcac3`)

Distance from a Gaussian-perturbed vector to a fixed hyperplane. Full proof body:
[`../proof/Milestone2_0_HyperplaneAntiConcentration.lean`](../proof/Milestone2_0_HyperplaneAntiConcentration.lean).

Regenerate raw JSON with:
`trajectory_export {episode_id: "851ff2ce-de85-4164-a274-024f4f2bcac3"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `ff02637d`, max_steps 6) | `d3dc28799e1762caa2e225b73c59ac0d70d120ab2ccdf59e147a18ab727b4bd2` | `GENESIS` |
| 2 | `action_committed` (submit_module, **rejected**, outcome `kernel_fail`) | `33a0f205f5fd1311a1ac2c2f264bd981b7b3693e160e0f68c10e0e48541ff7c1` | `d3dc2879…` |
| 3 | `action_committed` (submit_module, **accepted**, outcome `kernel_pass`) | `0dc9cc30d12b9d42f5d6e70f2ffa99f15a4dc4a47fb490c43b1de18fe8f30ad3` | `33a0f205…` |
| 4 | `episode_terminated` (outcome `kernel_verified`, reason `root_proved`) | `2723c3fd348584349c6142d29e393b726dfdc5481fab349d65a7c829c4874529` | `0dc9cc30…` |

Event-3 (accepted) integrity fields (verbatim):

- `statement_hash`: `7031dca12c656cb4dbd9602e90746e1f8223fc438f6aebe5ffcf2895d18b19e4`
- `module_source_hash`: `55538342234cf14e98f0f45f5ace408f29b83a665412e991d769ebf39980832a`
- `declaration_manifest_hash`: `dd5b7bbb3e18fec36bd8f79cf4c7d6c4477ca5d07140fabad76e5eb47b3bd7e5`
- `lean_environment_hash`: `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`
- `obligation_id`: `c507ce88-aa33-4d33-b39a-1f60e3c4d52d`
- `problem_version_id`: `ff02637d-bdd8-4989-aff3-70f2decac8ee`
- reward: `kernel_pass` +5000, `root_kernel_verified` +20000, `step_penalty` -100 (×2)
- fidelity `attested` (`unsafe_dev_attestation=true`); standalone `lake env lean` of
  the canonical snapshot exits 0; `#print axioms` = `[propext, Classical.choice, Quot.sound]`

**Repair record (legitimate research data, per the constitution — not pass@1).**
Submission 1 failed `kernel_fail`: the two helper `proof_term`s were sent as multi-line
indented tactic blocks, and the `flat_tactic_sequence` transport re-based them
destructively — `have h : T := by …` continuation lines were parsed as separate
top-level tactics (diagnostics: `unsolved goals ⊢ -(x-m)^2/(2*v) ≤ 0` at the `hnonpos`
have; `unexpected token 'fun'` parse error at a continuation line; `unsolved goals ⊢
v ≠ 0`). The root theorem (sent as `raw_lean_block`) had no diagnostics — the failure
was purely a helper-transport artifact, not a mathematical gap. Fix: helpers rewritten
as single-line semicolon-chained sequences with every inline `by`-block parenthesized
(including `(show … by ring)` inside `rw` lists), re-validated by an exact scratch
`lake env lean` (exit 0) before resubmission. This confirms the campaign's recorded
flatten-trap lesson: **helper proof bodies do not survive `flat_tactic_sequence`
transport as multi-line blocks even without bullets; only the root supports
`raw_lean_block`.**

# Trajectory — Milestone 2.1 (episode `10653478-f63b-4704-8761-cb3cec0cc503`)

Codimension-2 (coordinate-aligned) product anti-concentration. Full proof body (with M2.2):
[`../proof/Milestone2_SubspaceAntiConcentration.lean`](../proof/Milestone2_SubspaceAntiConcentration.lean).

Regenerate raw JSON with:
`trajectory_export {episode_id: "10653478-f63b-4704-8761-cb3cec0cc503"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `c548e3fe`, max_steps 6) | `0525d72d9a328dc15d49e8db09e08bf45b599e6e411cbb4d290ec1ae73358f1d` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `fac2c3854adfcfa52161c1d3411215c3ee51fafe05fab33f748d40671752fadc` | `0525d72d…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `0048efc91f3fce16a938f35d621f6749b5c39a74588c1c6927bc95469f627a6e` | `fac2c385…` |

Event-2 integrity: statement_hash `dd3b81bd871f967c55ffb4fe6f1ac4614313e5aadd888a13a98de8985639bf91`,
module_source_hash `0665a4404c00dd8be0de25322676449b121ad2377687076813172c78d62713d9`,
declaration_manifest_hash `644625cc384a11d81cc66eebcfa02521bf3ea5dc58c7b4b24d9cd55359afbe98`,
obligation_id `d7fd24d1-6aef-40c9-9bc5-4a9cbbef1bde`. pass@1, one submission. Content:
distinct coordinates of `N(center,σ²I)` are independent (covariance `(σ²I) i j = 0`), so the
two-slab probability factorizes into a product of two M1 marginals ⇒ `(2ε/(σ√2π))²`.

# Trajectory — Milestone 2.2 (episode `ea3c53fe-fca3-4764-b89d-26a5d9546654`)

General arbitrary-orientation subspace anti-concentration (MASTER — subsumes M2.0, M2.1).
Full proof body:
[`../proof/Milestone2_SubspaceAntiConcentration.lean`](../proof/Milestone2_SubspaceAntiConcentration.lean).

Regenerate raw JSON with:
`trajectory_export {episode_id: "ea3c53fe-fca3-4764-b89d-26a5d9546654"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `4a4d86dd`, max_steps 6) | `88604648c11a9e183f111247698ff12b61c3451db77e3fed709451b9882238aa` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `ecdce692b6dfc8c9c04f0a87b95e7182cd048b69441237d1009c1cdcb66cdd17` | `88604648…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `817553193546ac643b7af9ed12d3f8a9c4d92badd2b581a80b80c12936ad6fef` | `ecdce692…` |

Event-2 integrity: statement_hash `3ad10c1dd02b569b30d76e57863563a324a708c6d01b7114024bcbc43f99353f`,
module_source_hash `af28f30e3e9cca24203f70eceb6fc78544dbed11ec8643849c43127b0b197587`,
declaration_manifest_hash `bdc8d671461b7688cc6f858d6407e0a46cb947c41d276d06448f56e28e638670`,
obligation_id `cde9e7cc-69fd-4592-b808-66f8883d0b13`. pass@1, one submission.

Both M2.1 and M2.2: fidelity `attested`; standalone `lake env lean` of
`proof/Milestone2_SubspaceAntiConcentration.lean` exits 0; `#print axioms` on both roots =
`[propext, Classical.choice, Quot.sound]`. Mathematical content of M2.2: distinct
projections `⟨u j,·⟩` of an isotropic Gaussian are independent (pairwise covariance
`σ²⟪u i,u j⟫ = 0` by orthonormality), so the joint slab probability factorizes into `k` M1
marginals ⇒ the sharp `(2ε/(σ√2π))^k` codimension gain, for arbitrary subspace orientation.

# Trajectory — Milestone 2-GEOM (episode `d99aa6a8-a43f-4cdc-ab37-a3f6a9e2edbb`)

Rudelson–Vershynin deterministic geometric core. Full proof body:
[`../proof/Milestone2_GEOM_RudelsonVershynin.lean`](../proof/Milestone2_GEOM_RudelsonVershynin.lean).

Regenerate raw JSON with:
`trajectory_export {episode_id: "d99aa6a8-a43f-4cdc-ab37-a3f6a9e2edbb"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `8d13dff9`, max_steps 6) | `20c860f45e244147ae300a9a5e73ade756934d3d07f3cb1e4c62fba469bab0db` | `GENESIS` |
| 2 | `action_committed` (submit_module, **rejected**, `kernel_fail`) | `031ed410de267b0137a386a3ee5181c6c6d6a5ad24a4648a00caeeffffbb7f7d` | `20c860f4…` |
| 3 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `6e57fc53d4e364136f61a2215dec06472c7cfda3bb3d18c595d8333cb8091549` | `031ed410…` |
| 4 | `episode_terminated` (`kernel_verified`, `root_proved`) | `2ace94b67301b093115534648db18f2e689a424d57ddfa8ff7e0878146fa1a04` | `6e57fc53…` |

Event-3 (accepted) integrity: statement_hash
`8588c87e9472e58b75a9b627108a430e3c3d130aeda402feef294eee6df1d73c`,
module_source_hash `efc9983b9d7d35fcb705f6cd227be42d904743c3a633397d6c9cfb090edb96ff`,
declaration_manifest_hash `0f8355f247822668f865521bdd2434c5956a7ba4d6eed72ea57aeba0ebb0f409`,
obligation_id `3034f98b-3396-4d09-99c3-8f7b7e1ce9dc`. Repair: sub 1 kernel_fail — helper
`rcases` case split used `·` bullets, which do not survive `flat_tactic_sequence`; sub 2
pass with a bullet-free sequential chain. fidelity `attested`; standalone `lake env lean`
of the snapshot exits 0; `#print axioms` on both root + helper =
`[propext, Classical.choice, Quot.sound]`. Content: `|x i|·dist(a i, span{a j:j≠i}) ≤
‖∑ x j • a j‖` in any real normed space — the deterministic RV reduction turning
`σ_min = min_{‖x‖=1}‖Ax‖` into column-to-span distances.

# Trajectory — Milestone 2-GEOMσ (episode `56a975eb-e54e-4970-8b7c-6cbb847c1cf4`)

Rudelson–Vershynin σ_min-form deterministic lower bound (per-vector core + coordinate lemma).
Full proof body:
[`../proof/Milestone2_GEOM_RudelsonVershynin.lean`](../proof/Milestone2_GEOM_RudelsonVershynin.lean).

Regenerate raw JSON with:
`trajectory_export {episode_id: "56a975eb-e54e-4970-8b7c-6cbb847c1cf4"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `ca8e0109`, max_steps 6) | `c37076b4858ec45881d73cb4748ffec4fd97e11be761b8b654d983eb36a397be` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `20d1a4e71532390255bd6ecfad85cc0aa2d58eb72874be2609178b5a337aa87e` | `c37076b4…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `a24cbe2f96f6e361cfeef4e653377159e3381326fe1d68b4f9653e1b4bffe31d` | `20d1a4e7…` |

Event-2 integrity: statement_hash
`aeb92904ec37fe962008250514a266503995e3603e0c2fda29007cbcf5aae402`,
module_source_hash `99626e77d3bed3a0cd20a87389428286f413f8bb9c52a7bee45f8c912ada79c7`,
declaration_manifest_hash `180ab619cdc471ab35d6d6842a9b70021b77b9ac332e3c6a94ce1eb4efa9f182`,
obligation_id `8a70580a-1569-4ed7-90d4-ebafa5707c30`. pass@1, one submission (empty
`module_items`, fully-inlined `raw_lean_block` root — avoids all helper-flattening).
fidelity `attested`; standalone `lake env lean` of the snapshot exits 0; `#print axioms`
on all four snapshot theorems = `[propext, Classical.choice, Quot.sound]`. Content:
`(min_i dist(a i, span{a j:j≠i}))·‖x‖ ≤ √n·‖∑ x j • a j‖` — the full deterministic RV lower
bound; over unit `x` gives `σ_min(A) ≥ n^{-1/2}·min_i dist(A_i, span of other columns)`.

# Trajectory — Milestone 2-DEF (episode `9bdee270-3333-4e6f-995d-9489ff936ce8`)

σ_min definition (unit-sphere infimum) + the Rudelson–Vershynin σ_min lower bound. Full proof
body: [`../proof/Milestone2_DEF_SigmaMinLowerBound.lean`](../proof/Milestone2_DEF_SigmaMinLowerBound.lean).

Regenerate raw JSON with:
`trajectory_export {episode_id: "9bdee270-3333-4e6f-995d-9489ff936ce8"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `73ac63c1`, max_steps 6) | `dfd4ad23ba88b53a1f413e84dcec430e1539a4d4c96a315af69652454c91c0b0` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `f27d308fa23c69acda0c8dd3bcf81c9533157f4345b3fa3e4ab18fa80e461f43` | `dfd4ad23…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `3645cfb5aa69823a59e06339a0e256abb6d79a473f885afffc5be1fcd758caba` | `f27d308f…` |

Event-2 integrity: statement_hash
`f3cb5ad111fcc7696095b2115a017e7d33c58816d00359d9ee8e2044c9462c27`,
module_source_hash `0e684f2c57b6e24a513a39133a8a85900fb464b2a4732869aa6305e0d087e46d`,
declaration_manifest_hash `35c70e3a07353010b40e87841fabb0846bba0092456c05fb5428256ae08ee2fc`,
obligation_id `0e22db28-f3c5-4198-85a7-099f0761f7f4`. pass@1, one submission (empty
`module_items`; σ_min inlined as `⨅` in the statement; RV chain inlined in the root). Content:
`σ_min(cols) := ⨅_{‖x‖=1} ‖∑ x_j a_j‖ ≥ n^{-1/2}·min_i dist(a i, span of other columns)` — the
Rudelson–Vershynin σ_min lower bound. Completes the deterministic half of the σ_min ladder;
the remaining edge is the probabilistic M2-COND (conditioning + M2.2) then M2-UNION.

---

# Trajectory — Milestone 2-COND conditional (episode `b15cd230-3d17-4c8a-be21-0ce0f7d18636`)

Distance-to-fixed-subspace tail bound (conditional piece of M2-COND). Full proof body:
[`../proof/Milestone2_COND_ConditionalDistBound.lean`](../proof/Milestone2_COND_ConditionalDistBound.lean).

Regenerate raw JSON with:
`trajectory_export {episode_id: "b15cd230-3d17-4c8a-be21-0ce0f7d18636"}`.

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `337087ce`, max_steps 6) | `9b5cac8301a6bc4c6347a831b51ffa0fbbe05060b3cf3c0da332ccd9467aa7e3` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `3a62a5f9b120d9343667d6650e487037876b4e1c24149e8d85011889f5313215` | `9b5cac83…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `3216a5731d2fc78ad2cbbfb9a16b761e1eaf6f92ca032c81eceb45720700e5b7` | `3a62a5f9…` |

Event-2 integrity: statement_hash
`60ecff763acfc53a482ed79471122e5a8c19f0b065bfef77da63640b21c84c94`,
module_source_hash `f07c20ce63af1abfd5f1f7a5f3d3aa46838386a737290c859bdcf78c135d702b`,
declaration_manifest_hash `c28b25389ff59cf685d54c31c67b4e7346116da7fdf7207f761e1f9b686d04f4`,
obligation_id `30e3b2f2-b124-4b86-9d3f-1a2e23f9bee2`. pass@1, one submission (empty
`module_items`; M1/M2.0/geometric lemma inlined in the root). Content:
`P(dist(x, W) ≤ ε) ≤ 2ε/(σ√2π)` for a fixed subspace `W` with unit normal `u ⊥ W`, via
`Metric.infDist` — the per-ω conditional bound the σ_min conditioning step needs.

---

# Trajectory — Milestone 2-COND step 3a (episode `a95d1c04-1679-47ab-a799-671424348482`)

Matrix-Gaussian column independence. Full proof body:
[`../proof/Milestone2_COND_ColumnIndependence.lean`](../proof/Milestone2_COND_ColumnIndependence.lean).

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `88cc675f`, max_steps 6) | `6a0f9f03c6f9506997232c676d91fd716147b8e7daeaa7e18ebd37a35aaf18a9` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `c28bad71db3d74b13016e8bc7090f66c300dc630fd40fd5195fef5493f29aab8` | `6a0f9f03…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `e282a44f1b8d00c738bd6ce84dc10bb1a723138242d0f20c6e7a59373b1e2620` | `c28bad71…` |

Event-2 integrity: statement_hash
`04c6e1447e5ea23c8c4f81e0240bcfa4b6301974a45d4b64f18fe1d4df4dae5f`,
module_source_hash `7e9f739f96807c453943c195a1d67e0729aae0c46bf6fbcdf9f2bc662621d0e7`,
declaration_manifest_hash `f08831a2d6bc74d1076f8d7ab25ff15f9eea24bf44fae85e4b56dc0ed52e2107`,
obligation_id `537fda0d-28f7-4566-b7cb-baef6af69073`. pass@1, one submission. Content: under
`Measure.pi` over columns, the column-evals `ω ↦ ω j` are `iIndepFun` (matrix-Gaussian column
independence) — M2-COND step 3a.

---

# Trajectory — Milestone 2-COND step 3c (episode `3a68c3c7-c2c1-49a0-a55f-f9f594059fd4`)

Fubini conditioning glue. Full proof body:
[`../proof/Milestone2_COND_FubiniGlue.lean`](../proof/Milestone2_COND_FubiniGlue.lean).

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `7cf633b2`, max_steps 6) | `24b3acd4f9130f149322ff08d44f9945cceab635ef6ea93b1143c958097f6a60` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `1eeb6891f1ac800f7e195d98bcf825431a61439b7dc0908fe97351eec5730712` | `24b3acd4…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `4390f689cb5c17a3a430bb0aa697a48eaa4eeb3c807542c631f18df587588923` | `1eeb6891…` |

Event-2 integrity: statement_hash
`14052aff1d4cf64aca08beac994dc8b53cdb37bc9bf5344222d1221ff5050acc`,
module_source_hash `c825c05f34cf840342be550b76f70885e99cf4d97c2e60aba00a51aae58cf897`,
declaration_manifest_hash `6026c80371dc0bc67373adaa48b2525703d21e5b0e680a541be1df5167cf03ff`,
obligation_id `5e64704f-329d-4c1e-a7bb-129e7a43c6f4`. pass@1, one submission. First campaign
use of an `open MeasureTheory` manifest directive. Content: all conditional slices ≤ c ⇒
product measure ≤ c (M2-COND Fubini glue).

---

# Trajectory — Milestone 2-COND step 3b core (episode `6216166d-5194-4278-95a5-cfdc41c13d46`)

Adjugate-row normal orthogonality (general-`n` cross product). Full proof body:
[`../proof/Milestone2_COND_AdjugateNormal.lean`](../proof/Milestone2_COND_AdjugateNormal.lean).

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `4f595606`, max_steps 6) | `050647e76a819b0ddd229cdf08f8878f411468f26f3ecdf66aa1fc3d924198f9` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `3e39d8a504899d8f775212b4a3890ee9f1f704cfb3dcf62d0157ea9fc7a952ba` | `050647e7…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `e50336b76cebc33ff0b66150efbad51c217cfefe7ba9284b6b619504743ebb47` | `3e39d8a5…` |

Event-2 integrity: statement_hash
`bfd1a6427e74c0b07afe722b83fe50b8c6f770e63a7101f0c0e7e09101512b9b`,
module_source_hash `05d092a0e3867c3b90d59fe7aec7cc80238a0a39a2d1f162c8087193a21bc51d`,
declaration_manifest_hash `e712b020ec7a9a51437984e3480cb38e4fb557940a19643e16620c8a0924e73f`,
obligation_id `1edf9680-ca39-49b0-ba55-020b181eb091`. pass@1, one submission. Content: the
`i`-th row of `adjugate A` is orthogonal to every column `j ≠ i` — the general-`n`
cross-product normal (Mathlib's `crossProduct` is `Fin 3` only), polynomial hence measurable.

---

# Trajectory — Milestone 2-COND step 3b measurability (episode `1aa443a1-fdc9-4f59-b38d-cd281eee6b12`)

Adjugate-row normal map continuity. Snapshot (with 3b-core):
[`../proof/Milestone2_COND_AdjugateNormal.lean`](../proof/Milestone2_COND_AdjugateNormal.lean).

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `beafa0cb`, max_steps 6) | `82e21e0cd2a4b5c0f953e3224260dfb4d05bbf7888936f7e53c1ddfba4aa4cab` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `77c482d558b0a6d35e49bc74d1cb47a6758767c161c6fa7a2aecacb34d4d5f9c` | `82e21e0c…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `b660c00527c30eae8b7f787f24171351a81bba14fe2b5479f2e0f46d611d74ea` | `77c482d5…` |

Event-2 integrity: statement_hash
`37cde840869ef43b865ed14989e9c028fae85a103bd24412bb8f7e1fde1d8e9c`,
module_source_hash `90eb3a84170187f6a1f563925caf6f32cabdda307b96d5d966ce60724f67f7fb`,
declaration_manifest_hash `f991e50614ecede92c30afb9b36bdd5e6f4c0bd56fb3aca8a75885833eeea6ce`,
obligation_id `a5092ba3-3d8c-4601-875d-c414cf8ab261`. pass@1. Content: `A ↦ adjugate A i` is
continuous (via `Matrix.continuous_det` + `fun_prop`), hence measurable — the measurable normal.

---

# Trajectory — Milestone 2-COND step 3b (nonzero normal) (episode `4af0617a-ffd5-4c23-901c-bb909936dce0`)

`det A ≠ 0 ⇒ adjugate A i ≠ 0`. Snapshot (with 3b-core, 3b-meas):
[`../proof/Milestone2_COND_AdjugateNormal.lean`](../proof/Milestone2_COND_AdjugateNormal.lean).

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `8624ced9`, max_steps 6) | `542b458247dba0a349f0d4ee968157c6f4a991ff42b5b1c06039781ac9e3f9f2` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `98c306ab2453e704ae7c8f36f091a628a897feea761bf170554ca1d507ee6ace` | `542b4582…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `5f4f71780c89f5b6c6f9793b74fd3f4cc081afa938679bb15959eb57d9196316` | `98c306ab…` |

Event-2 integrity: statement_hash
`969a5b76a408457ba99fb2219938986fff161e9005c174168ec4dbcfe8e08a77`,
module_source_hash `6fc359564bc458916c1ff2a6c8eba1f074278d93a633352e6973d8f3a6cd28c2`,
declaration_manifest_hash `2e191a4e92f4e29450e79e18f9a174c8381e2e533701a7ed387eeda93cfc2c8d`,
obligation_id `7435b839-dc21-49e1-957c-42fd1f7b9357`. pass@1. Content: from
`(adjugate A * A) i i = det A ≠ 0`, the `i`-th adjugate row cannot be zero — a nonzero normal
wherever `A` is nonsingular (a.s. under the Gaussian).

---

# Trajectory — Milestone 2-COND step 3b (hyperplane null) (episode `ba309a56-f0a4-4a4e-a258-bcac90018883`)

A fixed Gaussian hyperplane is measure-zero. Snapshot:
[`../proof/Milestone2_COND_HyperplaneNull.lean`](../proof/Milestone2_COND_HyperplaneNull.lean).

| # | event | event_hash | previous_event_hash |
|---|-------|-----------|---------------------|
| 1 | `episode_created` (problem_version `c2a131a2`, max_steps 6) | `d95bd7e30d653f480f2b35554708bd5ea65d04c8d51ba93973939af9f36fd823` | `GENESIS` |
| 2 | `action_committed` (submit_module, **accepted**, `kernel_pass`) | `69bfccdf1f9a25661ab8f32771b9861db600b65b9b5af6cd6faf696db9d836aa` | `d95bd7e3…` |
| 3 | `episode_terminated` (`kernel_verified`, `root_proved`) | `0de031710d45f37a68bceb1fda0b48449b19b1020a2a0cb97a0b8520e7ea368e` | `69bfccdf…` |

Event-2 integrity: statement_hash
`f7011700ef84a4de44602a8b75f2010087e3d8391d9d24bbcac2f04854901d64`,
module_source_hash `205a0a519152a3c4dabb7b09e3c7359f7d089bfed56c1f1fa44fc9c3c436dd1d`,
declaration_manifest_hash `1d67bd4e7a2e1d3f3435464ebd2d87c3846063722d19de1a899fe9440e87e54b`,
obligation_id `50d84fb5-8165-4c73-96ac-a6907cb4b926`. pass@1. Content: `P(⟨u,x⟩ = t) = 0` for
unit `u`, via `ε→0` in the M2.0 small-ball bound — the elementary a.s.-nonsingularity route
that avoids the missing analytic-zero-set theorem.

---

## Session summary (12 new kernel-verified milestones this cycle)

M2.1 (`10653478`), M2.2 (`ea3c53fe`), M2-GEOM (`d99aa6a8`), M2-GEOMσ (`56a975eb`), M2-DEF
(`9bdee270`), M2-COND-conditional (`b15cd230`), M2-COND-3a (`a95d1c04`), M2-COND-3c
(`3a68c3c7`), M2-COND-3b-core (`6216166d`), M2-COND-3b-meas (`1aa443a1`), M2-COND-3b-nz
(`4af0617a`), M2-COND-3b-hyp0 (`ba309a56`) — the complete distance-to-subspace tower, the entire
deterministic σ_min lower bound `σ_min ≥ n^{-1/2}·min_i dist`, the conditional
distance-to-fixed-subspace tail bound, the product-measure column-independence, the Fubini
conditioning glue, the general-`n` adjugate-row cross-product normal (orthogonality +
continuity/measurability + nonzero-when-`det≠0`), AND the fixed-Gaussian-hyperplane-is-null lemma
(the elementary a.s.-nonsingularity route, avoiding the missing analytic-zero-set theorem).
Hash-chain verified per episode above; all roots `#print axioms = [propext, Classical.choice,
Quot.sound]`; all snapshots `lake env lean` exit 0. The root problem R1 remains OPEN and not yet
Lean-expressible; no terminal RESOLUTION claimed. Of the σ_min lower-tail, CONDc + 3a +
3b-core/meas/nz/hyp0 + 3c are done; what remains is the routine assembly (a.s.-nonsingularity
from hyp0 + conditioning, unit-normalization, measurable-event assembly) and the M2-UNION reuse.

# Trajectory — 2026 literature correction and Tier-3 lower-bound bridge

The campaign reopened the primary-literature audit rather than accepting the
recorded 2025 frontier. This found Bach–Huiberts arXiv:2504.04197v2 (revised
2026-05-23): upper bound `O(σ^{-1/2}d^{11/4}log(m)^{7/4})` and Theorem 57's
high-probability all-objective combinatorial-diameter lower bound. The STOC 2026
paper by Bach–Black–Kafer–Huiberts explicitly says the lower bound applies to all
pivot rules. This invalidates the previous ledger claim that no universal lower
bound was known.

Derived the fixed-`d=2` global-norm transfer: with literature noise `τ`,
`M=⌊(4/τ)^2⌋`, scale `α=(2M)^{-1/2}`, and SolveAll noise `σ=ατ=Θ(τ²)`. The center
then has stacked norm one and the feasible polytope is unchanged. The diameter
lower bound becomes `Ω(σ^{-1/4}log(1/σ)^{-1/4})`, while the proposed upper bound is
only a fixed power of `log(M/σ)=O(log(1/σ))`.

Lean-checked the objective-noise bridge in
`Tier3_AntipodalLowerBoundReduction.lean`: the literal-specification loophole
`oracle_initialization_gives_zero_pivots`, `antipodal_pivot_sum_ge`,
`antipodal_one_run_ge_half`, `symmetric_lintegral_pair_lower_bound`, and
`polylog_with_quarter_isLittleO_quarterPower`, followed by the rescaling lemmas
`scaled_noise_between_quadratic_bounds` and
`half_le_natFloor_and_natFloor_le`. First
compile exposed only a parser issue with the `ℝ≥0∞` notation in a binder; replacing
it with `ENNReal` produced standalone exit 0. Axioms: `[propext, Quot.sound]` for
the combinatorial roots; the standard three for the integration root. Source hash
`e288317e78c09fca80c7cf02a7129b1bda3c2ea7c4f735f6e04c1fc1027e7b40`.

Root lesson: the page is a specification fork. Objective-independent Phase I gives
a disproof of the displayed polylogarithmic-noise bound; unrestricted uncharged
initialization gives a trivial zero-pivot rule. The general exact-order question
remains open after model repair.

# Trajectory — Tier-3 deterministic Bach–Huiberts geometry

Continued beyond the short antipodal reduction into the published proof of
Theorem 57. Added `Tier3_BachHuibertsRoundness.lean` and Lean-checked the complete
near-ball sandwich of Lemma 55, including arbitrary inner-product-space
generality. The same module proves the reciprocal polar radii, the
minimum-norm-point estimate `‖v-y‖≤√(14η)`, and the pairwise polar-facet bound
`‖v-w‖≤2√(14η)`.

The module also isolates and verifies the metric/combinatorial numerical core
of Lemma 56: a short-link chain telescopes, the maximizing/minimizing endpoint
accounting adds exactly three `γ` terms, and the resulting inequality yields
`q(2/(Rγ)-3)≤k`. It now also proves the adjacent-basis block-overlap fact:
fewer than `d` one-index exchanges cannot remove every index from a `d`-element
basis. This moves the formalization wall to the basis-to-polar-facet and
objective-ray incidence layer, followed by the dense-net and Gaussian-tail
assembly.

Standalone compile: exit 0 in Lean `v4.32.0-rc1`, Mathlib `360da6fa`; all
printed roots use `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
Source hash:
`050e05ed1c06780f605a4a0f6203ca086868529fe3fb2cefc075b98f85690951`.
Evidence label: `lean_checked` (no tracked proof-service episode in this session).

# Trajectory — Tier-3 polar, net, and Gaussian closure

Extended the lower-bound import along three independent edges. First, completed
the abstract basis-path form of Lemma 56 in `Tier3_BachHuibertsRoundness.lean`.
Second, added `Tier3_PolarIncidence.lean`: active constraint normals and normalized
objective rays now inhabit the relevant polar exposed faces; polar bodies/faces are
closed and convex; the Hilbert projection theorem supplies the paper's minimum-norm
face point and first-order inequality; and primal ball inclusions reverse to the
required reciprocal polar ball inclusions. Third, added `Tier3_SphereNet.lean` and
`Tier3_GaussianTail.lean`, checking Lemma 54 and the simultaneous finite-row
Gaussian norm-tail interface from exact coordinate laws.

Clean four-file audit: exit 0 for all files, 51 printed roots total, only the
standard axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Current
hashes are recorded in `state.md` and `evidence.md`. The wall has moved to concrete
simple-polytope/basis and genericity instantiation, explicit parameter substitution,
and final Theorem 57 assembly—not the dense net, polar incidence, minimum-point, or
Gaussian tail components themselves.

Then specialized the Gaussian event to the paper's threshold. Lean now proves
`2·exp(-(4σ√log n)²/(2σ²))=2/n⁸` and the resulting simultaneous row failure
bound `2·rows·dim/n⁸`. The current Gaussian module has 288 lines, 13 roots, and
SHA-256 `f7a05056535e0c0738b5bbea010172f5e302fd77469ca748ab8cb64165ee7591`.

# Trajectory — concrete vertex bases and genericity induction

Closed the deterministic simple-polytope/basis gap at the reusable theorem level.
`Tier3_NormalizedLPBasis.lean` now models normalized feasible bases and their
one-index exchanges. `Tier3_VertexActiveBasis.lean` proves, from Mathlib's actual
`extremePoints`, that active normals span the ambient space; under the affine-GP
nondegeneracy consequence, the whole active set has exactly `d` elements and is
linearly independent. `Tier3_AffineGenericity.lean` proves that consequence for
augmented rows and shows positive normalization preserves it.

On the probability side, `Tier3_GenericityProbability.lean` now iterates the
absolutely-continuous snoc step through an independent product law, specializes it
to Euclidean volume, and intersects the fixed-subset a.e. statements over the finite
subset family. Roundness gained the explicit `d=2` final constant, and PolarIncidence
now derives exposed-face diameter directly from the ball sandwich.

Fresh six-file audit: exit 0, 63 roots, only `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`. The remaining wall is exact joint-Gaussian law
instantiation, charged-edge/basis-path wiring, event assembly, and the repaired
initialization semantics.

Then replaced the separate-subset-law interface by an exact joint-product theorem.
The new proof inducts on `Measure.pi`, reindexes from `Fin n` to arbitrary finite
index types, uses Mathlib's projective product family to identify every subset
marginal, and performs the finite a.e. intersection. One joint collection of
absolutely continuous rows is now simultaneously in linear general position on all
small subsets. The updated module has 336 lines, 13 roots, SHA-256
`a7ef5947ec66665290bea121aa73b2787ba2cb2534352dce872d536b8b243b61`, and compiles
with only the standard three axioms.

Finally assembled the generic theorem with the exact translated/scaled Gaussian
row law in `Tier3_GaussianAffineGenericityAssembly.lean`. The resulting root states
simultaneous a.s. linear independence of every augmented-row subset of size at most
`d+1` under one joint smoothing sample. This removes the remaining probability-law
genericity caveat; the next wall is algorithmic edge/basis-path wiring and event assembly.

Then removed the infinite-chain artifact from the deterministic capstone. Bounded
overlap lemmas now use only an actual finite path through time `k`; the normalized
simplex path exposes exactly those bounded basis-cardinality/exchange facts; and
`Tier3_FinitePathLowerBoundAssembly.lean` maps the concrete charged path directly to
the Bach--Huiberts pivot lower bound. The next semantic edge is integration of this
execution object with `T_R` and an objective-independent initializer, not basis-path wiring.

Added that semantic repair next. `ObjectiveIndependentPivotRule.init` receives only
constraint data; `ChargedExecution` records every paid transition; Lean proves its
length is exactly the existing Tier-2 `pivotCount`, and two objectives on the same
constraints start identically. The remaining semantic work is now a wrapper combining
this execution record with the concrete normalized basis path, not a definition gap.

Closed that wrapper immediately afterward. `NormalizedChargedExecution` aligns the
repaired run states with the normalized bases, and its capstone theorem rewrites the
finite-path Bach--Huiberts bound directly onto Tier-2 `pivotCount`. The only remaining
Theorem 57 assembly edge is now the high-probability good-event/parameter conjunction.

Closed that probability edge next. `Tier3_GoodEventAssembly.lean` proves that an a.s.
genericity condition costs no probability when intersected with a quantitative tail
event. `Tier3_BachHuibertsD2Parameters.lean` checks both `d=2` thresholds and the
`6n/n⁸ ≤ n⁻²` arithmetic. `Tier3_D2TailGenericityAssembly.lean` combines them, and
`Tier3_ExactGaussianD2Assembly.lean` derives every marginal from the very same exact
product of translated/scaled augmented-row Gaussian laws on which simultaneous affine
general position holds. The final root has failure probability at most `n⁻²`, compiles
with only the standard three axioms.

The proof-service became available after that local audit. Four root-resolution
companions were then replayed through tracked episodes and reached `kernel_verified`:
the unrestricted optimal initializer (`4edec869…`), antipodal lintegral bridge
(`83e2e9ea…`), global-unit-ball rescaling (`3548c3b0…`), and quarter-power versus
polylog separation (`39baac00…`). This upgrades the two semantic branches and the
asymptotic contradiction spine from local checks to tracked kernel evidence; the
large exact-product event assembly remains honestly labeled `lean_checked`.

Closed the deterministic wrapper immediately afterward.
`theorem57_deterministic_pivotCount_lower` begins with the raw perturbed normals and
right-hand sides, obtains the near-ball sandwich, normalizes positive RHS values,
constructs every polar-face and endpoint estimate along the concrete charged path,
and invokes the finite capstone directly on Tier-2 `pivotCount`. The module compiled
on its first attempt with only the standard three axioms. A pointwise good-event
eliminator was added as well, leaving only root-level splitting/antipodal packaging.
