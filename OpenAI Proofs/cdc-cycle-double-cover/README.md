# Cycle Double Cover — two-track formal verification

This folder documents our verification of the Cycle Double Cover (CDC) theorem
claimed in the OpenAI paper
([cdc_proof.pdf](https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_proof.pdf))
and formalized in [openai/cdc-lean](https://github.com/openai/cdc-lean).

Two independent tracks, with different trust models:

## Track 1 — Independent kernel audit of `openai/cdc-lean`

We do not trust the repository's own `VERIFICATION.md`. We cloned the repo to
`f:\Github\cdc-lean`, built it from source under its pinned toolchain on this
machine, and ran the axiom audit ourselves. The full record, with commands and
raw results, is in [audit/cdc-lean-independent-verification.md](audit/cdc-lean-independent-verification.md).

Result: the final theorem `CDCLean.cycleDoubleCover_of_bridgeless` — every
finite loopless bridgeless multigraph has a list of circuits covering each edge
exactly twice — kernel-checks unconditionally, depending only on `propext`,
`Classical.choice`, and `Quot.sound`. Definition fidelity was reviewed by hand
(multigraph encoding, cut characterization of bridgeless, cycles as
inclusion-minimal nonempty even edge sets = genuine circuits).

## Track 2 — Step-by-step 0→1 re-derivation in our proof-search environment

The audit says *that* the theorem is true. This track shows *how* it is built,
one kernel-gated step at a time, inside the LLM-Driven Proof Search Environment
(this repository). Every step below is a registered problem whose proof was
proposed by the agent, rejected or accepted **only** by the pinned Lean
verifier through the tracked attempt path, with the full propose→fail→diagnose→
retry process recorded in append-only reasoning and attempt ledgers. Nothing is
marked proved by advisory metadata; the environment DB is the system of record.
The final dependency closure, capstone IDs, replay command, and superseded
malformed records are summarized in
[audit/proof-search-capstone-audit.md](audit/proof-search-capstone-audit.md).

### Verified step ledger (paper's cubic core, Lemmas 2.1–2.2)

| # | Step (file in `steps/`) | Mirrors in cdc-lean | Problem version | Episode | Outcome |
|---|---|---|---|---|---|
| 01 | Local pair parity (eqs. 2–3) | `local_pair_parity` | `64ea8680-26c9-4544-acb3-eaf565df0e2e` | `90be1f6b-3408-4362-9711-17380cd615fb` | kernel_verified (2026-07-11) |
| 02 | Local dual identity, dot-product form | `local_dual_identity` | `3d5b9cb6-b3a3-4358-95aa-b2e52bb2032b` | `23b209f0-a31f-40be-8ec4-429ebbfa56d9` | kernel_verified (2026-07-11) ⚠ uses `native_decide` |
| 03 | Abstract vertex identity (eqs. 7–9) | `local_dual_identity` (abstract χ) | `566d2bfc-fbc9-4d9f-a0e6-274ef69cb428` | `b64f8ba3-3ba8-46e5-8487-2dff301ee410` | kernel_verified (2026-07-11) |
| 04 | Global dual-obstruction assembly (system 4) | `compatibility_solvable` (certificate form) | `9eafd294-d3b7-4f2f-8704-6e530e0d227e` | `4eeb87f5-2ee8-48f1-a414-0b1e4c942ee6` | kernel_verified (2026-07-11) |
| 05 | Annihilator uniqueness in dim 3 | (implicit in their `decide`) | `cf9ca3b0-d4a9-4406-bf34-c406515efd6f` | `9763965c-5107-45db-bc6e-f5b2e391b250` | kernel_verified (2026-07-11, 1 attempt) |
| 06 | **Lemma 2.2 complete** — compatibility system solvable | `compatibility_solvable` | `4c4eb078-b6b6-4823-aa72-6d120035f823` | `0c06c7cd-de31-45f2-9fde-03a3690c6e81` | kernel_verified (2026-07-11, 2 attempts) |
| 07 | **Cubic labeling** (Lemma 2.1∘2.2) | `cubic_labeling` | `78778b1d-1889-477e-a4ad-66eb22059045` | `e0395b03-697b-420b-a75e-39ef1e388882` | kernel_verified (2026-07-11, 5 attempts — see note) |
| 08 | **Indexed even double cover** (cubic-case core) | `cubic_even_double_cover` | `3917309c-9df8-4f9b-a154-bb937a45cd05` | `15c3c5d2-7512-4545-a7da-cd3acfcf10fa` | kernel_verified (2026-07-11, 1 attempt) |
| 09 | **Cycle decomposition of even edge sets** | `decompose_even_edge_set` | `d269b928-fb3b-4ba5-b376-956bb15565d4` | `82fc190d-0f34-48bf-b4f3-f65641ebc129` | kernel_verified (2026-07-11, 1 attempt) |
| 10 | **Ends-form even double cover** | `cubic_even_double_cover` + `support_even` | `2667a666-0b2f-4786-b9d0-d5f874bc4883` | `e36261d0-3efc-448a-9cd9-4a78671ac349` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 11 | **Cover ⇒ cycle double cover** (assembly; hypotheses = concl. of 09 + 10) | `IndexedEvenDoubleCover.toCycleDoubleCover` | `4adc1d0b-1d85-4d3d-879d-0ec080d5f28a` | `c28d8df1-780e-4bd9-8018-34d4952c0f9d` | kernel_verified (2026-07-11, attempt 3) |
| 12 | **Expansion cover projection** (rings cancel; concl. = cover hyp. of 11) | `projected_vertex_even` / `projectEvenDoubleCover` | `b202d6d2-6d22-432b-a74d-ef472621567b` | `99c5106b-1669-4318-ac4b-146bbe1ed5e0` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 13 | **Rotation-system existence** (degree ≠ 1 ⇒ vertex-preserving fixed-point-free fiber-transitive perm) | `rotationSystemOfDegreeNeOne` | `abd3fd7f-4d0d-4042-98cc-14e68449e9db` | `04744cf3-b179-45d4-b0cb-f4a15896ba29` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×4) |
| 14 | **Bridgeless ⇒ degree ≠ 1** (concl. = hyp. of 13) | `degree_ne_one_of_bridgeless` | `7aa583df-c304-4f9f-9396-720964cebc4b` | `fb3502ad-11b3-4848-8c5a-630f6bb5d0c0` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 15 | **Flow ⇒ localized expansion cover** (step 08's statement as hypothesis, instantiated at the expansion incidence) | `cubicExpansion` + `expansionIncidence` + apply | `e46a54f1-e42c-4852-94a2-a7004c6f9e3e` | `dcc3a393-8dcd-4673-9757-4e4b91e7365d` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 16 | **Expansion is bridgeless** (ring cuts impossible in char 2; spoke cuts descend to G) | `expansionGraph_bridgeless` | `f6d3b3d0-6a74-45dd-8fc3-17214fdec90f` | `b05d039a-3fa5-413b-94c9-b8c226cc46ee` | kernel_verified (2026-07-11, attempt 2) |
| 17 | **Flow from three even covers** (8-flow campaign JK-A) | `nowhereZeroGammaFlow_of_evenCover` | `993b9826-f68c-4534-8517-877d118adf7b` | `045a2345-7bc2-4469-8784-179d6870e554` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 18 | **Even superset from fundamental cycles** (JK-B1; char-2 shortcut past the ℤ-circulation machinery) | `exists_even_superset_compl_of_spanningTree` (core) | `68e5b80e-c41c-45b7-b2c3-ace4d05ebcb6` | `35479379-9829-498c-af26-ab45e65fe4d4` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 19 | **Fundamental cycles from connectivity** (JK-B2; F₂ path-parity certificates by `ReflTransGen` induction; concl. = hyp. of 18) | `hasIntegerPath_*` / fundamental cycles | `c09edee4-ede6-4204-a1ba-305f42c9f080` | `0a521779-1dd0-4454-b62f-1a9978576729` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 20 | **Tree packing ⇒ nowhere-zero flow** (JK-D-lite; statements of 17+18+19 as hypotheses; disjointness gives edge coverage) | `nowhereZeroGammaFlow_of_threeEdgeConnected` glue (JK 334–399, modulo tree-packing input) | `43da22a1-fd7e-4f76-9f52-084b2f1a6e9f` | `c4caad40-c393-4c67-aac4-d4d51aed3f3f` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 21 | **3-edge-connected ⇒ doubled packing condition** (JK-C; partitions as classifiers `c : V → V`, classes = fibers over `image c`) | `doubleGraph_satisfiesTreePackingCondition_of_threeEdgeConnected` | `cd0a7b4a-c670-4f6c-8b6d-3bbee2afc41f` | `472fc585-97d4-4e96-a00f-df338308555c` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 22 | **Omission glue** (JK-D main-chain form: connected `T i` + every edge omitted by one ⇒ flow; 17/18/19 as hypotheses) | `nowhereZeroGammaFlow_of_threeEdgeConnected` glue (JK 388–399) | `1cd81f06-9a66-40ee-a070-11724bbd8d7d` | `40271639-6dcd-4ffd-93a0-b87dfc3d7e75` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 23 | **Doubled-packing projection** (disjoint connected sets in `E × Fin 2` ⇒ connected + omission in `E`; pigeonhole on copies; concl. = T-hyps. of 22) | packing half of `exists_three_spanningTrees_omitting_each_edge` (JK 334–386) | `18818939-1981-47c2-be2d-db85b813ba9b` | `10f70a28-eb75-45e4-bee8-5b8379977a96` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 24 | **Internal + quotient ⇒ connected** (NW-2; classifier fibers internally connected + class-closed quotient walks ⇒ full connectivity) | `connects_of_internal_of_quotient_connects` (NW 884–958) | `39c57ce0-76c9-4f85-b4f1-e3495e5ecaf2` | `5272c958-f18d-412b-84a2-86150c9ee396` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 25 | **Forest crossing count** (NW-1; forest + internal fibers ⇒ crossings ≤ classes−1, equality ⇒ quotient connected; merge induction on the crossing set) | counting layer, NW 2573–2691 (forests, classifier form) | `5341018f-9caf-456c-a188-8875d3a5c5da` | `ad2124ce-817b-42fe-bf43-b99920fad585` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×3) |
| 26 | **The exchange lemma** (NW-3 = Diestel 2.4.3, the heart of tree packing: maximum disjoint-forest tuple + fully-free edge ⇒ a predicate containing its ends, internally connected in every forest; exchange closure over tuples, free-edge adjacency component, 490-line single declaration) | replaces Kaiser machinery, NW 337–3459 | `3632c255-b78e-4128-9a1e-9602c3946de4` | `9f74edd6-8a3e-44bb-a9d5-58be0b4cb486` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×10) |
| 27 | **Nash-Williams tree packing, k=3** (NW-TOP: packing condition ⇒ three disjoint spanning-connected sets; 24+25+26 as hypotheses; max tuple + EqvGen classifier + counting) | `hasTreePacking_of_condition` / `nashWilliamsTutte` (NW 3592–3653) | `c5b86842-c29d-48fa-b477-a8a1b3466e3e` | `24730338-152b-4bf7-bc19-6d742e9d02c6` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×2) |
| 28 | **Conservation across a 2-cut** (JK-E-1: φ conserving off the ends of e₁ + 2-cut {e₁,e₂} + equal cut values ⇒ conserves everywhere; char-2 core of the contraction pullback) | `nowhereZeroGammaFlow_of_contractEdge_of_twoCut` (JK 686–793) | `8dda72dc-ccfc-45b4-a4c3-9213abd10162` | `1e07b2b0-cb95-413d-9e8e-bba0921b5211` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×3) |
| 29 | **3EC ⇒ doubled tree packing** (JK-E-2a: bundles 21+27, carrying 24/25/26; ⇒ three disjoint spanning-connected sets in `E × Fin 2`) | 21∘27 composition | `6edd347f-0058-4275-a8d7-67596c70f332` | `6bc3de88-43b8-4688-8ab4-d51377e6009b` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 30 | **Doubled packing ⇒ flow** (JK-E-2b: bundles 23+22, carrying 17/18/19; doubled disjoint-connected tuple ⇒ ends-form flow over E) | 23∘22 composition | `1a88148f-0169-4a60-b4e5-6365573274b8` | `d4cb12d9-65e5-49cc-8abf-af9d4ed7e632` | kernel_verified (2026-07-11, 1 attempt, pre-flighted) |
| 31 | **Two-cut contraction pullback** (JK-E-2c: nowhere-zero flow on the edge-contracted graph (abstract merge-map `q : V → W`) ⇒ nowhere-zero ends-form flow on the original; uses step 28) | `nowhereZeroGammaFlow_of_contractEdge_of_twoCut` (JK 686–793) | `0cf0561e-7176-4071-a692-93971bf687b4` | `f85271cd-ae3d-4a78-9fef-ce643d32a2fc` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×3) |
| 32 | **2-cut existence** (JK-E-3a: bridgeless + connected + ¬3EC ⇒ a 2-edge cut) | case split in `jaegerKilpatrickEightFlow_connected` (JK 905–933) | `e073d2c8-b40e-4ad7-8342-76957d951caf` | `67dd9620-f09d-4642-8552-4450f4afcf07` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×2) |
| 33 | **Bridgeless-to-3EC contraction recursion** (JK-E-3: THE main reduction — bridgeless + connected ⇒ nowhere-zero ends-form flow, no 3EC assumption; concrete subtype contraction `W := {v // v ≠ mergedVertex}`, strong induction on `card V`; carries hFlow3EC + steps 28/31/32) | `jaegerKilpatrickEightFlow_connected` (JK 902–933) | `aae6e901-7438-4e49-be94-d3e75df152ec` | `820065fe-ea40-476b-a30a-ebc0b2d56a53` | kernel_verified (2026-07-11, 1 attempt, sorry-skeleton-first ×8) |
| 34 | **Component decomposition** (JK-E-4: connectedness drops — EVERY bridgeless multigraph has a nowhere-zero ends-form flow; per-component flows via a `Quotient.out` reachability classifier, glued by disjoint supports; hypothesis = step 33's conclusion verbatim) | `jaegerKilpatrickEightFlow_of_nonempty` + components (JK 1110–1219) | `5145a5c2-63e7-4c86-805e-cfae1e2577b1` | `82de0408-700c-4382-91f0-ec34ac2c4f1d` | kernel_verified (2026-07-11, 1 attempt, pre-flighted ×4) |
| 35 | **Expansion conservation localization** (ends-form conservation on the concrete spoke/ring expansion collapses to the three-term equation consumed by step 15) | expansion incidence bookkeeping | `ebdceefb-a181-4a85-89f6-7ba4a7ab337e` | `56f03854-caca-400f-b62a-2e386cfb7525` | kernel_verified (2026-07-11, 1 attempt; locally pre-flighted) |
| 36 | **Expansion bridgeless ⇒ expansion flow** (step 16 composed with the completed step-34 8-flow theorem) | `expansionGraph_bridgeless` + Jaeger–Kilpatrick flow | `bb630198-62a9-4b2a-878f-02730b48a8e8` | `cbb5ffbb-e951-4ac5-b1b5-c62873d1a958` | kernel_verified (2026-07-11, 1 attempt; locally pre-flighted) |
| 37 | **Expansion flow ⇒ original indexed even cover** (35 → 15+08 → 12) | expansion flow, cubic cover, projection | `ea2b752c-c068-4470-a096-57ab8d5adb8a` | `50dad87f-d22e-4200-be67-8761c79d20cd` | kernel_verified (2026-07-11, 1 attempt; locally pre-flighted) |
| 38 | **Bridgeless graph ⇒ indexed even double cover** (14→13 rotation, then 36→37) | full reduction to the expansion | `a590ad0c-5165-49f7-b098-7c46eca98d93` | `e078a0a6-3a45-404d-84f0-1fa7c9c92c60` | kernel_verified (2026-07-11, corrected statement, 1 proof attempt) |
| 39 | **Final Cycle Double Cover capstone** (step 38 + step 09; step-11 list assembly rederived inline) | `cycleDoubleCover_of_bridgeless` theorem shape | `7211fcc8-d1d9-422c-aab3-14db222a98b3` | `06c72fd1-9e61-44f0-8ec5-93995d204eed` | kernel_verified (2026-07-11, 1 attempt) |

**Chained composition (general reduction, flow-conditional):** steps 14 → 13 →
15 (with 08 discharged) → 12 → 11 (with 09) compose to: *every finite loopless
bridgeless multigraph whose vertex-ring expansion carries a nowhere-zero
F₂³-flow has a cycle double cover*. Unconditional CDC now requires exactly two
more inputs: bridgelessness of the expansion (their
`expansionGraph_bridgeless`) and the Jaeger–Kilpatrick 8-flow theorem.

**Chained composition (8-flow for 3-edge-connected graphs, COMPLETE):** steps
21 → 27 (instantiated at `E × Fin 2`) → 23 → 22 (with 17/18/19 discharged
inside 22) compose to: *every finite 3-edge-connected multigraph has a
nowhere-zero F₂³-flow in ends form*. The Nash-Williams giant (3657 reference
lines) is covered by steps 24–27 in the Diestel maximum-tuple formulation —
the Kaiser machinery's recursively-defined partition sequences cannot cross
this environment's plain-statement chaining boundary, so the campaign proves
Diestel's exchange lemma (step 26) instead. Step 20 is the flow glue with a
pairwise-disjointness hypothesis in `E` itself — verified but off the main
chain, since the doubled packing projects to *overlapping* sets (only omission
survives; the pigeonhole of step 23). **Chained composition (THE 8-FLOW THEOREM, COMPLETE):** step 34 (fed step 33's
conclusion), step 33 (fed hFlow3EC — dischargeable by 29∘30 — and steps
28/31/32) compose to: *every finite bridgeless multigraph has a nowhere-zero
F₂³-flow in ends form*. The full discharge tree is
34 ← 33 ← (29∘30) ← {17,18,19,21,22,23,24,25,26,27} + {28,31,32} — every link
kernel-verified. **The capstone is now complete:** step 35 converts the
ends-form expansion flow to the localized equation; step 36 composes
expansion bridgelessness with the global 8-flow theorem; step 37 composes
35→15+08→12; step 38 supplies the rotation via 14→13; and step 39 combines
the resulting indexed even cover with step 09 while rederiving step 11's list
assembly inline. Thus the step-by-step track reaches the unconditional Cycle
Double Cover conclusion for finite loopless bridgeless multigraphs.

**Chained composition (cubic CDC):** steps 09 + 10 + 11 compose by two modus
ponens steps to: *every finite loopless cubic multigraph carrying a
nowhere-zero F₂³-flow has a cycle double cover*. The composition is chained
through hypotheses rather than inlined because the verifier enforces a
60-second wall cap per Lean invocation (and the MCP transport caps payload
size); each link is unconditional kernel evidence, and step 11's hypotheses
are exactly the conclusions of steps 09 and 10. The all-in-one restatement is
registered as problem `d835eca2-ab17-4a0d-bfd8-3ee859787439` (open; cannot fit
the wall cap as a single declaration).

**Parallel track:** files `08-multigraph-cdc.lean`, `08-cycle-decomposition.lean`,
`multigraph_test.lean`, `step_lemma21.json` in `steps/` were produced by a
separate concurrent session pursuing a Sym2-based multigraph encoding (loops
counted twice, ℕ-valued even degrees) against an extended checker setup. They
are preserved as found; the numbered ledger above refers to this session's
slot-equivalence/ZMod 2 track.

About a dozen additional supporting lemmas (span rank, dual separation,
incidence bookkeeping, edge-coordinate decomposition) were kernel-verified as
separate problems in the same environment on 2026-07-10/11; they are listed by
`problem_list` in the environment DB and superseded by steps 05–08 above.

### Notes on the process data

- Steps 05–08 compose earlier steps by **re-derivation**: the environment
  deliberately provides no cross-problem imports, so each root theorem is
  self-contained and independently kernel-checked. Step 06 appears verbatim as
  the `hsolv` sub-proof inside steps 07 and 08.
- Step 07's episode is the richest process artifact: five attempts spanning a
  cumulative-heartbeat exhaustion, a no-op `set_option` discovery, a
  `classical`-instance poisoning of `decide`, a genuine `Decidable` synthesis
  failure, and finally the module-with-helper-budgets idiom that solved it.
  The full attempt/diagnostic/reasoning trail is in the environment ledgers
  (episode `e0395b03-…`), exportable via `proof_export`/`trajectory_export`.
- Step 02 (early session) used `native_decide`, which extends trust beyond the
  Lean kernel. It is flagged here for honesty; the final chain (06→07→08) does
  **not** depend on it — everything is re-derived with plain kernel `decide`.
- Trust model: `fidelity_status` for these problems is `attested`
  (`unsafe_dev_attestation`), meaning statement–intent fidelity was asserted by
  the operating agent, not independently reviewed. The kernel outcomes are
  unconditional; the fidelity review of statements against the paper is the
  remaining human-auditable surface, aided by the side-by-side mirror column.

### Completion status

The tracked re-derivation now contains 39 kernel-verified steps, ending in the
unconditional CDC capstone. Cross-problem composition is expressed through
exact theorem-as-hypothesis interfaces because the proof-search environment
does not import declarations from previous problem versions and enforces a
per-invocation wall limit. Each interface link is separately kernel-verified,
and steps 35–39 were also compiled together against the pinned local
`lean-checker/` environment.

## Verifier environments

- Track 1: Lean `v4.31.0`, Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8`
  (cdc-lean pins), built locally 2026-07-11.
- Track 2: this repository's pinned lean-checker,
  environment hash `9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`,
  import manifest `Mathlib` (hash `b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`).

Two different Mathlib pins accepting structurally parallel proofs is itself a
robustness signal: no single library version is load-bearing.
