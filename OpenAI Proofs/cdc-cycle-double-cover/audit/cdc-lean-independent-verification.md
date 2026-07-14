# Independent verification record — openai/cdc-lean

Date: 2026-07-11 (UTC)  
Machine: local Windows 10 workstation (this repository's dev machine)  
Operator: automated agent session (Claude), commands and outputs reproduced verbatim below.  
Checkout: `f:\Github\cdc-lean` (clone of [openai/cdc-lean](https://github.com/openai/cdc-lean), `main`, depth 1)

**Repository:** [Mnehmos/llm-driven-proof-search](https://github.com/Mnehmos/llm-driven-proof-search) ·
**Tag:** [v0.3.29](https://github.com/Mnehmos/llm-driven-proof-search/releases/tag/v0.3.29) ·
**Full step ledger:** [README.md](../README.md) ·
**Track 2 capstone audit:** [proof-search-capstone-audit.md](proof-search-capstone-audit.md)

## What was verified

[`CDCLean.cycleDoubleCover_of_bridgeless`](https://github.com/openai/cdc-lean/blob/main/CDCLean/Main.lean):
every finite loopless bridgeless
multigraph (`FiniteGraph V E` with `endAt : E → Fin 2 → V`, loopless) has a
`CycleDoubleCover` — a list of `Cycle`s (nonempty inclusion-minimal even edge
sets, i.e. genuine circuits; a parallel pair is a 2-cycle) in which every edge
object occurs exactly twice. The proof is unconditional: Jaeger–Kilpatrick's
8-flow theorem is proved inside the repo ([`NashWilliams.lean`](https://github.com/openai/cdc-lean/blob/main/CDCLean/NashWilliams.lean),
[`JaegerKilpatrick.lean`](https://github.com/openai/cdc-lean/blob/main/CDCLean/JaegerKilpatrick.lean)),
not axiomatized.

**Upstream references:**
- OpenAI benchmark prompt: [`cdc_prompt.pdf`](https://cdn.openai.com/pdf/94be3ee6-d3dc-4d37-8e52-94e80dc58c73/cdc_prompt.pdf)
- Mathematical proof sketch: [`cdc_proof.pdf`](https://cdn.openai.com/pdf/04d1d1e4-bc75-476a-97cf-49055cd98d31/cdc_proof.pdf)
- Upstream formalization: [openai/cdc-lean](https://github.com/openai/cdc-lean)

## Dependency surface checked before building

[`lakefile.toml`](https://github.com/openai/cdc-lean/blob/main/lakefile.toml)
requires only `leanprover-community/mathlib4` at rev
`9a9483a92959bc92bd6a60176dd1fe597298c1f8`; `lake-manifest.json` pins the
standard transitive Mathlib dependencies (plausible, LeanSearchClient,
import-graph, ProofWidgets, …) from `leanprover-community` scopes only. No
third-party or non-community package. Project config is declarative TOML.

## Commands run

```bash
git clone --depth 1 https://github.com/openai/cdc-lean.git
cd cdc-lean
lake exe cache get
lake build CDCLean
lake env lean CDCLean/Audit.lean
grep -rnE '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*(axiom|opaque|unsafe)\b' --include='*.lean' CDCLean/ CDCLean.lean
```

Toolchain resolved by elan from [`lean-toolchain`](https://github.com/openai/cdc-lean/blob/main/lean-toolchain): `leanprover/lean4:v4.31.0`.

## Results

1. **Build**: `Build completed successfully (1727 jobs).` All 15 CDCLean
   modules compiled and kernel-checked locally ([Basic](https://github.com/openai/cdc-lean/blob/main/CDCLean/Basic.lean),
   [CubicLabeling](https://github.com/openai/cdc-lean/blob/main/CDCLean/CubicLabeling.lean),
   [EvenCover](https://github.com/openai/cdc-lean/blob/main/CDCLean/EvenCover.lean),
   [GeneralGraph](https://github.com/openai/cdc-lean/blob/main/CDCLean/GeneralGraph.lean),
   [SixFlow](https://github.com/openai/cdc-lean/blob/main/CDCLean/SixFlow.lean),
   [CycleDecomposition](https://github.com/openai/cdc-lean/blob/main/CDCLean/CycleDecomposition.lean),
   [NashWilliams](https://github.com/openai/cdc-lean/blob/main/CDCLean/NashWilliams.lean),
   [CubicBridge](https://github.com/openai/cdc-lean/blob/main/CDCLean/CubicBridge.lean),
   [FlowCount](https://github.com/openai/cdc-lean/blob/main/CDCLean/FlowCount.lean),
   [CubicTheorem](https://github.com/openai/cdc-lean/blob/main/CDCLean/CubicTheorem.lean),
   [PathCut](https://github.com/openai/cdc-lean/blob/main/CDCLean/PathCut.lean),
   [JaegerKilpatrick](https://github.com/openai/cdc-lean/blob/main/CDCLean/JaegerKilpatrick.lean),
   [Expansion](https://github.com/openai/cdc-lean/blob/main/CDCLean/Expansion.lean),
   [Main](https://github.com/openai/cdc-lean/blob/main/CDCLean/Main.lean),
   CDCLean).

2. **Axiom audit** (`#print axioms`, via [`CDCLean/Audit.lean`](https://github.com/openai/cdc-lean/blob/main/CDCLean/Audit.lean)) — every audited
   declaration, including the final theorem, reports exactly
   `[propext, Classical.choice, Quot.sound]`:

   ```
   'CDCLean.local_pair_parity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.local_dual_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.compatibility_solvable' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.cubic_even_double_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.FiniteGraph.expansionGraph_bridgeless' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.FiniteGraph.tutteFlowCardinalityInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.FiniteGraph.IndexedEvenDoubleCover.toCycleDoubleCover' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.cycleDoubleCover_of_sixFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.cycleDoubleCover_of_gammaFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'CDCLean.cycleDoubleCover_of_bridgeless' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Source scan**: clean — no `sorry`, `admit`, `native_decide`, `axiom`,
   `opaque`, or `unsafe` anywhere in the project sources.

## Definition fidelity review (manual)

The only way a sorry-free, axiom-clean build can fail to prove CDC is if the
definitions don't say what the conjecture says. Reviewed by hand:

- [`FiniteGraph V E`](https://github.com/openai/cdc-lean/blob/main/CDCLean/GeneralGraph.lean) (GeneralGraph.lean): edges are primitive objects with two
  numbered ends (`endAt : E → Fin 2 → V`, `loopless`). Parallel edges are
  genuinely distinct. Faithful multigraph. The loopless restriction is the
  standard WLOG for CDC.
- [`Bridgeless`](https://github.com/openai/cdc-lean/blob/main/CDCLean/GeneralGraph.lean) (GeneralGraph.lean): no vertex subset has an edge cut of
  cardinality one — the standard cut characterization of bridgeless for finite
  graphs.
- [`Cycle`](https://github.com/openai/cdc-lean/blob/main/CDCLean/CycleDecomposition.lean) (CycleDecomposition.lean): a nonempty inclusion-minimal even edge
  set. For loopless multigraphs this is exactly the graphic-matroid circuit —
  the usual simple cycle, with a pair of parallel edges as a legitimate
  2-cycle. This is the *strong* (circuit) form of CDC, not the weaker
  even-subgraph form.
- [`CycleDoubleCover`](https://github.com/openai/cdc-lean/blob/main/CDCLean/CycleDecomposition.lean) (CycleDecomposition.lean): a `List G.Cycle` (multiset —
  repetition allowed, as required e.g. for a digon) such that for every edge
  `e`, exactly two list entries contain `e`.
- [`cubicExpansion`/`projectEvenDoubleCover`](https://github.com/openai/cdc-lean/blob/main/CDCLean/Expansion.lean) (Expansion.lean, spot-checked):
  the standard vertex-ring cubic expansion and its cover projection.

Conclusion: the statement is a faithful formalization of the Cycle Double
Cover conjecture for finite loopless bridgeless multigraphs, and the proof is
now independently kernel-verified on this machine.

## Correspondence with Track 2

The Track 2 re-derivation mirrors these Lean declarations step-by-step.
See the [step ledger](../README.md) for the side-by-side `Mirrors in cdc-lean` column.
Key correspondences:

| cdc-lean declaration | Track 2 step | Source |
|---|---|---|
| `local_pair_parity` | Step 01 | [01-local-pair-parity.lean](../steps/01-local-pair-parity.lean) |
| `local_dual_identity` | Step 02 | [02-local-dual-identity-dotproduct.lean](../steps/02-local-dual-identity-dotproduct.lean) |
| `compatibility_solvable` | Step 06 | [06-lemma-2-2-compatibility-solvable.lean](../steps/06-lemma-2-2-compatibility-solvable.lean) |
| `cubic_even_double_cover` | Step 08 | [08-indexed-even-double-cover.lean](../steps/08-indexed-even-double-cover.lean) |
| `expansionGraph_bridgeless` | Step 16 | [16-expansion-bridgeless.lean](../steps/16-expansion-bridgeless.lean) |
| `toCycleDoubleCover` | Step 11 | [11-cover-to-cycle-double-cover.lean](../steps/11-cover-to-cycle-double-cover.lean) |
| `cycleDoubleCover_of_bridgeless` | Step 39 (capstone) | [39-cycle-double-cover-capstone.lean](../steps/39-cycle-double-cover-capstone.lean) |
