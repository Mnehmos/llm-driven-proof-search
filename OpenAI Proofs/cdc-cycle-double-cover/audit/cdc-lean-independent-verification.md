# Independent verification record — openai/cdc-lean

Date: 2026-07-11 (UTC)
Machine: local Windows 10 workstation (this repository's dev machine)
Operator: automated agent session (Claude), commands and outputs reproduced verbatim below.
Checkout: `f:\Github\cdc-lean` (clone of https://github.com/openai/cdc-lean, `main`, depth 1)

## What was verified

`CDCLean.cycleDoubleCover_of_bridgeless`: every finite loopless bridgeless
multigraph (`FiniteGraph V E` with `endAt : E → Fin 2 → V`, loopless) has a
`CycleDoubleCover` — a list of `Cycle`s (nonempty inclusion-minimal even edge
sets, i.e. genuine circuits; a parallel pair is a 2-cycle) in which every edge
object occurs exactly twice. The proof is unconditional: Jaeger–Kilpatrick's
8-flow theorem is proved inside the repo (`NashWilliams.lean`,
`JaegerKilpatrick.lean`), not axiomatized.

## Dependency surface checked before building

`lakefile.toml` requires only `leanprover-community/mathlib4` at rev
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

Toolchain resolved by elan from `lean-toolchain`: `leanprover/lean4:v4.31.0`.

## Results

1. **Build**: `Build completed successfully (1727 jobs).` All 15 CDCLean
   modules compiled and kernel-checked locally (Basic, CubicLabeling,
   EvenCover, GeneralGraph, SixFlow, CycleDecomposition, NashWilliams,
   CubicBridge, FlowCount, CubicTheorem, PathCut, JaegerKilpatrick, Expansion,
   Main, CDCLean).

2. **Axiom audit** (`#print axioms`, via `CDCLean/Audit.lean`) — every audited
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

- `FiniteGraph V E` (GeneralGraph.lean): edges are primitive objects with two
  numbered ends (`endAt : E → Fin 2 → V`, `loopless`). Parallel edges are
  genuinely distinct. Faithful multigraph. The loopless restriction is the
  standard WLOG for CDC.
- `Bridgeless` (GeneralGraph.lean): no vertex subset has an edge cut of
  cardinality one — the standard cut characterization of bridgeless for finite
  graphs.
- `Cycle` (CycleDecomposition.lean): a nonempty inclusion-minimal even edge
  set. For loopless multigraphs this is exactly the graphic-matroid circuit —
  the usual simple cycle, with a pair of parallel edges as a legitimate
  2-cycle. This is the *strong* (circuit) form of CDC, not the weaker
  even-subgraph form.
- `CycleDoubleCover` (CycleDecomposition.lean): a `List G.Cycle` (multiset —
  repetition allowed, as required e.g. for a digon) such that for every edge
  `e`, exactly two list entries contain `e`.
- `cubicExpansion`/`projectEvenDoubleCover` (Expansion.lean, spot-checked):
  the standard vertex-ring cubic expansion and its cover projection.

Conclusion: the statement is a faithful formalization of the Cycle Double
Cover conjecture for finite loopless bridgeless multigraphs, and the proof is
now independently kernel-verified on this machine.
