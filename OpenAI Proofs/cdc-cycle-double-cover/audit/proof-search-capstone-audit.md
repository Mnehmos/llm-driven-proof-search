# Proof-search capstone audit

Date: 2026-07-11  
Verifier environment:
`9e26d28efe88484c36562da27aa22a2cc73a0638d11532cbbc9071a60609025d`  
Import manifest: `Mathlib`
(`b71c3c9da913b2ce43017a08a69ccf102d0e4a6d621776a18c3ef555960af7fc`)

## Claim audited

For finite types of vertices and primitive edge objects, with two numbered
ends per edge, every loopless graph with no one-edge cut has a list of
nonempty inclusion-minimal even edge sets in which each edge occurs exactly
twice.

This is the circuit form of the Cycle Double Cover statement for finite
loopless multigraphs. Parallel edge objects remain distinct, so a parallel
pair can form a two-edge circuit.

## Capstone evidence

| Step | Role | Problem version | Episode | Kernel outcome |
|---|---|---|---|---|
| 35 | Ends-form expansion conservation ⇒ localized three-edge equation | `ebdceefb-a181-4a85-89f6-7ba4a7ab337e` | `56f03854-caca-400f-b62a-2e386cfb7525` | `kernel_verified` |
| 36 | Expansion bridgelessness + global 8-flow ⇒ nowhere-zero expansion flow | `bb630198-62a9-4b2a-878f-02730b48a8e8` | `cbb5ffbb-e951-4ac5-b1b5-c62873d1a958` | `kernel_verified` |
| 37 | Expansion flow ⇒ localized cover ⇒ projected cover | `ea2b752c-c068-4470-a096-57ab8d5adb8a` | `50dad87f-d22e-4200-be67-8761c79d20cd` | `kernel_verified` |
| 38 | Loopless bridgeless graph ⇒ indexed even double cover | `a590ad0c-5165-49f7-b098-7c46eca98d93` | `e078a0a6-3a45-404d-84f0-1fa7c9c92c60` | `kernel_verified` |
| 39 | Indexed cover + cycle decomposition ⇒ cycle double cover | `7211fcc8-d1d9-422c-aab3-14db222a98b3` | `06c72fd1-9e61-44f0-8ec5-93995d204eed` | `kernel_verified` |

Step 39 does not assume the step-11 assembly theorem. It redoes the assembly:
each of the eight indexed even edge sets is decomposed into minimal nonempty
even components, the component lists are flattened, and the indexed
cardinality-two condition is converted into list multiplicity exactly two.

## Dependency closure

The capstone consumes the earlier verified chain as follows:

```text
Lemma 2.2 and cubic labeling: 01–08
cycle decomposition:           09
cover assembly/projection:     11–12
rotation and expansion:        13–16
global 8-flow theorem:         17–34
conservation localization:     35
expansion flow:                16 + 34 → 36
projected indexed cover:       35 + 15 + 08 + 12 → 37
bridgeless indexed cover:      14 + 13 + 36 + 37 → 38
Cycle Double Cover:            38 + 09 → 39
```

Cross-problem dependencies are represented by exact theorem-as-hypothesis
interfaces. This is necessary because proof-search problem versions do not
import one another and the verifier has a per-invocation wall limit. The
interfaces preserve the complete mathematical statements; they are not
unproved axioms in a combined source module. Each producer and each consumer
is separately kernel-verified and identified in the ledger.

## Local replay

The capstone files were also compiled sequentially against the same pinned
`lean-checker` environment:

```powershell
$base = 'F:\Github\mnehmos.llm-driven-proof-search.environment\OpenAI Proofs\cdc-cycle-double-cover\steps'
foreach ($n in 35..39) {
  $f = Get-ChildItem "$base\$n-*.lean" | Select-Object -First 1
  lake env lean $f.FullName
}
```

Observed result: exit code 0 for all five files, total wall time 76.8 seconds.

## Failed/superseded records

Two immutable registered statements contained an extra opening parenthesis and
were not proof-checked:

- step-38 malformed problem `fc93a289-d4e8-4a90-bc3f-2ed1a58ae488`,
  episode `32ca2af0-6a99-4fff-b7af-ee17534f466e`, explicitly `gave_up`
  after a root parse error;
- step-39 malformed problem `3b44630d-91a6-48bc-994f-1c58dec5356e`,
  superseded before an episode was created.

Neither is cited as proof evidence. The corrected versions are the
kernel-verified rows above.

## Trust boundary

The problem versions are marked `attested`, not independently
fidelity-certified. Kernel verification establishes the Lean implications;
the statement-to-manuscript correspondence is documented in the step ledger
and the independent `openai/cdc-lean` audit. The independent implementation
also proves the unconditional theorem in one project build and has an axiom
surface of only `propext`, `Classical.choice`, and `Quot.sound`.
