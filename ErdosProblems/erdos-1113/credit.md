# Credit & disclosure — Erdős #1113 (infinitely many Sierpiński numbers)

## Mathematics
- **Problem:** Erdős #1113. The *open* question (Sierpiński numbers with no
  finite covering set) is unresolved. This folder proves the classical solved
  companion.
- **Result:** *There are infinitely many Sierpiński numbers* — **W. Sierpiński,
  1960** (*Elementary Theory of Numbers*), via covering systems.
- **Covering set:** `{3,5,7,13,19,37,73}` for `78557` is due to **J. Selfridge**
  (1962). Our proof reuses this covering and generalizes it across the residue
  class `k ≡ 78557 (mod 3·5·7·13·19·37·73)` to produce the infinite family.

## Corpus
- Statement source: google-deepmind/formal-conjectures,
  `FormalConjectures/ErdosProblems/1113.lean`, theorem
  `erdos_1113.variants.infinitely_many_sierpinski`, shipped `sorry`.
- Definitions (`Composite`, `Nat.IsSierpinskiNumber`) copied byte-for-byte from
  `FormalConjecturesForMathlib`. The corpus's `SierpinskiNumber.selfridge_78557`
  (the single-number case, `native_decide`) was the technique reference; our
  proof strengthens it to infinitude and to pure kernel `decide`.

## This proof
- Formalized by an LLM (Claude, Opus 4.8) in the verifier-gated proof-search
  environment; verified **solely by the Lean 4 kernel + Mathlib** with only the
  standard axioms `[propext, Classical.choice, Quot.sound]` (no `native_decide`).

## Honest limits
- Known mathematics (Sierpiński 1960). The contribution is the formalization
  artifact — a first standalone, pure-kernel Lean proof of the infinitude, so
  far as we can tell. Does not touch the open #1113.
