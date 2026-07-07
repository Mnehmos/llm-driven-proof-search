# Credit & attribution — Erdős #349 folder

- **The mathematics.** The binary-representation theorem (every natural
  number is a sum of distinct powers of two) is classical/folklore —
  no attribution needed beyond "elementary number theory." Erdős Problem
  #349 itself (additive completeness of `⌊tαⁿ⌋`) is catalogued at
  [erdosproblems.com/349](https://www.erdosproblems.com/349) (Thomas Bloom).
- **Lean statement.** From
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  `FormalConjectures/ErdosProblems/349.lean` (Apache 2.0), theorem
  `exists_finset_sum_two_pow`, self-contained (no corpus-specific
  definitions needed).
- **Prior formal proof.** The corpus links a `formal_proof` to
  `cepadugato/formal-conjectures` (branch
  `erdos-349-integer-characterization-proof`) for this and several sibling
  theorems in the same file. Not inspected before writing ours — the proof
  below was found independently via Mathlib's `Finset.Colex` development.
- **This Lean proof.** Written in the Mnehmos/llm-driven-proof-search
  environment, **AI-assisted (Claude, Anthropic)** under human direction
  (Mnehmos). Correctness evidence is the Lean 4 kernel verdict, not the
  model. The substantive lemma used
  (`Finset.sum_toFinset_bitIndices_two_pow`) is Mathlib's own — credit to
  the Mathlib community (Apache 2.0), built originally for the
  Kruskal–Katona `Finset.Colex` development, not for this problem.
- **Verification infrastructure.** The LLM-Driven Proof Search Environment
  (this repository): hash-pinned statements, tracked episodes, kernel-gated
  outcomes.
