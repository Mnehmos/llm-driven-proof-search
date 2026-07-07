# Credit & attribution — Erdős #349 folder

- **The mathematics.** The binary-representation theorem (every natural
  number is a sum of distinct powers of two) is classical/folklore. The
  other six theorems in this folder — including the culminating
  `integer_isGoodPair_iff` — are elementary real-analysis/number-theory
  arguments and a case-split assembly of them, all already known math,
  catalogued as `research solved` in the corpus, none of it new. Erdős
  Problem #349 itself (additive completeness of `⌊tαⁿ⌋`) is catalogued at
  [erdosproblems.com/349](https://www.erdosproblems.com/349) (Thomas Bloom).
- **Lean statements.** From
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  `FormalConjectures/ErdosProblems/349.lean` (Apache 2.0): `exists_finset_sum_two_pow`,
  `int_coeff_ge_two_not_isGoodPair`, `alpha_le_one_not_isGoodPair`,
  `one_two_isGoodPair`, `dyadic_two_isGoodPair`,
  `alpha_gt_two_not_isGoodPair`, `integer_isGoodPair_iff`. The latter six use
  the corpus's `IsGoodPair`/`IsAddComplete`/`subsetSums` abbreviations from
  `FormalConjecturesForMathlib/NumberTheory/AdditivelyComplete.lean`,
  inlined (specialized to `M = ℤ`) for tracked registration.
- **Prior formal proof.** The corpus links a `formal_proof` to
  `cepadugato/formal-conjectures` (branch
  `erdos-349-integer-characterization-proof`) for all seven theorems in this
  folder. The first five local proofs were written before inspecting that
  linked fork. For `alpha_gt_two_not_isGoodPair`, the follow-up session used
  the linked proof's growth-gap route as a candidate plan and then checked
  the transported proof through this repository's tracked Lean verifier.
  `integer_isGoodPair_iff` is a mechanical case-split assembly of the four
  already-proved pieces — no additional external route needed.
- **This Lean proof.** Written in the Mnehmos/llm-driven-proof-search
  environment, **AI-assisted (Claude, Anthropic)** under human direction
  (Mnehmos). Correctness evidence is the Lean 4 kernel verdict, not the
  model. The substantive lemma reused for the binary-expansion constructions
  (`Finset.sum_toFinset_bitIndices_two_pow`) is Mathlib's own — credit to
  the Mathlib community (Apache 2.0), built originally for the
  Kruskal–Katona `Finset.Colex` development, not for this problem. The
  remaining negative results (`int_coeff_ge_two_not_isGoodPair`,
  `alpha_le_one_not_isGoodPair`, `alpha_gt_two_not_isGoodPair`) are direct
  ordered-field/`Finset` arguments; the last also uses standard Mathlib
  facts about geometric sums, floors, and tendsto at infinity.
- **Verification infrastructure.** The LLM-Driven Proof Search Environment
  (this repository): hash-pinned statements, tracked episodes, kernel-gated
  outcomes.
