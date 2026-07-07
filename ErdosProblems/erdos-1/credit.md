# Credit & attribution — Erdős #1 folder (calibration)

- **The mathematics.** Erdős Problem #1 (distinct subset sums, `N ≫ 2^n`,
  $500) is open; the *weaker bound* `N ≫ 2^n/n` proven here is Erdős's
  classical counting argument (folklore/Erdős, mid-20th century).
- **Problem catalog.** [erdosproblems.com/1](https://www.erdosproblems.com/1)
  (Thomas Bloom); [teorth/erdosproblems](https://github.com/teorth/erdosproblems).
- **Lean statement AND the reference proof on file.** Both from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  `FormalConjectures/ErdosProblems/1.lean` (Apache 2.0): the
  `IsSumDistinctSet` definition, the `erdos_1.variants.weaker` statement,
  and its complete proof (`C = 1/3`). That proof compiles unmodified in our
  pinned toolchain and is the external artifact our calibration audit
  compares against.
- **This independent proof.** Written in the Mnehmos/llm-driven-proof-search
  environment, **AI-assisted (Claude Opus 4.8, Anthropic)** under human
  direction (Mnehmos); different constant (`C = 1/4`) and structure.
  Disclosure: the reference was necessarily inspected during target
  selection — the audit certifies the pipeline, not proof originality.
  Correctness evidence is the Lean 4 kernel verdict. Mathlib (Mathlib
  contributors, Apache 2.0) underneath.
