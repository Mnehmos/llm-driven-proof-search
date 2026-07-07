# Credit & attribution — Erdős #1052 folder

- **The mathematics.** The theorem *unitary perfect numbers are even* and
  the notion of unitary perfect numbers: M. V. Subbarao and L. J. Warren,
  *Unitary perfect numbers*, Canad. Math. Bull. 9 (1966). The fifth known
  unitary perfect number: C. R. Wall (1975). The open finiteness question is
  catalogued as Erdős Problem #1052.
- **Problem catalog.** [erdosproblems.com](https://www.erdosproblems.com/1052)
  (maintained by Thomas Bloom); machine-readable catalog
  [teorth/erdosproblems](https://github.com/teorth/erdosproblems).
- **Lean statement.** The formal statement (definitions
  `properUnitaryDivisors`, `IsUnitaryPerfect`, theorem shape
  `even_of_isUnitaryPerfect`) is from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  `FormalConjectures/ErdosProblems/1052.lean` (Apache 2.0). Our registered
  statement inlines those definitions (definitional delta-reduction,
  documented in the fidelity-review notes).
- **Prior formal proof.** An AlphaProof-generated proof exists, linked from
  the corpus (mzhorvath1 fork, commit `b70a2ddf`). It established the
  statement's solved status in its home environment; it does not replay
  against plain Mathlib (custom tactics + older toolchain). Our proof is
  independent of it (fetched only after our kernel verdict) and is the
  standalone-reproducible artifact.
- **This Lean proof.** Written in the Mnehmos/llm-driven-proof-search
  environment, **AI-assisted (Claude Opus 4.8, Anthropic)** under human
  direction (Mnehmos). Correctness evidence is the Lean 4 kernel verdict —
  not the model, not the authors. Mathlib (Mathlib contributors, Apache 2.0)
  provides the underlying library.
- **Verification infrastructure.** The LLM-Driven Proof Search Environment
  (this repository): hash-pinned statements, tracked episodes, kernel-gated
  outcomes. (Note: proof snapshots contain verbatim `ChatDB.P_*` namespace
  strings — legacy internal identifiers preserved byte-exactly because the
  verification hashes cover them.)
