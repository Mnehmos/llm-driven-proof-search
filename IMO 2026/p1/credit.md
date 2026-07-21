# Credit & attribution — IMO 2026 Problem 1

- **Problem source.** International Mathematical Olympiad 2026 official
  problems page; 67th IMO, Shanghai, contest day 1. The local transcription is
  [`problem.md`](problem.md).
- **Mathematical solution.** Independently derived in this campaign. The proof
  uses a product/non-unit termination measure and the gcd of prime valuations
  as the choice-independent invariant.
- **Formalization and proof search.** AI-assisted by OpenAI Codex (GPT-5) under
  user direction in the Mnehmos LLM-Driven Proof Search Environment. Every
  formal success cited here was submitted through the proof-search MCP and
  accepted by the pinned Lean kernel.
- **Libraries.** Lean 4 and Mathlib contributors. The registered import manifest
  was `Mathlib.Tactic.Ring`, `Mathlib.Tactic.NormNum`, and `Mathlib`.
- **Disclosure.** No circulating IMO solutions were imported into the problem
  statement. The formal targets were self-authored decompositions of the local
  proof. They used development attestation rather than independent fidelity
  review, so their correct label is `kernel_verified`, never `certified`.
- **Scope limit.** The complete formal root is kernel-verified but has not
  received an independent fidelity review. See
  [`whitepaper.md`](whitepaper.md).
