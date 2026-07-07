# Credit & disclosure — Erdős #494 (product version false)

## Mathematics
- **Problem:** Erdős #494 (Selfridge–Straus / Gordon–Fraenkel–Straus): is a
  finite set determined by the multiset of sums of its `k`-subsets?
- **This result:** the *product* analogue is **false**, by a counterexample
  attributed to **S. Steinerberger** (per the erdosproblems catalog / corpus
  docstring). Our witness is the primitive-cube-root family
  `A = {1, ω, ω², 2}`, `B = ω·A` — a clean instance of the same idea.

## Corpus
- Statement source: google-deepmind/formal-conjectures,
  `FormalConjectures/ErdosProblems/494.lean`, theorem
  `erdos_494.variants.product`, shipped `sorry`. The `prodMultiset` definition
  is copied from that file.

## This proof
- Formalized by an LLM (Claude, Opus 4.8) in the verifier-gated proof-search
  environment; verified **solely by the Lean 4 kernel + Mathlib**, axioms
  `[propext, Classical.choice, Quot.sound]`.

## Honest limits
- Known mathematics. The contribution is the formalization artifact. Does not
  address the sum-version (Selfridge–Straus) `research solved` siblings.
