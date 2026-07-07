# Credit & disclosure — Erdős #291 (ii)

## Mathematics
- **Problem:** Erdős #291, on the denominators of harmonic numbers. Open
  question (part i) remains unresolved.
- **Part (ii), the solved companion:** the observation that `gcd(aₙ,Lₙ) > 1`
  infinitely often is attributed to **S. Steinerberger** (via the erdosproblems
  catalog note: any `n` with leading base-3 digit `2` has `3 ∣ (aₙ,Lₙ)`).
- Our proof uses a specific infinite family `n = 2·3ᵏ` — a special case of that
  observation, chosen to give the cleanest fully-elementary formalization
  (needing only `v₃(Lₙ) ≥ k`, no lcm-valuation upper bound).

## Catalog / corpus
- Statement source: google-deepmind/formal-conjectures,
  `FormalConjectures/ErdosProblems/291.lean`, theorem `erdos_291.parts.ii`,
  shipped `sorry`. The `L`/`a` definitions and the `L_eval`/`a_eval` test
  values are the corpus's; we reproduced them and cross-checked by `decide`.

## This proof
- Formalized by an LLM (Claude, Opus 4.8) in the verifier-gated proof-search
  environment; **verified solely by the Lean 4 kernel + Mathlib** — no trust in
  the author. First standalone-reproducible Lean proof of this statement that
  we are aware of.

## Honest limits
- Known mathematics; the contribution is the formalization artifact, not new
  mathematics. Does not touch the open part (i) or any other #291 variant.
