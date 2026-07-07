# Credit & disclosure — Erdős #399 (Cambie companion)

## Mathematics
- **Problem:** Erdős #399 (`n! = xᵏ ± yᵏ`). Headline resolved (Barfield's
  `10! = 48⁴ − 36⁴`), already in the corpus as `erdos_399`.
- **This companion:** the observation that `n! = x⁴ + y⁴` has no solution with
  `gcd(x,y)=1`, `xy>1` is attributed to **Cambie** (erdosproblems catalog
  note: "considerations modulo 8 rule out any solutions"). Our proof follows
  exactly that mod-8 route.
- Related classical results in the same file: Erdős–Obláth 1937 (`k ≠ 4`,
  coprime), Pollack–Shapiro 1973 (`n! = x⁴ − 1`) — not formalized here.

## Corpus
- Statement source: google-deepmind/formal-conjectures,
  `FormalConjectures/ErdosProblems/399.lean`, theorem
  `erdos_399.variants.cambie`, shipped `sorry`.

## This proof
- Formalized by an LLM (Claude, Opus 4.8) in the verifier-gated proof-search
  environment; **verified solely by the Lean 4 kernel + Mathlib**.

## Honest limits
- Known mathematics; the contribution is the formalization artifact. Does not
  touch the open siblings or the headline (already-resolved) question.
