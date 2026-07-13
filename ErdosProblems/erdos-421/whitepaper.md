# Erdős Problem #421 — density-1 sequence with distinct consecutive-block products

**Problem folder whitepaper — started 2026-07-13, LIVE campaign**

> **Status: Erdős Problem #421 is OPEN.** [erdosproblems.com/421](https://www.erdosproblems.com/421)
> still marks it open. Its comment thread carries an actively-disputed,
> AI-assisted claimed full solution (density exactly 1) that has **not**
> passed the site's moderation and has **not** been read/verified in detail
> by the maintainer (Thomas Bloom) as of 2026-07-13. This folder does **not**
> resolve that claim either way. It records our own, fully independent,
> kernel-verified partial progress plus a durable, honest map of the
> external state of the art.

## The problem

Is there a sequence `1 ≤ d_1 < d_2 < ...` with density 1 such that all
products `∏_{u≤i≤v} d_i` over consecutive-index blocks are pairwise
distinct?

Formal statement (from `google-deepmind/formal-conjectures`,
`FormalConjectures/ErdosProblems/421.lean`, theorem `Erdos421.erdos_421`):

```lean
∃ (d : ℕ → ℕ), StrictMono d ∧ 1 ≤ d 0 ∧ HasDensity (Set.range d) 1 ∧
    {(u, v) : ℕ × ℕ | u ≤ v}.InjOn fun (u, v) => ∏ i ∈ Finset.Icc u v, d i
```

## What is genuinely established (as of 2026-07-13)

- **Selfridge's construction** (Erdős Problem #786, `erdos_786.parts.i.selfridge`
  in the same corpus): density `1/e − ε` for any `ε > 0`, via naturals
  divisible by exactly one of a well-chosen set of consecutive primes.
  Category `research solved` in the corpus, but the Lean proof body is
  **still `sorry`** — informally accepted, never kernel-verified anywhere.
- **Our own contribution — FULLY kernel-verified 2026-07-13:** the explicit
  sequence `d(n) = 4n + 2` (naturals `≡ 2 (mod 4)`) has natural density
  exactly `1/4` and **all consecutive-block products are pairwise
  distinct** — the complete existential statement (matching Erdős #421's
  exact shape, with `1` replaced by `1/4`) is Lean-kernel-verified
  end-to-end (`root_kernel_verified`, no `sorry`, no external citations).
  See [evidence.md](evidence.md) for the exact proof-search trail and
  [proof/Erdos421_density_quarter.lean](proof/Erdos421_density_quarter.lean)
  for the reconstructed snapshot.
- **What is disputed and NOT relied on by us:** a claimed density-1
  solution (Przemek Chojecki, heavy GPT-5.x assistance, reviewed publicly
  by Terence Tao) leaning on the Castryck–Cluckers–Dittmann–Nguyen
  determinant method, Bilu–Tichy/Hajdu–Tijdeman degeneracy classification,
  and (in a 2026-07-13 simplification) Runbo Li's "primes in almost all
  short intervals" (arXiv:2407.05651). Several concrete bugs were found
  and reportedly fixed across multiple iterations; the site maintainer has
  explicitly not verified it. We track it as an unverified external claim,
  never as evidence — see the `candidate_construction` and `open_gap`
  dossier entries.

## Proof idea for our density-1/4 result (elementary, no external citations)

Every `d(n) = 4n+2 = 2·(2n+1)` has 2-adic valuation **exactly** 1 (the
cofactor `2n+1` is always odd). By `Nat.factorization_prod_apply`, a
consecutive block of length `L` has product with 2-adic valuation exactly
`L`, so two blocks with equal products must have equal length
(`Nat.card_Icc` turns this into `p.2+1-p.1 = q.2+1-q.1`). For a *fixed*
length, reindexing one block onto the other via `Finset.image_add_left_Icc`
and comparing termwise with `Finset.prod_lt_prod_of_nonempty` shows the
block product is **strictly increasing** in its start index — so equal
products force equal start index too. Together: injectivity.

## What we did / did not prove

- **Did (kernel-verified 2026-07-13, complete):**
  `∃ d, StrictMono d ∧ 1≤d 0 ∧ HasDensity(range d, 1/4) ∧
  {(u,v)|u≤v}.InjOn(block-product)` — the full existential, witness
  `d(n)=4n+2`, all three components (structural half, density-Tendsto
  half, and the final assembly) independently kernel-verified via three
  `episode_step` submissions in episode `0f5562fe-e14f-41b9-9f7b-ac11485a1be6`.
- **Did not:** Selfridge's stronger `1/e − ε` bound (corpus `sorry`,
  unformalized) — our natural next target — and emphatically **not** the
  disputed density-1 claim, which remains genuinely open to this project
  and to the mathematical community as of this writing.

## Proof-search trail

Tracked entirely inside the `proofsearch` MCP tool (problems, episodes,
reasoning logs, research dossier, empirical searches) per this project's
trust doctrine: nothing here is claimed proved except what the pinned Lean
kernel actually accepted. See [evidence.md](evidence.md) and
[credit.md](credit.md).

Live dev diary (X-thread style): [dev-diary/](dev-diary/)
