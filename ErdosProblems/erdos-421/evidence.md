# Evidence — Erdős Problem #421 (machine records)

All work tracked live inside the `proofsearch` MCP tool. IDs below are
stable references into that ledger; re-run `reasoning_log` with
`action.type=observe` against the episode IDs to replay the full trail.

## Problems registered

| Problem | `problem_version_id` | Root statement |
|---|---|---|
| Erdős #421 root (corpus-faithful) | `535faff4-c8c1-48af-88fc-732c68277f70` | `∃ d, StrictMono d ∧ 1≤d 0 ∧ density(range d)=1 ∧ InjOn(block-product)` |
| Density-1/4 variant (self-authored) | `49ca0931-9dd1-4e06-85bf-0afc3aa1cb99` | Same shape, density `1/4`, witness `d(n)=4n+2` |

(Both superseded an earlier registration with an insufficient Ring+NormNum-only
import manifest — `dc09e348-747e-43a3-ad51-c944492374a8` and
`f5b1bf42-9afb-4380-befd-4718e6b17e22` respectively — reissued with the full
Mathlib umbrella.)

## Episodes

- Root #421 episode: `c0f8d0f5-ab86-4e93-9fa7-9d373ca4933b` — holds the
  root obligation and campaign-level plan; not expected to reach
  `kernel_verified` given the density-1 case is genuinely open.
- Density-1/4 episode: `0f5562fe-e14f-41b9-9f7b-ac11485a1be6` — real
  proof-search episode.
  - `Decompose` split the root existential (witness fixed to `4n+2`) into
    two children: (1) `StrictMono ∧ 1≤d0 ∧ InjOn` (structural), (2) the
    density `Tendsto` limit.
  - Child (1), obligation `O_1446cf16b3e14f8c`: **first `Solve` attempt
    failed** (`kernel_fail`) with two concrete, localized bugs — an
    un-beta-reduced `Set.InjOn` hypothesis used directly in `rw`, and
    `Finset.prod_lt_prod_of_nonempty'` requiring a `MulLeftStrictMono ℕ`
    instance that doesn't exist. **Second `Solve` attempt, with both
    fixes applied, kernel-verified successfully** (`kernel_pass`,
    reward `5000`). Every other part of the ~70-line proof (the
    `Nat.factorization_prod_apply` valuation argument, the
    `Finset.image_add_left_Icc` reindexing, all `omega` arithmetic)
    elaborated correctly on the *first* attempt.
  - Child (2), obligation `O_83c289dc5c4649bc`: the density-`1/4` `Tendsto`
    goal for `d(n)=4n+2`, via `tendsto_add_mul_div_add_mul_atTop_nhds` +
    `div_le_div_iff₀` + `nlinarith` squeeze on the floor-division count.
    **Kernel-verified on the first submission attempt**, zero bugs.
  - **Root assembly**: `exact ⟨fun n => 4n+2, O_1446cf16b3e14f8c.1,
    O_1446cf16b3e14f8c.2.1, O_83c289dc5c4649bc, O_1446cf16b3e14f8c.2.2⟩`,
    referencing both proved children by name. **`outcome=kernel_verified`,
    `termination_reason=root_proved`**, reward included
    `root_kernel_verified:20000`. The density-1/4 problem_version's root
    existential is now completely proved end-to-end. Snapshot at
    [proof/Erdos421_density_quarter.lean](proof/Erdos421_density_quarter.lean).

## Second problem/episode: generalized k-prime multiplicity lemma

`problem_version_id = a9f3f35b-7495-44ba-a62b-78a5dc96be0b`, episode
`318d5fcd-17af-4688-8f15-f4437dbdc4ce`. Statement: `∀ S : Finset ℕ, ∀ a b :
Finset ℕ, (∀n∈a, ∑q∈S, n.factorization q = 1) → (∀n∈b, ...) → a.prod id =
b.prod id → a.card = b.card`. **Kernel-verified on the first submission**,
`outcome=kernel_verified`, `termination_reason=root_proved`. Generalizes
the density-1/4 result's single-prime valuation argument to an arbitrary
finite set of primes -- the ℕ-specialization of the corpus's
`Set.IsMulCardSet` for Selfridge's set `A_S`. Snapshot:
[proof/GeneralMulCard.lean](proof/GeneralMulCard.lean). Reasoning logs:
`83d6e2ad-7604-43eb-9028-7e0960d14989` (initial_plan),
`facbfe74-ac63-4591-992f-a146a4e1b082` (success_retrospective).

Honest scoping of what's *left* for the full `erdos_786.parts.i.selfridge`:
the cutoff-`k`-exists part is tractable (Mathlib has
`Nat.Primes.not_summable_one_div`, `Mathlib/NumberTheory/SumPrimeReciprocals.lean`),
but the density `= 1/e - ε` claim needs a Mertens-third-theorem-style
asymptotic (`∏(1-1/q) → e⁻¹`) with **no located Mathlib lemma** (searched
for "Mertens" across Mathlib, zero hits) -- assessed as a genuinely
substantial, multi-session sub-project. Recorded as dossier node
`9f7feb53-7be5-4dcd-8bf2-8c3a20fe4602` (open_gap).

## Research dossier

`dossier_id = 1d3efc7e-8e21-45e6-a30f-8361bc187a8c`, linked to the root
problem version. Contains:
- External references: Selfridge/#786 (`external_citation_unreviewed`,
  corpus `sorry`), CCDN determinant method (arXiv:2311.05433, Vermeulen,
  citing/extending CCDN), Bilu–Tichy (not on arXiv, pre-arXiv-era, Acta
  Arith. 2000), Hajdu–Tijdeman (not independently located), Li's primes in
  almost all short intervals (arXiv:2407.05651, confirmed).
- One `candidate_construction` (`a57edcd6-1415-47df-b320-5c64b0404ad5`)
  tracking the disputed density-1 claim's two architectures and its four
  reported-then-fixed bugs, `trust_status=cited` (never proved).
- Two dossier `nodes`: the root proposition, and an explicit `open_gap`
  node stating the density-1 case is genuinely unresolved by this project.

## Empirical searches (experimental evidence, never proof)

`empirical_search_id = 61fa13eb-1cac-4ae1-82ed-cc0ff0483aaf` — exact
bigint exhaustive pairwise block-product check, run independently in
Python (script: `erdos421_empirical.py`, kept in this session's scratch
area, not committed — reproducible from the description below):

| Construction | Result |
|---|---|
| identity `d_i=i` (naive full density) | Collision found immediately: blocks `(0,1)` and `(1,1)` both give product `2` (since `d_1=1` is a multiplicative identity) |
| `d(n)=4n+2`, 400 terms | No collision (matches the kernel-verified result above) |
| `d(n)=6n+2`, 300 terms | Collision found at blocks `(0,36)` vs `(3,37)` — **refutes** the naive idea that the valuation trick generalizes to any modulus; `k=3` is odd, breaking uniform 2-adic valuation |
| `d(n)=10n+2`, 300 terms | No collision found in range, but `k=5` is *also* odd (same flaw as `k=3`) — this is flagged explicitly as **not** trustworthy evidence, likely a larger collision exists out of range |
| Forum's "prefix-stable greedy", N=2000 | 1948/2000 kept, empirical density 0.974, 107s — qualitatively matches the forum's own description ("looks promising, leaves no control") |

## Reasoning log IDs (chronological)

1. `fae7641c-0cd7-4452-97c8-9cdc7dbc4fff` — root #421 `initial_plan`
2. `f0cb282a-db3b-4715-b181-a70a342bea3b` — density-1/4 `initial_plan`
3. `7af76aff-2b16-48ae-91fe-8fabbd9d69fd` — `retry_after_failure` (the two bugs above)
4. `d5c8885f-0da0-4b9e-aeca-f10c5f2be0a0` — `success_retrospective` (structural half verified)
5. `dbdcf521-614f-4496-895a-a9e8b17a2583` — `success_retrospective` (density Tendsto + root assembly both verified; campaign's density-1/4 sub-goal is COMPLETE)

## Reproduce

This work is tracked live in the `proofsearch` MCP's database. A
reconstructed snapshot of the full kernel-verified proof is at
[proof/Erdos421_density_quarter.lean](proof/Erdos421_density_quarter.lean)
(toolchain `leanprover/lean4:v4.32.0-rc1` +
`mathlib@360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`).
