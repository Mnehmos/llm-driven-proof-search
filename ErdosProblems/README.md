# ErdosProblems — one folder per problem

Organized **by problem**: each Erdős problem this project has touched gets
its own self-contained folder with proof, evidence, credit, and a
problem-specific whitepaper. Start with the **[project index](whitepaper.md)**.

## Layout

```
ErdosProblems/
├── whitepaper.md          project-level index + system-wide trust design
├── README.md               this file
├── erdos-1/                Erdős Problem #1 (calibration case study)
│   ├── whitepaper.md       problem statement, proof idea, verification record
│   ├── credit.md           attribution: math, catalog, corpus, this proof
│   ├── evidence.md         machine records (result row, episode summary)
│   ├── proof/              snapshot .lean, byte-stamped by module_source_hash
│   └── trace/              hash-chained episode ledger
├── erdos-1052/             Erdős Problem #1052 (unitary perfect numbers)
│   ├── whitepaper.md
│   ├── credit.md
│   ├── evidence.md
│   ├── proof-narrative.md  how the proof was found, incl. round-1 failures
│   ├── attack-plan.md      staged milestones toward the OPEN question
│   ├── proof/
│   └── trace/
├── erdos-349/              Erdős Problem #349 (integer characterization — COMPLETE)
│   ├── whitepaper.md
│   ├── credit.md
│   ├── evidence.md         includes the local-corpus-scan discovery method
│   ├── attack-plan.md      integer_isGoodPair_iff fully assembled, all milestones DONE
│   ├── proof/              7 kernel-verified theorems
│   └── trace/              7 episode ledgers
├── erdos-647/              Erdős #647 (global density theorem DONE; problem OPEN)
│   ├── README.md           start here: headline results + status, plainly
│   ├── whitepaper.md       campaign log + complete density proof architecture
│   ├── attack-plan.md      completed density program + remaining existence directions
│   ├── credit.md           Hughes / Kitamura / Idén / Bloom attribution + limits
│   ├── evidence.md         tracked episodes + clean final replay
│   ├── dossiers/           full 319-episode export archive
│   └── proof/              172 Lean files; density and existence reductions included
└── shared/                 cross-problem infrastructure notes
    ├── corpus-validation.md
    ├── bounty-board.md
    ├── run-575f57b1-summary.md
    └── disclosure-note.md
```

Adding a new problem: copy the `erdos-1052/` shape (whitepaper, credit,
evidence, proof/, trace/; add `proof-narrative.md`/`attack-plan.md` only if
relevant) into a new `erdos-<N>/` folder and link it from the project index.

## Headline results

1. **Calibration MATCH** ([erdos-1/](erdos-1/whitepaper.md)) — an
   independently written proof agrees with the corpus's proof on file, on
   the byte-identical statement, under one verifier.
2. **Unitary perfect numbers are even** ([erdos-1052/](erdos-1052/whitepaper.md),
   Subbarao–Warren 1966): first standalone-reproducible Lean proof — the
   statement ships as `sorry` in google-deepmind/formal-conjectures, and
   the only prior linked proof does not replay outside its home
   infrastructure. Since then: general `σ*` multiplicativity (not in
   Mathlib), fast verification of the corpus's two disabled/`sorry` test
   numbers (`87360`, Wall's 24-digit fifth unitary perfect number), and a
   new structural bound (`ω_odd(n) ≤ ν₂(n)+1`) that combined with Wall's
   real 1988 theorem forces any sixth unitary perfect number to be
   divisible by `256`.
3. **The #349 integer characterization, fully assembled**
   ([erdos-349/](erdos-349/whitepaper.md)): `integer_isGoodPair_iff` —
   `(t,α)` is a good integer pair iff `t=1 ∧ α=2` — is kernel-verified,
   combining its four named component lemmas (`one_two_isGoodPair`,
   `alpha_le_one_not_isGoodPair`, `int_coeff_ge_two_not_isGoodPair`,
   `alpha_gt_two_not_isGoodPair`) via case split. A real, complete,
   already-known theorem (external `formal_proof` on file), now
   independently reproduced end-to-end through this project's own pipeline.
   See [erdos-349/attack-plan.md](erdos-349/attack-plan.md).
4. **The #291 harmonic-denominator companion (part ii)**
   ([erdos-291/](erdos-291/whitepaper.md)): `{n | gcd(aₙ,Lₙ) > 1}.Infinite` —
   the easy already-known direction (Steinerberger), which the corpus ships as
   `sorry`. Kernel-verified via the explicit infinite family `n = 2·3ᵏ`. The
   open part (i) (`= 1` infinitely often) is untouched.
5. **The #399 Cambie companion** ([erdos-399/](erdos-399/whitepaper.md)):
   `n! ≠ x⁴ + y⁴` for coprime `x,y` with `xy > 1` — corpus `sorry`,
   kernel-verified via a mod-8 fourth-power argument. The headline #399
   (does `n! = xᵏ ± yᵏ` have solutions) was already resolved by Barfield.
6. **Infinitely many Sierpiński numbers** ([erdos-1113/](erdos-1113/whitepaper.md),
   Sierpiński 1960): `Set.Infinite {k | IsSierpinskiNumber k}` — corpus `sorry`,
   kernel-verified via Selfridge's `{3,5,7,13,19,37,73}` covering generalized to
   the residue class `k ≡ 78557 (mod M)`. Uses **only kernel `decide`** (axioms
   `[propext, Classical.choice, Quot.sound]`, no `native_decide`) — a stronger
   guarantee than the corpus's own `selfridge_78557`. The open #1113 (a
   Sierpiński number with no finite covering) is untouched.
7. **#494 product version is false** ([erdos-494/](erdos-494/whitepaper.md),
   Steinerberger): distinct `A, B ⊆ ℂ` of equal size with the same multiset of
   3-subset *products* — corpus `sorry`, kernel-verified via the witness
   `A = {1,ω,ω²,2}`, `B = ω·A` (`ω³=1`), reducing to a one-line scalar lemma.
8. **The #647 global density theorem**
   ([erdos-647/](erdos-647/README.md), **density theorem complete; existence
   problem OPEN**): independent kernel-verified replication of the
   Hughes/Idén/Kitamura modular reduction (41 open residue classes, via a
   tighter 48-survivor sieve with every row *proven* from classification
   theorems); 48 new sub-AP closures (then frozen — the all-avoid
   obstruction proves that technique class can't finish); the **first
   machine-checked proof of Hughes's Theorem 2** (every candidate sits in
   one of two explicit 4-prime constellations); and a completed effective
   bound `|C(X)|≤KX/(log X)^7`. The proof repairs the missing level truncation,
   proves polynomial error control, supplies an elementary seventh-power
   denominator, certifies dyadic parameters, and closes the finite range.
    The folder publishes 461 theorem/lemma declarations (508 declarations when
    47 definitions, including two private helpers, are included) and full
    exports for 321 related proof-search episodes: 314 verified successes and
    seven retained non-success histories.
   The later existence work proves finite-catalog escape, large-prime
   non-reuse, subset-product/CRT re-entry reductions, and a conditional
   second-layer cofactor catalog. These sharpen the remaining problem but do
   not replace any of the three open Formal Conjectures declarations.

## Verify it yourself

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos1052.lean
```

Exit 0 = Lean's kernel accepts every step. No trust in the authors required.

## Status of open problems

**None of #1, #1052, #349, or #647 is resolved by this repository — all four
remain OPEN on erdosproblems.com.** Every proof in this repo targets a
*different, already-known* companion fact that lives in the same corpus
file as the open question, never the open question itself. See each
folder's whitepaper for the explicit "what we did / did not prove" split.

#1052's staged attack is in [erdos-1052/attack-plan.md](erdos-1052/attack-plan.md):
σ*-multiplicativity (done), fast verification of the corpus's missing
87360/25-digit tests (done), and a `ω_odd ≤ ν₂+1` structure bound (done) —
which, combined with Wall's real 1988 theorem, forces any sixth unitary
perfect number to be divisible by `256`. Real, if modest, new information —
not remotely close to resolving finiteness. An honest map of the wall is
still pending. A 2026 arXiv paper found while researching this was
identified as likely AI-fabricated and explicitly discarded — see the
attack-plan for the full disclosure.

#349's staged attack ([erdos-349/attack-plan.md](erdos-349/attack-plan.md))
targeted `integer_isGoodPair_iff` — a real, already-solved (by others)
characterization of the *integer* sub-case, not the general open question —
and is now **complete**: all 4 component lemmas plus the final iff assembly
are kernel-verified. The general question (`erdos_349` for real `(t,α)`)
remains open; this cluster does not touch it.

## Upstream

An upstream contribution to google-deepmind/formal-conjectures is **open** as
[PR #4405](https://github.com/google-deepmind/formal-conjectures/pull/4405):
`@[formal_proof using lean4]` links for three ErdosProblems/1052 statements
(`even_of_isUnitaryPerfect`, `isUnitaryPerfect_87360`, and Wall's
`isUnitaryPerfect_146361946186458562560000`), each pointing at this repo's
kernel-verified proof. Metadata-only — no proof bodies change upstream; the
`stop`/`sorry` in-file bodies stay put, matching the repo's existing
externally-hosted-proof convention. CLA check passes; awaiting maintainer
review.
