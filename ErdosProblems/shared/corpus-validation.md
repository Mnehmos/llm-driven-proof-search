# Erdős corpus validation — 2026-07-06

Checking the kit lab against the canonical Erdős problem corpus
(erdosproblems.com / [teorth/erdosproblems](https://github.com/teorth/erdosproblems),
Lean statements in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)),
and formalizing a few open problems.

## The corpus

- **1217** catalogued problems; **496** have Lean statements in
  `formal-conjectures` (`FormalConjectures/ErdosProblems/N.lean`).
- Status split (from the repo's own stats): 326 proved (116 formalized),
  132 disproved (61 formalized), 90 otherwise solved, 616 open.
- Format: each file has definitions plus `@[category research open|solved|…]`
  theorems; unsolved-answer problems use an `answer(sorry) ↔ …` shape, open
  ones a plain `sorry`.

## Validation against SOLVED problems (all kernel-verified)

`lean-checker/LeanChecker/Erdos/CorpusValidation.lean` — verified with
`lake env lean` under the pinned toolchain (lean4:v4.32.0-rc1 +
mathlib@360da6fa). Not imported by the `LeanChecker` root (on-demand artifact;
the EGZ n=3 `decide` is ~15s).

| Result | How | Trust rung |
|--------|-----|-----------|
| **Erdős–Ginzburg–Ziv, n = 2** (3 elts of ℤ/2 → 2 sum to 0) | kernel `decide` over the 2³ space | rung 1 |
| **Erdős–Ginzburg–Ziv, n = 3** (5 elts of ℤ/3 → 3 sum to 0) | kernel `decide` over the 3⁵ = 243 space | rung 1 |
| **Erdős–Ginzburg–Ziv, general** | `Int.erdos_ginzburg_ziv` (Mathlib) | Mathlib kernel proof |
| **Erdős–Ko–Rado** | `Finset.erdos_ko_rado` (Mathlib) | Mathlib kernel proof |
| **6 is perfect** (σ₁6 = 12) | `ArithmeticKit.sigma_mul_of_coprime` over 2·3 | rung 1 |
| **28 is perfect** (σ₁28 = 56) | `ArithmeticKit.sigma_mul_of_coprime` over 4·7 | rung 1 |

**What this confirms.** (1) The environment verifies real named Erdős theorems
end-to-end (EGZ, EKR via Mathlib). (2) The kits deliver on their registry
claims against real targets: the EGZ small instances are exactly the
"Erdős–Ginzburg–Ziv small instances" family the `ExtremalCombinatoricsKit`
entry lists, closed here at rung 1 (the same certificate ladder); the perfect
numbers exercise the `ArithmeticKit` σ-bridges on Erdős's own long-standing
interest in σ(n)/perfect/abundant numbers.

## Formalizing OPEN problems (statement only)

`lean-checker/LeanChecker/Erdos/OpenStatements.lean` — faithful, typechecking
Lean statements (`sorry` bodies; 3 sorry warnings, nothing else). These are
frontier problems, not provable here — the deliverable is a faithful statement.

- **Erdős–Straus**: `∀ n ≥ 2, 4/n = 1/a + 1/b + 1/c` with `a,b,c > 0`. Open.
- **Erdős problem 1** (distinct subset sums): if `A ⊆ {1,…,N}` has distinct
  subset sums then `N ≥ c·2^{|A|}`. Open (only `2^n/n` known); matches the
  corpus's own `erdos_1` statement.
- **Erdős–Turán additive basis**: if every `n` is a sum of two elements of
  `A ⊆ ℕ`, the representation function is unbounded. Open.

## Honest limits

- Proving *general* EGZ/EKR is "verify Mathlib has it," not a kit result; it
  validates the *environment*, and the writeup labels it as such. The genuine
  *kit* validation is the finite EGZ instances (rung 1) and the σ-bridge
  perfect-number checks.
- Most solved Erdős problems need mathematics far beyond a single session to
  formalize from scratch; the tractable solved ones are those Mathlib already
  carries or that reduce to a finite certificate. The certificate ladder
  (rungs 1–4, incl. the 2³⁶ Ramsey result) is what extends the reachable set
  beyond hand proofs — the EGZ finite instances sit on its rung 1, and larger
  EGZ/Schur/Rado instances are the natural next `bv_decide` targets.

## Next candidates

- EGZ / Schur / Rado **larger finite instances** via `bv_decide` (rung 2/4) —
  a direct extension of `ExtremalCombinatoricsKit`'s target families.
- Cross-reference the ~721 corpus problems **not** yet formalized against the
  kit domains (number theory, convexity, generating functions, inequalities)
  to find statements worth contributing upstream.
