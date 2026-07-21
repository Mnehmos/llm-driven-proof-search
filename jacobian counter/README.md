# Jacobian Counterexample — Formal Release

Machine-certified formalization of the July 19, 2026 counterexample to the **Jacobian
Conjecture** (L. Alpöge; question credited to Akhil Mathew, construction credited to the
AI model Fable), verified through the LLM-Driven Proof Search Environment's pinned
Lean 4 + Mathlib kernel, July 20–21, 2026.

**Summary of record** (Wall Map closeout, commit `5b28607`): The project kernel-verifies
the explicit three-dimensional Jacobian counterexample, its normalized determinant-one
form, and all map-specific polynomial identities needed for its canonical Poisson and
Weyl lifts. It also contains a direct, unconditional, sorry-free Lean proof that the
canonical rank-three Poisson conjecture is false: the cotangent lift is a
bracket-preserving but non-surjective algebra endomorphism. Six theorems have passed
through the project's tracked verification environment — five with certified statement
fidelity — and the Poisson refutation is separately file-verified against the pinned
Mathlib. Exact external certificates additionally construct an eleven-variable cubic
normalization and a twenty-three-variable cubic-homogeneous counterexample. The
Weyl/Dixmier and Zhao consequences remain transport and infrastructure targets; the
genuinely open mathematics is the dimension-two problem (control of escape at infinity)
and an explicit finite-type SU(3) moment witness.

The algebraic verification and global geometry of the map are developed in
P. Chojecki, *A Counterexample to the Jacobian Conjecture* (ulam.ai research write-up,
July 20, 2026, announced at [@prz_chojecki](https://x.com/prz_chojecki); families
generalization credited therein to GPT-5.6 Pro). The formal theorems below certify that
paper's Theorem 3.1 computations and their consequence for the conjecture.

## The counterexample

```
F(x,y,z) = ( (1+xy)³z + y²(1+xy)(4+3xy),
             y + 3x(1+xy)²z + 3xy²(4+3xy),
             2x − 3x²y − x³z )  :  ℂ³ → ℂ³
```

- **det Jac F ≡ −2** — a Keller map (nonzero constant Jacobian determinant), and yet
- **F(0,0,−1/4) = F(1,−3/2,13/2) = F(−1,3/2,13/2) = (−1/4,0,0)** — a collapsed fiber.

A Keller map that is not injective cannot be a polynomial automorphism, contradicting the
conjecture (Keller 1939) in dimension 3 — and by stabilization in every dimension ≥ 3.

## Files

| File | Contents | Status |
|------|----------|--------|
| `whitepaper.md` | Public-facing account: what happened, what is formally proved, what "certified" means, collateral damage | doc |
| `proof-construction.md` | Technical construction: mechanism, formal architecture, engineering pitfalls, full verification ledger | doc |
| `Challenge.lean` | Theorem statements 1–5 with `sorry` — solve them yourself | compiles (with `sorry` warnings) |
| `ChallengeSolved.lean` | Verbatim kernel-accepted proofs of theorems 1–5 | **compiles clean** against Mathlib `v4.32.0-rc1` |
| `certificates/` | Layered 11-variable determinant certificate; 23-variable cubic-homogeneous lift certificate (both exact sympy, status E) | all checks pass |
| `CollateralDamage.lean` | Dixmier / Zhao / cubic-reduction statements; certified core + sorry-free conditional refutations + cited open bridges | see file header labels |
| `jacobian.pdf` | Source paper: P. Chojecki, *A Counterexample to the Jacobian Conjecture* (ulam.ai) | external, not committed |

## The verified theorems

Six theorems through the environment's kernel path (rows 1–6: one `kernel_verified`,
five `certified`), plus one file-verified theorem (row 7: sorry-free, compiled clean
against the pinned Mathlib, not yet transported through the certification path).

| # | Claim | Problem / Episode | Outcome |
|---|-------|-------------------|---------|
| 1 | Symbolic det = C(−2) ∧ three-point collision (over ℚ) | `29f88fb5` / `0c0afd37` | `kernel_verified` |
| 2 | **¬ Jacobian Conjecture** (ℂ, dim 3), exactly the negated instance of DeepMind formal-conjectures' `jacobian_conjecture` | `654521be` / `1f9dfbee` | **`certified`** |
| 3 | F's evaluation map ℂ³ → ℂ³ is not injective | `f3b97f2c` / `a8a4062d` | **`certified`** |
| 4 | ¬ Jacobian Conjecture (ℂ, dim 4), stabilized witness (F, w) | `7312a555` / `591219bc` | **`certified`** |
| 5 | Normalized form U = (R/2, Q, P): det = 1, U(0) = 0, JU(0) = I, three-point fiber over the fixed point (0,0,−1/4) (paper Cor. 3.2) | `c270a9d2` / `c8d0d87c` | **`certified`** |
| 6 | **Poisson-bridge computational core**: J·B = −2·I (mixed brackets) + all 27 commuting-derivation identities for B = adj(J) in explicit cofactor form — the complete polynomial content of the rank-3 Poisson counterexample | `a4044282` / `c25405a7` | **`certified`** |
| 7 | **¬PoissonStatement, unconditional**: the canonical rank-3 Poisson conjecture is FALSE — cotangent lift is a bracket-preserving non-surjective endomorphism (generic generator-extension lemma + 36 in-file generator brackets + two-point-fiber separation; no inverse theorem, no bridge). In `CollateralDamage.lean` | in-repo, `poisson_statement_false` | **file-verified, sorry-free** (`lake env lean` exit 0; not yet environment-certified) |

`certified` = kernel-verified proof **+** hash-bound verified statement-fidelity review —
the environment's highest trust level. Environment hash `9e26d28e…`; statement hashes and
fidelity review IDs in `proof-construction.md` §2/§5. Full attempt ledgers (including all
five failed attempts and their kernel diagnostics) are replayable in the environment's
append-only ledger.

Independent cross-check: determinant and all three point images verified in exact
rational arithmetic with sympy before formalization.

## Honest scope

- Formalized: the counterexample's defining computations and their contradiction with
  polynomial invertibility (dims 3, 4) and injectivity.
- **Not** formalized: the paper's fiber/image/nonproperness geometry, the general-n
  stabilization, and the literature bridges to Dixmier / Mathieu / Zhao / cubic
  reduction (stated formally with citations in `CollateralDamage.lean`, proved only
  conditionally).
- The identification of the informal 1939 conjecture with the `formal-conjectures`
  statement is that repository's (reviewed, public) formalization decision.
- Peer review of the source announcement is ongoing.

## Upstream

`formal-conjectures/FormalConjectures/Wikipedia/JacobianConjecture.lean` (vendored
subtree of google-deepmind/formal-conjectures) gains a `research solved` disproof
variant pointing at this release; see that file's `jacobian_conjecture.variants.
disproof_dim_three`. Not yet submitted upstream (CLA + `lake --wfail build` gate).
