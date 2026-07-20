# Jacobian Counterexample — Formal Release

Machine-certified formalization of the July 19, 2026 counterexample to the **Jacobian
Conjecture** (L. Alpöge; question credited to Akhil Mathew, construction credited to the
AI model Fable), verified through the LLM-Driven Proof Search Environment's pinned
Lean 4 + Mathlib kernel on July 20, 2026.

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
| `Challenge.lean` | The four theorem statements with `sorry` — solve them yourself | compiles (with `sorry` warnings) |
| `ChallengeSolved.lean` | Verbatim kernel-accepted proofs of all four | **compiles clean** against Mathlib `v4.32.0-rc1` |
| `CollateralDamage.lean` | Dixmier / Zhao / cubic-reduction statements; certified core + sorry-free conditional refutations + cited open bridges | see file header labels |
| `jacobian.pdf` | Source paper: P. Chojecki, *A Counterexample to the Jacobian Conjecture* (ulam.ai) | external, not committed |

## The four verified theorems

| # | Claim | Problem / Episode | Outcome |
|---|-------|-------------------|---------|
| 1 | Symbolic det = C(−2) ∧ three-point collision (over ℚ) | `29f88fb5` / `0c0afd37` | `kernel_verified` |
| 2 | **¬ Jacobian Conjecture** (ℂ, dim 3), exactly the negated instance of DeepMind formal-conjectures' `jacobian_conjecture` | `654521be` / `1f9dfbee` | **`certified`** |
| 3 | F's evaluation map ℂ³ → ℂ³ is not injective | `f3b97f2c` / `a8a4062d` | **`certified`** |
| 4 | ¬ Jacobian Conjecture (ℂ, dim 4), stabilized witness (F, w) | `7312a555` / `591219bc` | **`certified`** |

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
