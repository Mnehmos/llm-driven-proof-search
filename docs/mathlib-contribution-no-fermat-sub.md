# Mathlib contribution: Fermat's `x⁴ − y⁴ ≠ z²`

**Artifact:** `lean-checker/LeanChecker/NoFermatSub.lean` — self-contained,
`import Mathlib` only, compiles EXIT 0, axioms `[propext, Classical.choice,
Quot.sound]` (no `sorry`, no `native_decide`).

## What it is

Mathlib has `not_fermat_42` (`a⁴ + b⁴ ≠ c²`, in `Mathlib/NumberTheory/FLT/Four.lean`)
but is **missing the companion minus-version** `x⁴ − y⁴ ≠ z²` — Fermat's theorem
that no right triangle with integer sides has a perfect-square area (equivalently,
the elliptic curve `y² = x³ − x` has rank 0; Conrad, *Proofs by Descent*, Thm 3.10
& Cor 3.14).

Two public results (namespace `Int`):

- `not_fermat_sub_coprime (a b c : ℤ) : IsCoprime a b → b ≠ 0 → c ≠ 0 → a⁴ ≠ b⁴ + c²`
  — the coprime core, by infinite descent on `a.natAbs`.
- `sq_ne_fourth_sub_fourth (x y z : ℤ) : x⁴ − y⁴ = z² → y = 0 ∨ z = 0`
  — the general (coprimality-free) form, via `gcd`-reduction to the core.

Proof method: `PythagoreanTriple.coprime_classification` applied twice (a `b`-odd
single descent and a `b`-even double-classification descent), plus
`Int.sq_of_gcd_eq_one`. ~200 lines. This mirrors the structure of Mathlib's own
`not_fermat_42` descent.

## Suggested upstream shape

- **File:** `Mathlib/NumberTheory/FLT/Four.lean` (next to `not_fermat_42`).
- **Names:** align with local conventions there; likely `Int.not_fermat_sub` /
  `Fermat42.not_fermat_sub` for the general form. The two private helper lemmas
  (`beven_factor`, `beven_step`) may be inlined or kept as `private`.
- The two helper lemmas and the core here are named descriptively; a maintainer
  may prefer a single theorem with the descent inlined, matching the existing
  `not_fermat_42` proof style.

## Action needed (not automatable)

Opening the PR requires the **Mathlib CLA** and a human-driven review cycle — see
memory `erdos-ecosystem-contribution-path`. I cannot sign the CLA or open the PR
autonomously. When ready: fork `leanprover-community/mathlib4`, drop the theorem
into `FLT/Four.lean` (adjust imports — Mathlib file, not `import Mathlib`), match
the naming, and submit.

## Provenance

Extracted from the `#672` marathon (`lean-checker/LeanChecker/Erdos/Erdos672.lean`),
where it is also applied to prove `Erdos672.triangular_not_fourth_power` (the only
triangular number that is a perfect fourth power is `1`). NOTE: this crux does
**not** close Erdős #672 itself — that is the rank-0 fact for a *different*,
non-isogenous curve (`y²=x³−x²−4x+4`); see `ErdosProblems/erdos-672/attack-plan.md`.
