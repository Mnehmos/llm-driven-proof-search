# Erdős Problem #399 — factorials as `xᵏ ± yᵏ` (Cambie's mod-8 companion)

**Problem folder whitepaper — 2026-07-07**

> **Status: Erdős #399's headline question is resolved (not by us).** Erdős
> asked whether `n! = xᵏ ± yᵏ` has solutions with `xy > 1`, `k > 2`; the answer
> is *yes there are* (Barfield: `10! = 48⁴ − 36⁴`), already in the corpus. This
> folder proves a **different, already-known companion** attributed to Cambie:
> there is no solution to `n! = x⁴ + y⁴` with `gcd(x,y) = 1` and `xy > 1`. The
> corpus ships it as `sorry`; kernel-verified here.

## What this folder proves

`Erdos399.cambie : ∀ {n x y : ℕ}, x.Coprime y → 1 < x * y → n ! ≠ x ^ 4 + y ^ 4`
— byte-identical to the corpus's `erdos_399.variants.cambie`.

## Proof (one paragraph)

Fourth powers detect parity mod 8: `a⁴ ≡ a (mod 2)` as a residue mod 8, i.e.
`odd⁴ ≡ 1`, `even⁴ ≡ 0 (mod 8)` (proved by `a⁴ % 8 = a % 2`, a finite check
over the 8 residues). Coprimality forbids `x, y` both even, so
`x⁴ + y⁴ ≡ 1 or 2 (mod 8)`, never `0`. For `n ≥ 4`, `8 ∣ n!`, so
`n! ≡ 0 (mod 8)` — contradiction. For `n ≤ 3`, `n! ≤ 6`, while `xy > 1` with
`x, y ≥ 1` forces one of them `≥ 2`, hence `x⁴ + y⁴ ≥ 2⁴ + 1 = 17 > 6`. Either
way `n! ≠ x⁴ + y⁴`. ∎

## What we did / did not prove

- **Did:** `cambie` (`n! ≠ x⁴+y⁴`, coprime, `xy>1`), kernel-verified.
- **Did not:** the sibling `research solved` sorries in the same file
  (`erdos_oblath` for general `k ≠ 4`, `pollack_shapiro` `n!+1 ≠ x⁴`,
  `sum_two_squares`). Each needs its own (deeper) argument.

## Reproduce

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos399.lean
```

Exit 0, **0 errors / 0 warnings**. Snapshot:
[proof/Erdos399_cambie.lean](proof/Erdos399_cambie.lean)
(sha256 `eefb770b0aef6fd5cbef46cbd54a4fc03ebdf6d49a006815c7b0497ddaaa8da9`).
Toolchain: `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`.
