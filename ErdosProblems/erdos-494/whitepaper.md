# Erdős Problem #494 — the product version is false (Steinerberger)

**Problem folder whitepaper — 2026-07-07**

> Erdős asked whether a finite set `A ⊆ ℂ` is determined by the multiset of the
> sums of its `k`-element subsets. The **multiplicative** analogue — is `A`
> determined by the multiset of *products* of its `k`-subsets? — is **false**,
> by a counterexample of Steinerberger. The corpus
> (`FormalConjectures/ErdosProblems/494.lean`, `erdos_494.variants.product`)
> ships this `research solved` statement as `sorry`; this folder gives a
> self-contained, kernel-verified proof.

## What this folder proves

`Erdos494.product : ∃ (A B : Finset ℂ), A.card = B.card ∧
prodMultiset A 3 = prodMultiset B 3 ∧ A ≠ B`, where `prodMultiset A k` is the
corpus's definition (the multiset of products of the `k`-element subsets of
`A`).

## The counterexample and the one-line idea

Let `ω` be a primitive cube root of unity and take
`A = {1, ω, ω², 2}`,  `B = ω·A = {1, ω, ω², 2ω}`  (`A ≠ B`, same cardinality).

The clean observation: `B = A.map (ω · —)`, so the 3-subsets of `B` are exactly
the `ω·`-images of the 3-subsets of `A`, and **each** 3-subset product scales by
`ω³ = 1`. Hence the two product-multisets are equal. Concretely both equal
`{1, 2, 2ω, 2ω²}`.

The whole proof reduces to one general lemma, `prodMultiset_map_mul`: multiplying
every element of `A` by a scalar `c` with `cᵏ = 1` leaves `prodMultiset A k`
unchanged (via `Finset.powersetCard_map` + `∏ (c·x) = c^k · ∏ x = ∏ x`). No
`powersetCard` is ever computed explicitly — and, pleasantly, one never needs to
prove the four elements of `A` are distinct, since `A.card = B.card` is just
`Finset.card_map`.

## What we did / did not prove

- **Did:** `product` — the product-version counterexample, kernel-verified,
  axioms `[propext, Classical.choice, Quot.sound]`.
- **Did not:** the sum-version `research solved` siblings in the same file
  (`k_eq_2_card_not_pow_two`, `k_eq_2_card_pow_two`, `k_eq_3_card_gt_6`, …),
  which are the genuine Selfridge–Straus results.

## Reproduce

```bash
cd lean-checker
lake env lean LeanChecker/Erdos/Erdos494.lean
```

Exit 0, **0 errors / 0 warnings**. Snapshot:
[proof/Erdos494_product.lean](proof/Erdos494_product.lean)
(sha256 `9fd75fcfe16f863a341387c48f5ec77d019ddc1e3b8191e232f6d70da0b0cdb1`).
Toolchain: `leanprover/lean4:v4.32.0-rc1` + `mathlib@360da6fa`.
