# Proof narrative -- `alpha_gt_two_not_isGoodPair`

Status: formalized and kernel-verified through the tracked proof-search
environment. Episode `6c0babf6-d577-4847-a2a5-08d2318b97e5`, benchmark result
`d986f456-340c-4fa6-ae95-06304a51eedb`, pass@3. This proves the fourth
component lemma needed by `integer_isGoodPair_iff`; the final iff assembly is
still a separate tracked target.

Target:

```lean
alpha_gt_two_not_isGoodPair (t alpha : Real) (ht : 0 < t) (ha : 2 < alpha) :
  ¬ IsGoodPair t alpha
```

With the corpus definitions expanded, this says the set
`range (fun n : Nat => floor (t * alpha^n))` is not additively complete in
`Int`: for arbitrarily large integers `M`, there is no finite set of terms
whose sum is `M`.

## Core idea

Let

```text
a_n = floor(t * alpha^n) : Int
S_n = a_0 + a_1 + ... + a_n : Int
```

For `alpha > 2`, the sequence eventually has genuine gaps:

```text
a_{n+1} >= S_n + 2.
```

Once this happens, the integer

```text
M = S_n + 1
```

cannot be a subset sum. A subset using any term `>= a_{n+1}` is already too
large, since all terms are nonnegative. A subset using only terms
`< a_{n+1}` uses only values from indices `0..n` by monotonicity, so its sum is
at most `S_n`. Thus `S_n + 1` is missed.

The analytic part of the formal proof is to prove such gaps happen beyond
every threshold.

## Growth estimate

First record the elementary bounds.

1. `a_n >= 0`, because `t > 0`, `alpha > 0`, and `t * alpha^n >= 0`.
2. `a_n` is monotone, because `alpha >= 1` implies `alpha^n` is monotone and
   `floor` is monotone.
3. `a_k <= t * alpha^k`, so

```text
S_n <= t * (1 + alpha + ... + alpha^n)
    = t * (alpha^(n+1) - 1) / (alpha - 1)
    <= t * alpha^(n+1) / (alpha - 1).
```

Also, `floor x > x - 1`, hence

```text
a_{n+1} > t * alpha^(n+1) - 1.
```

Subtracting the upper bound for `S_n` gives

```text
a_{n+1} - S_n - 1
  > t * alpha^(n+1) - 1 - t * alpha^(n+1)/(alpha - 1) - 1
  = t * alpha^(n+1) * (alpha - 2)/(alpha - 1) - 2.
```

Since `alpha > 2`, the coefficient

```text
t * (alpha - 2)/(alpha - 1)
```

is positive, so the right-hand side tends to `+infinity`. Therefore, for any
integer threshold `N`, choose `n` large enough that

```text
t * alpha^(n+1) * (alpha - 2)/(alpha - 1) - 2 >= max(N + 2, 3)
t * alpha^n - 1 >= N.
```

The first inequality gives the integer gap `a_{n+1} >= S_n + 2`. The second
gives `S_n >= a_n >= N`, so the missed value `M = S_n + 1` is also `>= N`.

## Missed-value argument

Fix `N` and choose `n` as above. Set `M = S_n + 1`.

Assume toward contradiction that `M` is a subset sum of the range of `a`, so
there is a finite set `B : Finset Int` with

```text
B ⊆ range a
M = sum B.
```

Every element of `B` is nonnegative.

Case 1: some `b in B` satisfies `a_{n+1} <= b`.

Then

```text
sum B >= b >= a_{n+1} >= S_n + 2,
```

contradicting `sum B = S_n + 1`.

Case 2: every `b in B` satisfies `b < a_{n+1}`.

For any `b in B`, choose `m` with `b = a_m`. If `m >= n + 1`, monotonicity gives
`a_{n+1} <= a_m = b`, contradiction. Hence `m <= n`, so every `b` lies in the
finite image of the first `n + 1` sequence values.

Therefore

```text
sum B <= sum (image a {0, ..., n}) <= S_n,
```

using nonnegativity. This contradicts `sum B = S_n + 1`.

Thus for every `N` there is an integer `M >= N` outside the subset sums, so the
range of `a` is not eventually additively complete.

## Lean formalization milestones

The accepted Lean proof keeps these as local `have` blocks rather than named
helper lemmas.

1. `floor_geometric_nonneg`

```lean
∀ n, 0 <= floor (t * alpha ^ n)
```

2. `floor_geometric_mono`

```lean
Monotone (fun n : Nat => floor (t * alpha ^ n))
```

3. `floor_geometric_partial_sum_bound`

```lean
((∑ k in Finset.range (n + 1), floor (t * alpha ^ k) : Int) : Real)
  <= t * alpha ^ (n + 1) / (alpha - 1)
```

4. `exists_large_gap`

For every integer `N`, there is `n` with both `S_n >= N` and
`a_{n+1} >= S_n + 2`.

5. `missed_value_of_large_gap`

If `a` is nonnegative and monotone, `S_n = sum_{k<=n} a_k`, and
`a_{n+1} >= S_n + 2`, then `S_n + 1` is not a subset sum of `range a`.

6. Root theorem

Use `Filter.not_eventually` / `Filter.frequently_atTop`: given any threshold
`N`, `exists_large_gap` and `missed_value_of_large_gap` produce a witness
`M >= N` that is not a subset sum.

## Lean API used

Likely useful names under `import Mathlib`:

- `Int.floor_nonneg`
- `Int.floor_le`
- `Int.sub_one_lt_floor`
- `Int.floor_le_floor`
- `pow_le_pow_right₀`
- `geom_sum_eq`
- `tendsto_pow_atTop_atTop_of_one_lt`
- `Filter.not_eventually`
- `Filter.frequently_atTop`
- `Finset.single_le_sum`
- `Finset.sum_image_le_of_nonneg`
- `Finset.sum_le_sum_of_subset_of_nonneg`

The external `formal_proof` linked by the corpus follows this route, so the
risk is mostly transport/API alignment in the pinned Mathlib snapshot, not
mathematical uncertainty.
