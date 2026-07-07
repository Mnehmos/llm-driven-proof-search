# How the #1052 proof was found — reasoning narrative

A systems-level account of the actual workflow, including the dead ends.

## 1. Target selection

The bounty board's lane 1 (solved-with-`sorry` statements inside bounty
files) surfaced `even_of_isUnitaryPerfect` in `1052.lean`: marked
`research solved`, body `sorry`, only an external AlphaProof link. Number
theory, squarely in ArithmeticKit territory, bounded classical result
(Subbarao–Warren 1966). Chosen over #470's density variant (heavier
analysis).

## 2. Mathematical plan (before any Lean)

Unitary divisors of `n` = divisors `d` with `gcd(d, n/d) = 1`. Unitary
perfect: proper unitary divisors sum to `n`, i.e. σ*(n) = 2n. Classical
proof sketch that odd `n` is impossible:

- σ* is multiplicative over prime powers; each factor is `1 + p^a`.
- For odd `n`, every `1 + p^a` is even, so `2^{ω(n)} ∣ σ*(n) = 2n ≡ 2 (mod 4)`
  forces `ω(n) ≤ 1` — and prime powers fail directly.

Full multiplicativity of σ* is heavy to formalize. The plan deliberately
avoided it: peel off ONE prime (`σ*(n) = (1 + p^{ν_p(n)}) · σ*(m)` with
`m` the p-free part), and get the evenness of `σ*(m)` for odd `m > 1` not
from the product formula but from the **fixed-point-free involution
`d ↦ m/d`**, which pairs odd values — a sum of even pairs. Two even factors
⇒ `4 ∣ 2n`, contradiction. One prime peel + one involution instead of an
induction over factorizations.

## 3. Lean development (probe-first workflow)

1. **API verification before writing**: every uncertain Mathlib name was
   grepped in the pinned snapshot first (`Finset.sum_bij'` signature,
   `Finset.sum_involution` argument order, `Nat.factorization_div`,
   `ordProj`/`ordCompl` lemma family, `ZMod.natCast_eq_zero_iff_even`).
   This is the single biggest error-rate reducer.
2. **Local pre-validation**: the whole development was compiled locally
   (`lake env lean`) before spending any tracked attempt.
3. **Round-1 failures (all mechanical, none mathematical):**
   - guessed name `Nat.div_dvd_div_of_dvd_of_dvd` doesn't exist → replaced
     by explicit quotient identities + `dvd_mul_left`;
   - `rw [← hmul]` rewrote ALL occurrences of `n` including inside
     `p ^ n.factorization p`, corrupting the goal → `nth_rewrite 1` to
     target only the numerator;
   - a `¬¬` artifact from partitioning by the negated predicate → partition
     by the positive predicate;
   - ZMod-parity by `push_cast`/`ring_nf` was brittle → replaced by the
     clean `↑e + ↑(m/e) = ↑(e + m/e)` + `Even` route (`Odd.add_odd`).
4. **Round 2: clean compile** (~250 lines, Mathlib-only).
5. **Transport hardening**: module helpers are flattened in transit (an
   environment rule), and the proof uses indentation-sensitive `calc`/bullet
   structure — so it was restructured into one monolithic root proof
   (machinery as ∀-quantified `have`s) submitted as `raw_lean_block`, and
   pre-validated again locally. Kernel-verified **pass@1** in the tracked
   episode.

## 4. Cross-check against the linked reference

Only AFTER our solve, the AlphaProof-generated reference (mzhorvath1 fork)
was fetched: dense machine-generated tactic text. Attempted replay in our
toolchain fails — it depends on formal-conjectures' custom tactic
infrastructure (`valid` is their macro, absent from Mathlib) and an older
toolchain. Finding: **our artifact is the standalone-reproducible proof of
this statement**; the reference corroborates the claim's solved status but
is not portable.

## 5. What transfers to the open problem

The peel-off lemma (`sum_uDiv_factor`) and the p-free-part identification
(`filter_not_dvd_eq_uDiv_ordCompl`) are exactly the recursion step of full
σ*-multiplicativity — see `05-open-problem-attack-plan.md`.
