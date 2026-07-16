# Erdős #647 — √-prefix failure audit (stats run, 2026-07-16)

Computational steering evidence, **not proof**. Produced mechanically from
the per-survivor telemetry of `search_sqrt_prefix_survivor.rs` (commit
`9885546`): 45-class wheel mod 46189, seven-form Miller–Rabin filter,
full incremental √-prefix check with Pollard-rho factorization of every
first failure.

**Run**: `t ∈ [21,650,000, 31,650,000)`, i.e. `N ∈ ~[1.000×10¹², 1.462×10¹²]`,
450,000,000 parameters tested. Raw log: `/f/tmp/sqrt_prefix_stats_run.log`
(719 `SURV` rows).

## Headline

**A five-rung gauntlet — shifts k ∈ {5, 7, 9, 10, 11} — killed every one
of the 719 seven-form survivors. None reached shift 13.** The shifts
13–16 that the leaf catalog normalized were never touched by the actual
frontier population at this height. The negative proof, if it exists at
accessible depth, lives in the unfiltered early ladder.

## First-failure histogram and per-rung kill rates

| rung k | budget | forced factor | cofactor demand | failures | reached | kill rate |
|---|---|---|---|---|---|---|
| 5  | 7  | 5·(504N−1)      | τ(504N−1) ≤ 3 | 616 | 719 | 86% |
| 7  | 9  | 7·(360N−1)      | τ(360N−1) ≤ 4 | 61  | 103 | 59% |
| 9  | 11 | 3²·(280N−1)     | τ(280N−1) ≤ 3 | 34  | 42  | 81% |
| 10 | 12 | 2·5·(252N−1)    | τ(252N−1) ≤ 3 | 7   | 8   | 88% |
| 11 | 13 | 2520N−11 direct | τ ≤ 13        | 1   | 1   | 100% |

The τ≤3 rungs (5, 9, 10) kill ~85% each; the τ≤4 rung (7) kills only
59% — semiprimes are admissible there, and the pass rates track the
expected near-prime densities of the sieved forms. The rung structure is
exactly the all-depth conditional window seen from the failure side.

## Excess distribution at k=5 (616 failures)

Mass concentrates at excess ∈ {1, 9, 25} ⇔ τ ∈ {8, 16, 32} ⇔ squarefree
failures with exactly 3, 4, 5 prime factors:

- excess 1 (τ=8, `504N−1 = p·q·r`): 205 — the dominant *marginal* mode;
- excess 9 (τ=16): 195; excess 25 (τ=32): 88; excess 5 (τ=12, a square
  factor): 53; long tail to excess 185.

## 5-adic spine depth at k=5

`n−5 = 5^a·…` with a = 1: 484, a = 2: 101, a = 3: 26, a = 4: 3, a = 5: 2 —
geometric ~1/5 per level, matching the formalized p-adic layer structure
(`Erdos647_AdicSpineTermination`).

## Residue classes

Roughly uniform across the 45 wheel classes (max 26, min 7 survivors per
class) — no class is privileged; the killing mechanism is
class-independent, consistent with it living in the unfiltered forms,
not the wheel.

## Recurring small primes in failure certificates

- k=5: beyond the forced 5 — 31 (38×), 23 (35×), 37 (26×), 29 (24×),
  41, 53, 43 each ~20×: the "stray small prime" channel.
- k=9: beyond the forced 3² — 31, 29, 73.
- k=10: beyond 2·5 — 23, 43, 83, 29.

## Record table

| N | depth | first fail | τ | factorization of n−k |
|---|---|---|---|---|
| 1,416,746,446,258 | 10 | 11 | 32 | 11·19·701·1433·17005217 |
| 1,013,029,527,510 | 9 | 10 | 16 | 2·5·43·5936824207733 |
| 1,046,405,092,018 | 9 | 10 | 24 | 2·5²·107·492886136801 |
| 1,086,524,841,116 | 9 | 10 | 64 | 2·5·83·1069·34483·89491 |
| 1,121,309,045,714 | 9 | 10 | 32 | 2·5·23·29·423642997781 |

## What this says for the negative lane

1. The operative certificate is the **near-primality demand on the next
   unfiltered ladder form** (τ ≤ 3 or ≤ 4 on `504N−1`, `360N−1`,
   `280N−1`, `252N−1`, then the direct form `2520N−11`), not a terminal
   affine leaf of the 13–16 catalog.
2. Survival through depth D is the conjunction of ~independent per-rung
   events with pass probability ~c/ln N each — the heuristic survivor
   count decays geometrically in the number of rungs, which is why 719
   survivors produced record depth only 10 in this range.
3. **The known caveat stands**: deep survivors exist (the kernel-verified
   depth-15 witness sits just above this range — and outside the wheel,
   as full-candidate filters do not bind finite-depth witnesses).
   Heuristic geometric decay is NOT a proof; proving even one rung must
   fail for all large N is prime-tuple-hard. The formally accessible
   next targets suggested by this data are the recursive escape
   structure (passing rung 5 at 5-adic depth a forces an explicit
   near-prime certificate that feeds rung 7's demand) and the
   B-parametric bookkeeping of how many τ≤3 demands fit below 2√n.

## Addendum: frontier-height run (completed 2026-07-16)

**Run**: `t ∈ [5,292,300,000, 5,392,300,000)`, i.e.
`N ∈ ~[2.4445×10¹⁴, 2.4907×10¹⁴]` (`n` beyond the published 6.16×10¹⁷
exclusion frontier), 4,500,000,000 parameters, 2696 seven-form
survivors, **zero candidates**. Raw log:
`sqrt-prefix-frontier-run-6e17.survlog.txt`.

| rung k | failures | reached | kill rate |
|---|---|---|---|
| 5  | 2343 | 2696 | 87% |
| 7  | 220  | 353  | 62% |
| 9  | 109  | 133  | 82% |
| 10 | 19   | 24   | 79% |
| 11 | 1    | 5    | 20% |
| 13 | 4    | 4    | 100% |

Height comparison: the kill rates match the N~10¹² run within noise
(87/62/82/79 vs 86/59/81/88) — **the gauntlet mechanism is
height-stable**. At this height the gauntlet extended one rung: four
survivors passed the full base block (and rung 12) and all died at
rung 13 (record certificate: `n−13 = 13·97·439·1118374637033`, τ=16>15,
at `N = 245,678,060,791,306`). Consistent with the growing-gauntlet
criterion: the base block is finite, the ladder extends with height,
and no fixed rung set suffices.
