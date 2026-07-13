# Erdős #647 — living campaign folder

**Problem ([erdosproblems.com/647](https://www.erdosproblems.com/647), Erdős–Selfridge, OPEN):**
is there any `n > 24` with `max_{m<n}(m + τ(m)) ≤ n + 2`?

**This folder** documents an ongoing AI + Lean-kernel campaign on #647: an
independent, machine-checked rederivation of the known reduction, several
new kernel-verified artifacts — including what we believe is the **first
machine-checked proof of Hughes's Theorem 2** (every candidate lies in one
of two explicit prime constellations) — and an active push toward the real
frontier: a machine-checked Brun/Selberg-sieve density bound.

**The problem is open. These are living documents.** Every claim is backed
by a Lean 4 kernel verification record; nothing rests on trusting the AI or
the human.

## Start here

| file | what it is |
|---|---|
| [whitepaper.md](whitepaper.md) | the full story: problem, prior art, campaign log, the wall, the frontier |
| [attack-plan.md](attack-plan.md) | current plan of record (density-bound program, Layers A/B/C) |
| [evidence.md](evidence.md) | machine records: statements, problem/episode IDs, hashes, outcomes |
| [credit.md](credit.md) | attribution (Hughes, Kitamura, Idén, Bloom) + honest limits |
| [proof/](proof/) | byte-faithful `.lean` snapshots of the headline kernel-verified theorems |

## Headline results (as of 2026-07-13)

1. **Theorem 2 formalized** — Hughes's prime-chain reduction (paper-sketch
   only, absent from his Lean tree) proven in three kernel-verified stages:
   every candidate `n > 24` is `8s+8` with `s, 2s+1, 4s+3, 8s+7` all prime,
   or `16s+8` with `s, 4s+1, 8s+3, 16s+7` all prime.
   → [proof/Erdos647_Thm2_Stage12.lean](proof/Erdos647_Thm2_Stage12.lean),
   [Stage4](proof/Erdos647_Thm2_Stage4.lean), [Stage8](proof/Erdos647_Thm2_Stage8.lean)
2. **Independent frontier replication, tighter sieve** — the 41 open residue
   classes mod 46189 reproduced from scratch (48-survivor base sieve vs the
   published 96), with every sieve row *proven* from classification
   theorems, plus 4 residue closures re-proven fresh. ~110 kernel-verified
   theorems total.
3. **48 new sub-AP closures** — then deliberately frozen: the all-avoid
   obstruction (Hughes; extended here to Theorem-2 chain forms) proves this
   entire technique class can never close the frontier.
4. **First brick of quantitative Mertens in Lean** — an exact identity for
   `∑ 1/p` via Chebyshev θ and Abel summation
   ([proof/Erdos647_MertensIdentity.lean](proof/Erdos647_MertensIdentity.lean)),
   opening the path to the Hughes–Kitamura `x/(log x)⁷` density bound.
   Mathlib has the Selberg sieve core; the missing pieces are mapped in
   [attack-plan.md](attack-plan.md).

## Status, plainly

No new witness. No disproof. The problem stands. What changed: more of the
wall around it is now machine-checked, the dead ends are *proven* dead, and
the live frontier (density bounds) has a formal foothold. Contributions,
corrections, and races welcome — see the open invitations at the end of
[whitepaper.md](whitepaper.md).
